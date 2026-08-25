#lang typed/racket
(provide r/match*)
(require syntax/parse/define racket/match
         (for-syntax racket/syntax
                     syntax/stx))

(begin-for-syntax
  ; a clause only names a lead-id, not a nonterminal, so search all of them
  ; (mirrors construct.rkt's find-case-entry, unscoped by nonterminal)
  (define (find-case-entry-anywhere table lead-sym)
    (define found-pair
      (or (for/or ([nt-entry (in-list (syntax->list table))])
            (syntax-parse nt-entry
              [(_ (ce ...) _)
               (define found
                 (for/or ([one (in-list (syntax->list #'(ce ...)))])
                   (syntax-parse one
                     [(lead:id _ _) (and (eq? (syntax-e #'lead) lead-sym) one)])))
               (and found (list found nt-entry))]))
          (list #f #f)))
    (values (car found-pair) (cadr found-pair)))

  (define (nt-entry-leaf-types nt-entry)
    (syntax-parse nt-entry
      [(_ _ (t ...)) (syntax->list #'(t ...))]))

  ; `,x` binds directly; `,[x]` binds to (on-id x)
  (define (translate-field f on-id)
    (syntax-parse f
      [((~literal unquote) (x:id)) #`(app #,on-id x)]
      [((~literal unquote) x:id) #'x]
      [_ (raise-syntax-error 'r/match* "expected `,x` or `,[x]`" f)]))

  (define (dots? p) (and (identifier? p) (eq? (syntax-e p) '...)))

  ; mirrors construct.rkt's consume-fields, building match sub-patterns
  ; instead of argument expressions
  (define (consume-field-patterns table on-id field-shapes pieces case-stx)
    (cond
      [(null? field-shapes)
       (unless (null? pieces)
         (raise-syntax-error 'r/match* "too many pieces" case-stx))
       '()]
      [else
       (define fs (car field-shapes))
       (define rest-shapes (cdr field-shapes))
       (define tag (syntax-e (car (syntax->list fs))))
       (define (whole-value-pat)
         (when (null? pieces)
           (raise-syntax-error 'r/match* "missing `,x`/`,[x]`" case-stx))
         (define pat (translate-field (car pieces) on-id))
         (cons pat (consume-field-patterns table on-id rest-shapes (cdr pieces) case-stx)))
       (case tag
         [(scalar)
          (when (null? pieces)
            (raise-syntax-error 'r/match* "missing `,x` or `,[x]`" case-stx))
          (define pat (translate-field (car pieces) on-id))
          (cons pat (consume-field-patterns table on-id rest-shapes (cdr pieces) case-stx))]
         [(list)
          (if (and (pair? pieces) (pair? (cdr pieces)) (dots? (cadr pieces)))
              (let ([elem-pat (translate-field (car pieces) on-id)]
                    [dots-stx (cadr pieces)])
                (cons #`(list #,elem-pat #,dots-stx)
                      (consume-field-patterns table on-id rest-shapes (cddr pieces) case-stx)))
              (whole-value-pat))]
         [(tuple-list)
          (when (null? pieces)
            (raise-syntax-error 'r/match* "missing value for tuple-list field" case-stx))
          (syntax-parse (car pieces)
            [((sub-piece ...) dots)
             #:when (dots? #'dots)
             (define elem-pats
               (for/list ([sp (in-list (syntax->list #'(sub-piece ...)))])
                 (translate-field sp on-id)))
             (cons #`(list (list #,@elem-pats) #,#'dots)
                   (consume-field-patterns table on-id rest-shapes (cdr pieces) case-stx))]
            [_ (whole-value-pat)])])]))

  ; returns (values match-pattern nt-entry-or-#f); nt-entry is #f for a leaf
  ; pattern, which doesn't carry enough info to know its own nonterminal
  (define (translate-pattern pat table on-id)
    (syntax-parse pat
      ; leaf's `?`-cast is added later in r/match*, once the nonterminal is known
      [((~literal unquote) x:id) (values (cons 'leaf #'x) #f)]
      [(lead:id field ...)
       (define-values (ce nt-entry) (find-case-entry-anywhere table (syntax-e #'lead)))
       (unless ce
         (raise-syntax-error 'r/match* (format "no case ~a in this language" (syntax-e #'lead)) pat))
       (define-values (ctor-id field-shapes)
         (syntax-parse ce [(_ ctor:id (fs ...)) (values #'ctor (syntax->list #'(fs ...)))]))
       (define fields (syntax->list #'(field ...)))
       (define sub-pats (consume-field-patterns table on-id field-shapes fields pat))
       (values (cons 'headed #`(#,ctor-id #,@sub-pats)) nt-entry)]
      [_ (raise-syntax-error 'r/match* "expected `,x` or `(lead field ...)`" pat)])))

; (r/match* e #:lang lang-id #:on on-id [pat body ...+] ...)
; e.g. (r/match* e #:lang L0 #:on compile-expr
;        [,n (list (mov 'x0 n))]
;        [(Add ,[l] ,[r]) `(,@l ,(mov 'x1 'x0) ,@r ,(add 'x0 'x1))])
;
; Rewrites each clause's grammar-shape pattern into a `match` pattern against
; `lang-id`'s `<lang>-meta` table (construct.rkt reads the same one). `,x`
; binds a field directly; `,[x]` binds it to `(on-id x)` -- recursion is
; explicit per field, not automatic. `,e ...`/`,[e] ...` and
; `([,x ,e] ...)`/`([,x ,[e]] ...)` do the same for list/tuple-list fields,
; via real `match` ellipsis; a bare `,xs` binds the whole field, no
; per-element access.
;
; Two real Typed Racket gaps this works around or lives with:
; - a leaf clause's `,n` is cast to its declared terminal type, since a bare
;   match variable can't narrow a union type on its own.
; - `(app f x) ...` never propagates `f`'s return type through the ellipsis
;   (`x` : `(Listof Any)` always) -- cast explicitly where it matters, e.g.
;   before `apply` (see the test module).
;
; Clause order matters like in plain `match`: a leaf clause matches
; unconditionally, so put headed clauses first.
(define-syntax-parser r/match*
  [(_ e:expr #:lang lang-id:id #:on on-id:id [pat body ...+] ...)
   (define meta-id (format-id #'lang-id "~a-meta" #'lang-id))
   (define table (syntax-local-value meta-id (lambda () #f)))
   (unless table
     (raise-syntax-error 'r/match* (format "no such language: ~a" (syntax-e #'lang-id)) #'lang-id))
   (define pats (syntax->list #'(pat ...)))
   (define bodies (attribute body)) ; per clause, a list of body-expr stx
   (define-values (kinds nt-entries)
     (for/lists (ks ns) ([p (in-list pats)])
       (translate-pattern p table #'on-id)))
   (define headed-nt-entry (for/or ([n (in-list nt-entries)]) n))
   (unless headed-nt-entry
     (raise-syntax-error 'r/match*
                         "r/match* needs at least one headed clause to know which nonterminal's leaf type(s) to use"
                         this-syntax))
   (define leaf-types (nt-entry-leaf-types headed-nt-entry))
   (define leaf-type
     (if (= 1 (length leaf-types))
         (car leaf-types)
         #`(U #,@leaf-types)))
   ; leaf pattern is just the bare name; narrowing happens by shadowing it
   ; in the body with a cast
   (define clauses
     (for/list ([k (in-list kinds)] [bs (in-list bodies)])
       (if (eq? (car k) 'leaf)
           (let ([x (cdr k)])
             #`[#,x (let ([#,x (cast #,x #,leaf-type)]) #,@bs)])
           (let ([p (cdr k)])
             #`[#,p #,@bs]))))
   #`(match e #,@clauses)])

(module+ test
  (require typed/rackunit (file "define-language.rkt"))

  (define-language L0
    (terminals (Integer (n)))
    (Expr (e)
          ,n
          (Add ,e ,e)))

  (: double : L0:Expr -> Integer)
  (define (double e)
    (r/match* e
              #:lang L0
              #:on double
              [(Add ,[l] ,[r]) (+ l r)]
              [,n (* 2 n)]))

  (check-equal? (double (L0:Expr:Add 3 4)) 14)
  (check-equal? (double 5) 10)

  (define-language L1
    (terminals (Integer (n)) (Symbol (x)))
    (Expr (e)
          ,n
          (Var ,x)
          (Add ,e ,e)
          (Block ,e ...)
          (Let ([,x ,e] ...) ,e)))

  (: count-nodes : L1:Expr -> Integer)
  (define (count-nodes e)
    (r/match* e
      #:lang L1
      #:on count-nodes
      [(Add ,[l] ,[r]) (+ 1 l r)]
      [(Block ,[es] ...) (+ 1 (apply + (cast es (Listof Integer))))]
      [(Let ([,xs ,[es]] ...) ,[body]) (+ 1 (apply + (cast es (Listof Integer))) body)]
      [(Var ,x) 1]
      [,n 1]))

  ; `,es`/`,bindings` with no brackets: bind the whole field, no recursion
  (: block-size : L1:Expr -> Integer)
  (define (block-size e)
    (r/match* e
      #:lang L1
      #:on block-size
      [(Block ,es) (length es)]
      [(Add ,l ,r) 0]
      [(Let ,bindings ,body) (length bindings)]
      [(Var ,x) 0]
      [,n 0]))

  (check-equal? (count-nodes (L1:Expr:Block (list 1 2 3))) 4)
  (check-equal? (count-nodes (L1:Expr:Let (list (list 'x 1) (list 'y 2)) 3)) 4)
  (check-equal? (block-size (L1:Expr:Block (list 1 2 3))) 3)
  (check-equal? (block-size (L1:Expr:Let (list (list 'x 1) (list 'y 2)) 3)) 2))
