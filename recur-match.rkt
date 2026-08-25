#lang typed/racket
(provide r/match*)
(require syntax/parse/define racket/match
         (for-syntax racket/syntax
                     syntax/stx))

(begin-for-syntax
  ; searches every nonterminal's case-entries in `table` for one named
  ; `lead-sym`, since a `r/match*` clause only gives a lead-id, not which
  ; nonterminal it belongs to (mirrors construct.rkt's `find-case-entry`,
  ; but unscoped by nonterminal). Returns `(values case-entry nt-entry)` --
  ; the owning `nt-entry` is what lets a later leaf clause in the same
  ; `r/match*` find that same nonterminal's `leaf-type`s -- or `(values #f #f)`.
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

  ; a field pattern is `,x` (bind directly, no recursion) or `,[x]` (bind to
  ; the result of calling `on-id` on this field's value)
  (define (translate-field f on-id)
    (syntax-parse f
      [((~literal unquote) (x:id)) #`(app #,on-id x)]
      [((~literal unquote) x:id) #'x]
      [_ (raise-syntax-error 'r/match* "expected `,x` or `,[x]`" f)]))

  ; translates one clause's pattern (grammar-shape syntax) into a `match`
  ; pattern, using `table` (the `<lang>-meta` table) to resolve a headed
  ; pattern's struct name and field shapes. Returns
  ; `(values match-pattern nt-entry-or-#f)` -- `nt-entry` is present only for
  ; a headed pattern (it's how the language's leaf types get resolved later,
  ; see `r/match*` below); a leaf pattern doesn't carry enough information on
  ; its own to know which nonterminal it belongs to.
  (define (translate-pattern pat table on-id)
    (syntax-parse pat
      ; leaf: `,x` -- final translation (a `?`-predicate pattern narrowing to
      ; this nonterminal's leaf type) happens once the nonterminal is known,
      ; see `r/match*`; for now just record the bare name and defer
      [((~literal unquote) x:id) (values (cons 'leaf #'x) #f)]
      ; headed: `(lead field ...)`
      [(lead:id field ...)
       (define-values (ce nt-entry) (find-case-entry-anywhere table (syntax-e #'lead)))
       (unless ce
         (raise-syntax-error 'r/match* (format "no case ~a in this language" (syntax-e #'lead)) pat))
       (define-values (ctor-id field-shapes)
         (syntax-parse ce [(_ ctor:id (fs ...)) (values #'ctor (syntax->list #'(fs ...)))]))
       (define fields (syntax->list #'(field ...)))
       (unless (= (length fields) (length field-shapes))
         (raise-syntax-error 'r/match*
                             (format "~a expects ~a field(s), got ~a"
                                     (syntax-e #'lead) (length field-shapes) (length fields))
                             pat))
       (define sub-pats
         (for/list ([f (in-list fields)] [fs (in-list field-shapes)])
           (define tag (syntax-e (car (syntax->list fs))))
           (unless (eq? tag 'scalar)
             (raise-syntax-error 'r/match*
                                 "r/match* only supports scalar fields for now"
                                 f))
           (translate-field f on-id)))
       (values (cons 'headed #`(#,ctor-id #,@sub-pats)) nt-entry)]
      [_ (raise-syntax-error 'r/match* "expected `,x` or `(lead field ...)`" pat)])))

; (r/match* e #:lang lang-id #:on on-id [pat body ...+] ...)
; e.g. (r/match* e #:lang L0 #:on compile-expr
;        [,n (list (mov 'x0 n))]
;        [(Add ,[l] ,[r]) `(,@l ,(mov 'x1 'x0) ,@r ,(add 'x0 'x1))])
;
; Rewrites each clause's grammar-shape pattern into a real `match` pattern
; against `lang-id`'s `<lang>-meta` table (the same one `lang-construct`
; reads, see construct.rkt), then hands the whole thing to `match`. `,x`
; binds a field's value directly; `,[x]` binds it to `(on-id <value>)`
; instead -- this is the whole recursion mechanism, entirely explicit at
; each field, not automatic.
;
; A leaf clause's binding (`,n`) is cast to its declared terminal type (e.g.
; `Integer`), because a bare `match` variable pattern can't narrow a union
; type on its own -- Typed Racket has no way to know, just from one pattern
; failing to match a struct, that what's left must be a narrower type. This
; is a real (if small) runtime check, not just static resolution; see the
; conversation this was designed in for why that's an acceptable trade-off
; for a gradually-typed macro like this one.
;
; Scope: only scalar fields are supported in a headed pattern for now --
; `list`/`tuple-list` field patterns (matching/recursing over each element of
; a `,e ...` or `[,x ,e] ...` grammar field) are a natural follow-up, not
; done here. Clause order matters exactly like it does in plain `match`: a
; leaf clause matches unconditionally, so put more specific (headed) clauses
; before it.
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
   ; a leaf clause's pattern is just the bare bound name (no narrowing a
   ; `match` pattern can express on its own); the narrowing happens by
   ; shadowing it in the body with a cast to this nonterminal's leaf type
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
  (check-equal? (double 5) 10))
