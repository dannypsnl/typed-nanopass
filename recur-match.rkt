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

  (define (nt-entry-name nt-entry) (syntax-parse nt-entry [(name:id _ _) #'name]))
  (define (nt-entry-cases nt-entry) (syntax-parse nt-entry [(_ (ce ...) _) (syntax->list #'(ce ...))]))
  (define (nt-entry-leaf-types nt-entry)
    (syntax-parse nt-entry
      [(_ _ (t ...)) (syntax->list #'(t ...))]))

  (define (find-nt-entry-by-name table nt-sym)
    (for/or ([entry (in-list (syntax->list table))])
      (and (eq? (syntax-e (nt-entry-name entry)) nt-sym) entry)))

  (define (case-entry-lead ce) (syntax-parse ce [(lead:id _ _) (syntax-e #'lead)]))
  (define (case-entry-parts ce)
    (syntax-parse ce [(lead:id ctor:id (fs ...)) (values #'lead #'ctor (syntax->list #'(fs ...)))]))
  (define (find-case-entry-in nt-entry lead-sym)
    (for/or ([ce (in-list (nt-entry-cases nt-entry))]) (and (eq? (case-entry-lead ce) lead-sym) ce)))

  (define (field-shape-tag fs) (syntax-e (car (syntax->list fs))))
  (define (field-shape-rest fs) (cdr (syntax->list fs))) ; scalar/list: 1 type; tuple-list: N types

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

;; --- #:auto: synthesize default clauses for every case a clause list didn't
;; cover, across every nonterminal of #:lang (not just the one the written
;; clauses happen to touch). This is what makes cross-nonterminal recursion
;; free: `on-id` is a single self-recursive function over the union of every
;; nonterminal in #:lang, so a field that recurses into a sibling nonterminal
;; is just another call to the same `on-id` -- no per-nonterminal dispatch
;; table needed, `find-case-entry-anywhere` already searches every
;; nonterminal unscoped.
(begin-for-syntax
  ; every `lang:NT` full type name this language declares, as bare symbols --
  ; used to tell "recurse, this field is a nonterminal of #:lang" apart from
  ; "copy, this field is a terminal" by comparing a field-shape's type symbol
  (define (source-nt-syms lang-sym table)
    (for/list ([nt-entry (in-list (syntax->list table))])
      (string->symbol (format "~a:~a" lang-sym (syntax-e (nt-entry-name nt-entry))))))

  (define (nonterminal-type? type-id nt-syms) (and (memq (syntax-e type-id) nt-syms) #t))

  ; target must have the same nonterminal + case name; we don't otherwise
  ; check field arity/types here -- the generated constructor call below
  ; leans on Typed Racket's own struct-arity check for that, same trust
  ; construct.rkt already places in it
  (define (require-target-case! to-lang-id to-table lang-id nt-name-stx lead-sym)
    (define to-nt-entry (find-nt-entry-by-name to-table (syntax-e nt-name-stx)))
    (unless to-nt-entry
      (raise-syntax-error 'r/match*
        (format "#:auto: target language ~a has no nonterminal ~a (source ~a's ~a has case `~a`); write this case explicitly"
                (syntax-e to-lang-id) (syntax-e nt-name-stx) (syntax-e lang-id) (syntax-e nt-name-stx) lead-sym)
        to-lang-id))
    (define to-ce (find-case-entry-in to-nt-entry lead-sym))
    (unless to-ce
      (raise-syntax-error 'r/match*
        (format "#:auto: target language ~a's ~a has no case `~a`; write this case explicitly"
                (syntax-e to-lang-id) (syntax-e nt-name-stx) lead-sym)
        to-lang-id))
    to-ce)

  (define (require-target-leaf! to-lang-id to-table lang-id nt-name-stx)
    (define to-nt-entry (find-nt-entry-by-name to-table (syntax-e nt-name-stx)))
    (unless to-nt-entry
      (raise-syntax-error 'r/match*
        (format "#:auto: target language ~a has no nonterminal ~a (source ~a's ~a has a leaf case); write this case explicitly"
                (syntax-e to-lang-id) (syntax-e nt-name-stx) (syntax-e lang-id) (syntax-e nt-name-stx))
        to-lang-id))
    (define to-leaf-types (nt-entry-leaf-types to-nt-entry))
    (when (null? to-leaf-types)
      (raise-syntax-error 'r/match*
        (format "#:auto: target language ~a's ~a has no leaf case; write this case explicitly"
                (syntax-e to-lang-id) (syntax-e nt-name-stx))
        to-lang-id))
    to-leaf-types)

  ; `lang:NT` -> `to-lang:NT`: `on-id`'s return type is the union of every
  ; nonterminal it handles, so a recursive call's result needs narrowing to
  ; the one nonterminal this particular field is actually known (statically,
  ; from the field-shape) to produce -- same class of gap the module
  ; docstring already documents for `,[x] ...`'s ellipsis case, just also
  ; showing up here now that #:auto's `on-id` can span more than one
  ; nonterminal.
  (define (target-type-for type-id lang-sym to-lang-id)
    (define prefix (format "~a:" lang-sym))
    (define nt-name (substring (symbol->string (syntax-e type-id)) (string-length prefix)))
    (format-id to-lang-id "~a:~a" (syntax-e to-lang-id) nt-name))

  ; a scalar field is either recursed (nonterminal, cast to the specific
  ; target nonterminal) or copied as-is (terminal)
  (define (default-scalar-arg v type-id nt-syms lang-sym to-lang-id on-id)
    (if (nonterminal-type? type-id nt-syms)
        #`(cast (#,on-id #,v) #,(target-type-for type-id lang-sym to-lang-id))
        v))

  ; a list field maps the same choice over every element
  (define (default-list-arg v type-id nt-syms lang-sym to-lang-id on-id)
    (if (nonterminal-type? type-id nt-syms)
        #`(cast (map #,on-id #,v) (Listof #,(target-type-for type-id lang-sym to-lang-id)))
        v))

  ; a tuple-list field maps per-component: each tuple's Kth slot is recursed
  ; or copied depending on that slot's own declared type
  (define (default-tuple-list-arg v type-ids nt-syms lang-sym to-lang-id on-id)
    (define comps (for/list ([_ (in-list type-ids)]) (generate-temporary 'c)))
    (define rebuilt
      (for/list ([c (in-list comps)] [ty (in-list type-ids)])
        (if (nonterminal-type? ty nt-syms)
            #`(cast (#,on-id #,c) #,(target-type-for ty lang-sym to-lang-id))
            c)))
    #`(for/list ([one (in-list #,v)])
        (match one [(list #,@comps) (list #,@rebuilt)])))

  ; builds one `[(SrcCtor f ...) (TargetCtor arg ...)]` clause for a source
  ; case-entry the written clauses didn't cover
  (define (default-headed-clause lang-id to-lang-id to-table nt-name-stx ce nt-syms on-id)
    (define lang-sym (syntax-e lang-id))
    (define-values (lead src-ctor field-shapes) (case-entry-parts ce))
    (define to-ce (require-target-case! to-lang-id to-table lang-id nt-name-stx (syntax-e lead)))
    (define-values (_ to-ctor __) (case-entry-parts to-ce))
    (define field-vars (for/list ([_ (in-list field-shapes)]) (generate-temporary 'f)))
    (define args
      (for/list ([fs (in-list field-shapes)] [v (in-list field-vars)])
        (define rest (field-shape-rest fs))
        (case (field-shape-tag fs)
          [(scalar) (default-scalar-arg v (car rest) nt-syms lang-sym to-lang-id on-id)]
          [(list) (default-list-arg v (car rest) nt-syms lang-sym to-lang-id on-id)]
          [(tuple-list) (default-tuple-list-arg v rest nt-syms lang-sym to-lang-id on-id)])))
    #`[(#,src-ctor #,@field-vars) (#,to-ctor #,@args)])

  ; identity default for a nonterminal's bare `,n` leaf alternative
  (define (default-leaf-clause lang-id to-lang-id to-table nt-name-stx)
    (define to-leaf-types (require-target-leaf! to-lang-id to-table lang-id nt-name-stx))
    (define leaf-type (if (= 1 (length to-leaf-types)) (car to-leaf-types) #`(U #,@to-leaf-types)))
    (define v (generate-temporary 'leaf))
    #`[#,v (let ([#,v (cast #,v #,leaf-type)]) #,v)])

  ; #:auto must not correspond #:lang's and #:to's cases by name coincidence
  ; -- two independently-authored languages that happen to share a case name
  ; and arity aren't necessarily the same thing. #:to has to (transitively)
  ; `extends` #:lang (define-language.rkt), which is what actually
  ; guarantees an unremoved case is the literal same struct in both
  ; languages, not a lookalike.
  (define (find-extends-parent lang-id)
    (define extends-id (format-id lang-id "~a-extends" lang-id))
    ; a base language stores `(quote-syntax #f)` -- syntax-local-value
    ; returns that as a syntax object WRAPPING #f, not #f itself, so a bare
    ; truthiness check would treat "no parent" as a parent to recurse into
    (define v (syntax-local-value extends-id (lambda () #f)))
    (and (syntax? v) (syntax-e v) v))

  (define (extends-chain-includes? to-lang-id target-sym)
    (let loop ([cur to-lang-id] [seen '()])
      (cond
        [(eq? (syntax-e cur) target-sym) #t]
        [(memq (syntax-e cur) seen) #f] ; cycle guard
        [else
         (define parent (find-extends-parent cur))
         (and parent (loop parent (cons (syntax-e cur) seen)))]))))

; (r/match* e #:lang lang-id [#:to to-lang-id] #:on on-id [#:auto] [pat body ...+] ...)
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
; #:auto turns on default-case generation: after the written clauses, every
; case (across every nonterminal #:lang declares, not just the one the
; written clauses touch) that wasn't explicitly matched gets a synthesized
; clause that recurses into nonterminal-typed fields via `on-id` and copies
; terminal-typed fields as-is, reconstructing in `#:to` (defaults to
; `#:lang` itself). Since `on-id` is a single function over the union of
; every nonterminal, a default case whose field belongs to a sibling
; nonterminal is just another call to that same `on-id` -- mutual recursion
; between nonterminals falls out of ordinary self-recursion over a sum type,
; no separate per-nonterminal dispatch needed. `#:to` must (transitively)
; `extends` `#:lang` (define-language.rkt) -- #:auto refuses to correspond
; two independently-authored languages just because a case name and arity
; happen to match, since that's a coincidence, not a guarantee. If `#:to`'s
; `extends` deliberately dropped a case (like `Sub` below), that's a
; compile-time error: write that case explicitly instead.
;
;   (define-language Core (extends Surface) (Expr (- Sub)))
;   (r/match* e #:lang Surface #:to Core #:on desugar-sub #:auto
;     [(Sub ,[l] ,[r]) (lang-construct Core Expr `(Add ,l (Mul ,r ,-1)))])
;
; Two real Typed Racket gaps this works around or lives with:
; - a leaf clause's `,n` is cast to its declared terminal type, since a bare
;   match variable can't narrow a union type on its own.
; - `(app f x) ...` never propagates `f`'s return type through the ellipsis
;   (`x` : `(Listof Any)` always) -- cast explicitly where it matters, e.g.
;   before `apply` (see the test module).
;
; Clause order matters like in plain `match`: a leaf clause matches
; unconditionally, so put headed clauses first; #:auto's own leaf default
; (if any) is always placed last for the same reason.
(define-syntax-parser r/match*
  [(_ e:expr #:lang lang-id:id
      (~optional (~seq #:to to-lang-id:id) #:defaults ([to-lang-id #'lang-id]))
      #:on on-id:id
      (~optional (~and auto-kw #:auto))
      [pat body ...+] ...)
   (define auto? (and (attribute auto-kw) #t))
   (define meta-id (format-id #'lang-id "~a-meta" #'lang-id))
   (define table (syntax-local-value meta-id (lambda () #f)))
   (unless table
     (raise-syntax-error 'r/match* (format "no such language: ~a" (syntax-e #'lang-id)) #'lang-id))
   (define to-meta-id (format-id #'to-lang-id "~a-meta" #'to-lang-id))
   (define to-table (and auto? (syntax-local-value to-meta-id (lambda () #f))))
   (when (and auto? (not to-table))
     (raise-syntax-error 'r/match* (format "no such language: ~a" (syntax-e #'to-lang-id)) #'to-lang-id))
   (when (and auto?
              (not (eq? (syntax-e #'to-lang-id) (syntax-e #'lang-id)))
              (not (extends-chain-includes? #'to-lang-id (syntax-e #'lang-id))))
     (raise-syntax-error 'r/match*
       (format "#:auto requires #:to language ~a to (transitively) extend #:lang language ~a; declare it via (define-language ~a (extends ~a) ...)"
               (syntax-e #'to-lang-id) (syntax-e #'lang-id) (syntax-e #'to-lang-id) (syntax-e #'lang-id))
       #'to-lang-id))
   (define pats (syntax->list #'(pat ...)))
   (define bodies (attribute body)) ; per clause, a list of body-expr stx
   (define-values (kinds nt-entries)
     (for/lists (ks ns) ([p (in-list pats)])
       (translate-pattern p table #'on-id)))
   (define headed-nt-entry (for/or ([n (in-list nt-entries)]) n))
   (unless (or headed-nt-entry auto?)
     (raise-syntax-error 'r/match*
                         "r/match* needs at least one headed clause (or #:auto) to know which nonterminal's leaf type(s) to use"
                         this-syntax))
   ; leaf pattern is just the bare name; narrowing happens by shadowing it
   ; in the body with a cast
   (define explicit-clauses
     (for/list ([k (in-list kinds)] [bs (in-list bodies)])
       (if (eq? (car k) 'leaf)
           (let ([x (cdr k)])
             (unless headed-nt-entry
               (raise-syntax-error 'r/match*
                                   "a leaf clause needs at least one headed clause in the same call to know its nonterminal"
                                   this-syntax))
             (define leaf-types (nt-entry-leaf-types headed-nt-entry))
             (define leaf-type (if (= 1 (length leaf-types)) (car leaf-types) #`(U #,@leaf-types)))
             #`[#,x (let ([#,x (cast #,x #,leaf-type)]) #,@bs)])
           (let ([p (cdr k)])
             #`[#,p #,@bs]))))
   ; (nt-sym . lead-sym) for every explicit headed clause -- what #:auto must not re-generate
   (define covered-leads
     (for/list ([p (in-list pats)] [k (in-list kinds)] [n (in-list nt-entries)]
                #:when (eq? (car k) 'headed))
       (cons (syntax-e (nt-entry-name n)) (syntax-parse p [(lead:id _ ...) (syntax-e #'lead)]))))
   ; the nonterminal an explicit leaf clause covers -- at most one leaf
   ; clause is meaningful anyway (a bare pattern always matches first)
   (define covered-leaf-nt
     (and headed-nt-entry (ormap (lambda (k) (eq? (car k) 'leaf)) kinds)
          (syntax-e (nt-entry-name headed-nt-entry))))
   (define nt-syms (and auto? (source-nt-syms (syntax-e #'lang-id) table)))
   (define-values (auto-headed-clauses auto-leaf-clauses)
     (if auto?
         (for/fold ([headed '()] [leaves '()] #:result (values (reverse headed) (reverse leaves)))
                   ([nt-entry (in-list (syntax->list table))])
           (define nt-sym (syntax-e (nt-entry-name nt-entry)))
           (define covered-here (for/list ([c (in-list covered-leads)] #:when (eq? (car c) nt-sym)) (cdr c)))
           (define new-headed
             (for/list ([ce (in-list (nt-entry-cases nt-entry))]
                        #:unless (memq (case-entry-lead ce) covered-here))
               (default-headed-clause #'lang-id #'to-lang-id to-table (nt-entry-name nt-entry) ce nt-syms #'on-id)))
           (define has-leaf? (not (null? (nt-entry-leaf-types nt-entry))))
           (define new-leaves
             (if (and has-leaf? (not (eq? nt-sym covered-leaf-nt)))
                 (list (default-leaf-clause #'lang-id #'to-lang-id to-table (nt-entry-name nt-entry)))
                 '()))
           (values (append (reverse new-headed) headed) (append (reverse new-leaves) leaves)))
         (values '() '())))
   #`(match e #,@explicit-clauses #,@auto-headed-clauses #,@auto-leaf-clauses)])

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
