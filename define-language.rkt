#lang typed/racket
(provide define-language)
(require syntax/parse/define racket/match
         (for-syntax ee-lib
                     fancy-app
                     racket/syntax
                     syntax/stx))

(define-for-syntax (prefix-id prefix id)
  (format-id id #:source id #:props id "~a:~a" prefix id))

; rule-case is a splicing syntax class (a repetition may consume >1 raw
; form, e.g. `,e ...`), so re-templating its bare pattern variable wraps
; each repetition in an extra list layer; this flattens that back out.
(define-for-syntax (flatten-rule-cases case*)
  #`(#,@(apply append (map syntax->list case*))))

(begin-for-syntax
  (define-syntax-class ty-meta
    ; TODO: how to check this is a valid type in typed/racket?
    (pattern (type (meta:id ...+))))

  (define-syntax-class rule
    (pattern (name:id (meta:id ...+)
                      #| TODO:
                      Currently, we have only simple rule-case
                      there should have a syntax

                        rule-case => rule-pretty-form

                      for example,

                        (bind ,x ,ty) => (,x : ,ty)

                      The bind structure will be printed as the right-hand side pretty form
                      |#
                      case*:rule-case ...+)))
  (define-splicing-syntax-class rule-case
    ; must come before the plain leaf pattern, so `,x ...` is one list-field
    ; case instead of a leaf case followed by a dangling `...`
    (pattern (~seq ((~literal unquote) meta:id) (~datum ...))
      #:attr intro-ty #f
      #:attr as-field #`[#,(generate-temporary #'meta) : (Listof #,(lookup #'meta))]
      ; shape: field kind for lang-construct (construct.rkt), reusing as-field's lookup
      #:attr shape #`(list #,(lookup #'meta))
      #:attr shapes #f)
    ; `([,x ,e] ...)`, e.g. `(let ([,x ,e] ...) ,e)`
    (pattern ((((~literal unquote) m*:id) ...+) (~datum ...))
      #:attr intro-ty #f
      #:attr as-field #`[#,(generate-temporary 'tuple*)
                         : (Listof (List #,@(stx-map lookup #'(m* ...))))]
      #:attr shape #`(tuple-list #,@(stx-map lookup #'(m* ...)))
      #:attr shapes #f)
    ; `,x`
    (pattern ((~literal unquote) meta:id)
      #:attr intro-ty #f
      #:attr as-field #`[#,(generate-temporary #'meta) : #,(lookup #'meta)]
      #:attr shape #`(scalar #,(lookup #'meta))
      #:attr shapes #f)
    ; `(+ ,e ,e)` -- `+` becomes a struct with fields `([e1 : T] [e2 : T])`
    ;
    ; a headed rule-case's own children must be leaf/list/tuple-list
    ; pieces, not another headed form (`as-field` below assumes exactly
    ; that shape) -- without this guard a grammar like `(Neg (Add ,e ,e))`
    ; doesn't fail cleanly, it crashes deep inside syntax-parse pointing at
    ; a line in this file instead of the offending rule. Nesting terms is
    ; still fine everywhere else (e.g. `(lang-construct L Expr `(Neg (Add
    ; ,l ,r)))`); it's only unsupported as a *grammar case's own field*.
    (pattern (lead:id c*:rule-case ...+)
      #:fail-when (ormap values (attribute c*.intro-ty))
                  "nested headed form as a field of another case isn't supported yet -- give it its own top-level case and reference it through a meta-variable instead"
      #:attr intro-ty #'lead
      #:attr as-field (syntax-property #'(c*.as-field ...) 'field #t)
      #:attr shape #f
      #:attr shapes #'(c*.shape ...))
    ; TODO: syntax without leading id, e.g. `(,fn ,arg)` instead of `(app ,fn ,arg)`
    ))

(begin-for-syntax
  (define (meta-variable/bind stx)
    (syntax-parse stx
      [(type (meta:id ...))
       (for-each (bind! _ #'#'type)
                 (syntax->list #'(meta ...)))]))

  (define (rule-case/meta-type stx name)
    (syntax-parse stx
      ; lookup a meta-variable associated type
      [((~literal unquote) meta:id) (lookup #'meta)]
      ; build the struct name
      [(lead:id c* ...) (prefix-id name #'lead)]))

  (define (rule/bind stx name)
    (syntax-parse stx [(meta:id ...) (stx-map (bind! _ #`#'#,name) #'(meta ...))]))
  ; returns (cons definitions nt-entry): definitions are struct/type forms
  ; for this rule; nt-entry is this rule's slice of the <lang>-meta table
  ; lang-construct/r/match* read back --
  ; (orig-name ((lead ctor-id (field-shape ...)) ...) (leaf-type ...))
  ; leaf-type is the type of each top-level bare `,x` alternative (e.g. `,n`
  ; in `(Expr (e) ,n (Add ,e ,e))`) -- no struct/case-entry, but r/match*
  ; needs it to narrow a leaf clause's binding, which a bare match variable can't.
  (define (rule/expand scoped-stx stx name orig-name)
    (syntax-parse scoped-stx
      [(scoped-c*:rule-case ...)
       (with-syntax
         ([(ty ...) (stx-map (rule-case/meta-type _ name) (flatten-rule-cases (attribute scoped-c*)))]
          [((case-struct ...) (case-entry ...) (leaf-type ...))
           (syntax-parse stx
             [(c*:rule-case ...)
              (list
                (for/list ([struct-name (attribute c*.intro-ty)]
                           [fields (syntax->list #'(scoped-c*.as-field ...))]
                           #:when struct-name)
                  #`(struct #,(prefix-id name struct-name) #,fields #:transparent))
                ; shapes/shape must come from scoped-c*, not c* -- they call
                ; lookup internally, which only resolves scoped identifiers
                (for/list ([struct-name (attribute c*.intro-ty)]
                           [shapes (attribute scoped-c*.shapes)]
                           #:when struct-name)
                  #`(#,struct-name #,(prefix-id name struct-name) (#,@shapes)))
                (for/list ([struct-name (attribute c*.intro-ty)]
                           [shape (attribute scoped-c*.shape)]
                           #:when (not struct-name)
                           #:when shape
                           #:when (syntax-parse shape
                                    [(tag:id _) (eq? (syntax-e #'tag) 'scalar)]
                                    [_ #f]))
                  (syntax-parse shape [(_ t) #'t])))])])
         (cons #`((define-type #,name (U ty ...)) case-struct ...)
               #`(#,orig-name (case-entry ...) (leaf-type ...))))])))

(begin-for-syntax
  (define (ext-nt-entry-name entry) (syntax-parse entry [(name:id _ _) #'name]))
  (define (ext-nt-entry-cases entry) (syntax-parse entry [(_ (ce ...) _) (syntax->list #'(ce ...))]))
  (define (ext-nt-entry-leaf-types entry) (syntax-parse entry [(_ _ (lt ...)) (syntax->list #'(lt ...))]))
  (define (ext-case-entry-lead ce) (syntax-parse ce [(lead:id _ _) (syntax-e #'lead)]))
  (define (ext-case-entry-ctor ce) (syntax-parse ce [(_ ctor:id _) #'ctor]))

  (define-syntax-class extend-delta
    (pattern (nt-name:id ((~datum -) rm:id ...))
      #:attr removed (syntax->list #'(rm ...)))))

; unparser
(begin-for-syntax
  (define (sx-case-entry-parts ce)
    (syntax-parse ce [(lead:id ctor:id (fs ...)) (values #'lead #'ctor (syntax->list #'(fs ...)))]))
  (define (sx-field-shape-tag fs) (syntax-e (car (syntax->list fs))))
  (define (sx-field-shape-rest fs) (cdr (syntax->list fs))) ; scalar/list: 1 type; tuple-list: N types

  ; every `lang:NT` full type name this language declares, as bare symbols --
  ; distinguishes "this field recurses" from "this field is a terminal, copy
  ; it as-is" (mirrors recur-match.rkt's #:auto machinery)
  (define (sx-source-nt-syms lang-sym table)
    (for/list ([nt-entry (in-list (syntax->list table))])
      (string->symbol (format "~a:~a" lang-sym (syntax-e (ext-nt-entry-name nt-entry))))))

  (define (sx-nonterminal-type? type-id nt-syms) (and (memq (syntax-e type-id) nt-syms) #t))

  ; a field's contribution to the printed form, meant to be spliced together
  ; with `append`: scalar/tuple-list contribute a single-element list (their
  ; one converted value/sub-list), list contributes its whole converted list
  ; directly -- so `,i ...`'s elements land as siblings of the lead symbol,
  ; same shape the grammar rule itself was written in.
  (define (sx-scalar-part v ty nt-syms self-id)
    (if (sx-nonterminal-type? ty nt-syms) #`(list (#,self-id #,v)) #`(list #,v)))
  (define (sx-list-part v ty nt-syms self-id)
    (if (sx-nonterminal-type? ty nt-syms) #`(map #,self-id #,v) v))
  ; `for/list`'s element binding needs an explicit type annotation here: when
  ; `v`'s own type comes from narrowing an outer `Any` via a struct match
  ; pattern (as it does in sx-build-case-clause below), Typed Racket's
  ; inference loses track of `one`'s type through the nested `match`, and
  ; mis-signals the whole `for/list` as producing zero-or-multiple values
  ; instead of one.
  (define (sx-tuple-list-part v tys nt-syms self-id)
    (define comps (for/list ([_ (in-list tys)]) (generate-temporary 'c)))
    (define converted
      (for/list ([c (in-list comps)] [ty (in-list tys)])
        (if (sx-nonterminal-type? ty nt-syms) #`(#,self-id #,c) c)))
    #`(list (for/list : (Listof Any) ([one : (List #,@tys) (in-list #,v)])
              (match one [(list #,@comps) (list #,@converted)]))))

  ; one `[(Ctor f ...) (append (list 'lead) part ...)]` match clause
  (define (sx-build-case-clause ce nt-syms self-id)
    (define-values (lead ctor field-shapes) (sx-case-entry-parts ce))
    (define field-vars (for/list ([_ (in-list field-shapes)]) (generate-temporary 'f)))
    (define parts
      (for/list ([fs (in-list field-shapes)] [v (in-list field-vars)])
        (define rest (sx-field-shape-rest fs))
        (case (sx-field-shape-tag fs)
          [(scalar) (sx-scalar-part v (car rest) nt-syms self-id)]
          [(list) (sx-list-part v (car rest) nt-syms self-id)]
          [(tuple-list) (sx-tuple-list-part v rest nt-syms self-id)])))
    #`[(#,ctor #,@field-vars) (append (list (quote #,lead)) #,@parts)])

  ; (build-lang->sexp-def name-id table lang-sym) -> syntax
  ;
  ; `name-id : Any -> Any`, matching every case of every nonterminal `table`
  ; (a language's `<lang>-meta` table) declares, and reconstructing the plain
  ; s-expression that would rebuild it via `lang-construct` -- `(lead field
  ; ...)`, recursing into nonterminal-typed fields via `name-id` itself and
  ; copying terminal-typed fields as-is. A case's own lead name is always
  ; what gets printed; there's no per-case custom pretty name/abbreviation
  ; (write that by hand, e.g. via a plain `r/match*` pass, when one's
  ; wanted).
  (define (build-lang->sexp-def name-id table lang-sym)
    (define nt-syms (sx-source-nt-syms lang-sym table))
    (define clauses
      (for*/list ([nt-entry (in-list (syntax->list table))]
                  [ce (in-list (ext-nt-entry-cases nt-entry))])
        (sx-build-case-clause ce nt-syms name-id)))
    #`(begin
        (: #,name-id : Any -> Any)
        (define (#,name-id x)
          (match x
            #,@clauses
            [_ x])))))

(define-syntax-parser define-language
  [(_ lang:id
      (terminals t*:ty-meta ...)
      rules:rule ...)
   (define rule-names (stx-map (prefix-id #'lang _) #'(rules.name ...)))
   (define all-cases (map flatten-rule-cases (attribute rules.case*)))
   ; quasisyntax + unsyntax-splicing, not a nested `#'` template: a rule may
   ; contain a literal `...` (from `,e ...`), which a nested `#'` would
   ; re-interpret as ellipsis instead of data
   (define lang-descriptor
     #`(language #,(attribute lang) (terminals #,@(attribute t*)) #,@(attribute rules)))
   ; compile-time binding read via syntax-local-value (construct.rkt,
   ; recur-match.rkt); named off `lang` since `lang` itself is a runtime binding
   (define meta-id (format-id #'lang "~a-meta" #'lang))
   (with-scope lang-scope
     (stx-map meta-variable/bind (add-scope #'(t* ...) lang-scope))
     (stx-map (rule/bind _ _)
              (add-scope #'((rules.meta ...) ...) lang-scope)
              rule-names)
     (define rule-results
       (stx-map (rule/expand _ _ _ _)
                (add-scope #`(#,@all-cases) lang-scope)
                #`(#,@all-cases)
                rule-names
                (attribute rules.name)))
     ; flattened the same way `all-cases` is: each result's `car` is itself a
     ; syntax LIST of definitions for that rule, not a single definition
     (define rule-defs (apply append (map (lambda (r) (syntax->list (car r))) rule-results)))
     (define meta-table #`(#,@(map cdr rule-results)))
     (define extends-id (format-id #'lang "~a-extends" #'lang))
     ; every language gets a printer for free -- `<lang>->sexp`, the inverse
     ; of `lang-construct` (see sexp-gen.rkt); nanopass-framework's unparser
     ; is the equivalent this mirrors
     (define sexp-id (format-id #'lang "~a->sexp" #'lang))
     #`(begin (define lang (quote-syntax #,lang-descriptor))
         (define-syntax #,meta-id (quote-syntax #,meta-table))
         (define-syntax #,extends-id (quote-syntax #f))
         #,@rule-defs
         #,(build-lang->sexp-def sexp-id meta-table (syntax-e #'lang))))]
  ; `(define-language Child (extends Parent) (NT (- lead ...)) ...)`
  ;
  ; Every nonterminal Child doesn't mention is inherited from Parent
  ; wholesale -- same ctor-ids, same struct types, not redefined -- so an
  ; untouched case is literally the same value in both languages, not a
  ; structurally-similar lookalike that happens to share a name. `(- lead
  ; ...)` drops named cases from an inherited nonterminal (e.g. a surface
  ; construct a lowering pass desugars away); MVP has no way to add cases,
  ; only remove them.
  ;
  ; This is what makes r/match*'s `#:auto` (recur-match.rkt) trustworthy:
  ; it doesn't guess correspondence between #:lang and #:to by matching
  ; names across two independently-authored languages -- it requires #:to
  ; to (transitively) extend #:lang, then reads back exactly the cases
  ; `extends` already carried over.
  [(_ lang:id ((~literal extends) parent:id) delta:extend-delta ...)
   (define parent-meta-id (format-id #'parent "~a-meta" #'parent))
   (define parent-table (syntax-local-value parent-meta-id (lambda () #f)))
   (unless parent-table
     (raise-syntax-error 'define-language (format "no such language: ~a" (syntax-e #'parent)) #'parent))
   (define parent-entries (syntax->list parent-table))
   (for ([nm (in-list (attribute delta.nt-name))])
     (unless (for/or ([e (in-list parent-entries)]) (eq? (syntax-e (ext-nt-entry-name e)) (syntax-e nm)))
       (raise-syntax-error 'define-language
                           (format "~a has no nonterminal ~a" (syntax-e #'parent) (syntax-e nm))
                           nm)))
   (define (removed-leads-for nt-sym)
     (or (for/or ([nm (in-list (attribute delta.nt-name))] [rm (in-list (attribute delta.removed))])
           (and (eq? (syntax-e nm) nt-sym) (map syntax-e rm)))
         '()))
   (define new-entries
     (for/list ([entry (in-list parent-entries)])
       (define nt-name (ext-nt-entry-name entry))
       (define remove-set (removed-leads-for (syntax-e nt-name)))
       (define all-cases (ext-nt-entry-cases entry))
       (for ([sym (in-list remove-set)])
         (unless (memq sym (map ext-case-entry-lead all-cases))
           (raise-syntax-error 'define-language
                               (format "~a's ~a has no case ~a to remove" (syntax-e #'parent) (syntax-e nt-name) sym)
                               #'lang)))
       (define kept (for/list ([ce (in-list all-cases)] #:unless (memq (ext-case-entry-lead ce) remove-set)) ce))
       #`(#,nt-name (#,@kept) (#,@(ext-nt-entry-leaf-types entry)))))
   (define type-defs
     (for/list ([entry (in-list new-entries)])
       (syntax-parse entry
         [(nt-name:id (ce ...) (lt ...))
          (define ctor-types (for/list ([ce (in-list (syntax->list #'(ce ...)))]) (ext-case-entry-ctor ce)))
          ; NOT `(prefix-id #'lang #'nt-name)`: prefix-id's hygiene context
          ; comes from its 2nd argument, and nt-name here was extracted from
          ; Parent's meta table, not from this macro's own input -- using it
          ; as context would make the resulting `Child:NT` identifier carry
          ; Parent's expansion history instead of Child's, so a plain
          ; `Child:NT` reference written by the user wouldn't resolve to it.
          ; Context must come from `lang` (this clause's own `lang:id`).
          #`(define-type #,(format-id #'lang "~a:~a" (syntax-e #'lang) (syntax-e #'nt-name))
              (U #,@ctor-types #,@(syntax->list #'(lt ...))))])))
   (define meta-id (format-id #'lang "~a-meta" #'lang))
   (define extends-id (format-id #'lang "~a-extends" #'lang))
   (define sexp-id (format-id #'lang "~a->sexp" #'lang))
   (define new-table #`(#,@new-entries))
   #`(begin
       (define-syntax #,meta-id (quote-syntax (#,@new-entries)))
       (define-syntax #,extends-id (quote-syntax parent))
       #,@type-defs
       #,(build-lang->sexp-def sexp-id new-table (syntax-e #'lang)))])

(module+ test
  (require typed/rackunit syntax/macro-testing)

  (define-language surface
    (terminals
      (Integer (n)))
    (Expr (e)
          ,n
          (+ ,e ,e)))

  (define a : surface:Expr (surface:Expr:+ 1 2))
  (check-equal? a a)
  ; every language gets `<lang>->sexp` for free -- no boilerplate `r/match*`
  ; pass needed just to print a term back as an s-expression
  (check-equal? (surface->sexp a) '(+ 1 2))
  (check-equal? (surface->sexp 5) 5)

  (define-language with-ellipsis
    (terminals
      (Integer (n))
      (Symbol (x)))
    (Expr (e)
          ,n
          (let ([,x ,e] ...) ,e)
          (block ,e ...)))

  (define b : with-ellipsis:Expr
    (with-ellipsis:Expr:let (list (list 'x 1) (list 'y 2)) 3))
  (check-equal? b b)

  (define c : with-ellipsis:Expr
    (with-ellipsis:Expr:block (list 1 2 3)))
  (check-equal? c c)

  (check-equal? (with-ellipsis->sexp b) '(let ((x 1) (y 2)) 3))
  (check-equal? (with-ellipsis->sexp c) '(block 1 2 3))

  (define-language core (extends with-ellipsis) (Expr (- let)))
  (define d : core:Expr (with-ellipsis:Expr:block (list 1 2 3)))
  (check-equal? (core->sexp d) '(block 1 2 3))

  ; a headed rule-case's own field can't be another headed form -- must fail
  ; at the offending grammar, not crash inside syntax-parse's internals
  (check-exn #rx"nested headed form as a field"
    (lambda ()
      (convert-compile-time-error
        (define-language Bad-Nested
          (terminals (Integer (n)))
          (Expr (e) ,n (Add ,e ,e) (Neg (Add ,e ,e))))))))
