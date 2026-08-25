#lang typed/racket
(provide define-language)
(require syntax/parse/define
         (for-syntax ee-lib
                     fancy-app
                     racket/syntax
                     syntax/stx))

(define-for-syntax (prefix-id prefix id)
  (format-id id #:source id #:props id "~a:~a" prefix id))

; `rule-case` is a splicing syntax class: a single repetition may consume more
; than one raw form (e.g. `,e ...`). Re-templating its bare pattern variable
; (or `(attribute x)`) as syntax therefore wraps every repetition in an extra
; list layer; this undoes that wrapping back into one flat list of case forms.
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
    ; syntax `,x`, which means `x` is a meta variable
    ;
    ; NOTE: must come before the plain leaf pattern below, so `,x ...`
    ; is recognized as one list-field case instead of a leaf case
    ; followed by a dangling, unmatchable `...`
    (pattern (~seq ((~literal unquote) meta:id) (~datum ...))
      #:attr intro-ty #f
      #:attr as-field #`[#,(generate-temporary #'meta) : (Listof #,(lookup #'meta))]
      ; `shape` records this case's field kind for `lang-construct` (see
      ; construct.rkt): a scalar/list/tuple-list tag plus its field type(s),
      ; reusing the exact same `lookup` calls `as-field` already uses.
      #:attr shape #`(list #,(lookup #'meta))
      #:attr shapes #f)
    ; syntax `([,x ,e] ...)`, a list of tuples built from several meta variables,
    ; e.g. `(let ([,x ,e] ...) ,e)`
    (pattern ((((~literal unquote) m*:id) ...+) (~datum ...))
      #:attr intro-ty #f
      #:attr as-field #`[#,(generate-temporary 'tuple*)
                         : (Listof (List #,@(stx-map lookup #'(m* ...))))]
      #:attr shape #`(tuple-list #,@(stx-map lookup #'(m* ...)))
      #:attr shapes #f)
    ; syntax `,x`, which means `x` is a meta variable
    (pattern ((~literal unquote) meta:id)
      #:attr intro-ty #f
      #:attr as-field #`[#,(generate-temporary #'meta) : #,(lookup #'meta)]
      #:attr shape #`(scalar #,(lookup #'meta))
      #:attr shapes #f)
    ; syntax `(+ ,e ,e)`, which means `+` should be a new structure, with fields `([e1 : T] [e2 : T])`
    ; the `T` here is fetching from the language definition
    ;
    ; TODO: nested headed forms as a field of another headed form aren't
    ; flattened correctly yet (as-field below assumes leaf/list-field children)
    (pattern (lead:id c*:rule-case ...+)
      #:attr intro-ty #'lead
      #:attr as-field (syntax-property #'(c*.as-field ...) 'field #t)
      ; a headed case has no `shape` of its own; `shapes` (one per child,
      ; reconstructed from the named `.shape` attribute -- safe, unlike
      ; reconstructing a bare splicing-class pattern variable) is what
      ; `rule/expand` turns into that case's table entry
      #:attr shape #f
      #:attr shapes #'(c*.shape ...))
    ; TODO: please consider the syntax without leading id
    ; for example, we might like to write application just `(,fn ,arg)`
    ; rather than `(app ,fn ,arg) => (,fn ,arg)`
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
  ; returns `(cons definitions nt-entry)`: `definitions` is the struct/type
  ; forms for this rule (as before); `nt-entry` is this rule's slice of the
  ; `<lang>-meta` table both `lang-construct` (construct.rkt) and `r/match*`
  ; (recur-match.rkt) read back later --
  ; `(orig-name ((lead ctor-id (field-shape ...)) ...) (leaf-type ...))`
  ; `leaf-type` collects the type of each top-level bare `,x` alternative
  ; (e.g. `,n` in `(Expr (e) ,n (Add ,e ,e))`) -- these don't get a struct or
  ; a case-entry, but `r/match*` needs their type to narrow a leaf clause's
  ; binding, which a bare match pattern variable can't do on its own.
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
                ; `shapes`/`shape` must come from `scoped-c*`, not `c*` --
                ; they call `lookup` internally (same as `as-field` above),
                ; which only resolves against scoped identifiers
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

(define-syntax-parser define-language
  [(_ lang:id
      (terminals t*:ty-meta ...)
      rules:rule ...)
   (define rule-names (stx-map (prefix-id #'lang _) #'(rules.name ...)))
   (define all-cases (map flatten-rule-cases (attribute rules.case*)))
   ; built with quasisyntax + unsyntax-splicing (not a nested `#'` template):
   ; a rule's source may itself contain a literal `...` (from `,e ...`), and a
   ; `#'` template nested inside this macro's own `#'` output re-interprets
   ; every `...` it sees, including ones that are just data, not ellipsis
   (define lang-descriptor
     #`(language #,(attribute lang) (terminals #,@(attribute t*)) #,@(attribute rules)))
   ; `<lang>-meta` (a compile-time-only binding, looked up via
   ; `syntax-local-value` by construct.rkt's `lang-construct`) holds the
   ; `(nt-entry ...)` table described above `rule/expand`. Bound under a name
   ; derived from `lang`, since `lang` itself is already a runtime binding.
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
     #`(begin (define lang (quote-syntax #,lang-descriptor))
         (define-syntax #,meta-id (quote-syntax #,meta-table))
         #,@rule-defs))])

(module+ test
  (require typed/rackunit)

  (define-language surface
    (terminals
      (Integer (n)))
    (Expr (e)
          ,n
          (+ ,e ,e)))

  (define a : surface:Expr (surface:Expr:+ 1 2))
  (check-equal? a a)

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
  (check-equal? c c))
