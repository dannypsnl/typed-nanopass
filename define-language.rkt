#lang typed/racket
(provide define-language)
(require syntax/parse/define racket/match
         (for-syntax ee-lib
                     fancy-app
                     racket/syntax
                     racket/string
                     syntax/stx))

(define-for-syntax (prefix-id prefix id)
  (format-id id #:source id #:props id "~a:~a" prefix id))

; the internal, never-user-typed key for a nonterminal's untagged case
; (`(,fn ,arg)` -- no leading id, e.g. function application). Deterministic
; (not a true gensym): it's independently re-derived in two places
; (rule-case/meta-type and rule/expand) that must agree on the identical
; identifier for the resulting define-type/struct pair to actually link up
; -- format-id with the same inputs always does, via free-identifier=?,
; the same trick prefix-id already relies on. Reserved-prefixed so it can
; never collide with a symbol a user actually wrote as a case tag;
; construct.rkt/recur-match.rkt each independently check for this same
; prefix (mirrored, not shared, matching this file's existing convention).
(define-for-syntax (untagged-id nt-name)
  (format-id nt-name #:source nt-name #:props nt-name "#%untagged:~a" nt-name))

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
      #:attr shapes #f
      #:attr untagged? #f)
    ; `([,x ,e] ...)`, e.g. `(let ([,x ,e] ...) ,e)`
    (pattern ((((~literal unquote) m*:id) ...+) (~datum ...))
      #:attr intro-ty #f
      #:attr as-field #`[#,(generate-temporary 'tuple*)
                         : (Listof (List #,@(stx-map lookup #'(m* ...))))]
      #:attr shape #`(tuple-list #,@(stx-map lookup #'(m* ...)))
      #:attr shapes #f
      #:attr untagged? #f)
    ; `,x`
    (pattern ((~literal unquote) meta:id)
      #:attr intro-ty #f
      #:attr as-field #`[#,(generate-temporary #'meta) : #,(lookup #'meta)]
      #:attr shape #`(scalar #,(lookup #'meta))
      #:attr shapes #f
      #:attr untagged? #f)
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
      #:attr shapes #'(c*.shape ...)
      #:attr untagged? #f)
    ; `(,fn ,arg)` -- untagged headed form, e.g. function application with
    ; no keyword. `fn` is itself the case's first field (there's no
    ; separate tag to discard), so its own scalar field-spec is prepended
    ; to `c*`'s. The real struct-name/lead-symbol (untagged-id) needs the
    ; enclosing nonterminal's name, which isn't known here -- `intro-ty`
    ; just marks "this introduces a struct" (any truthy value), same as
    ; for a tagged case; rule/expand substitutes the real name in. At most
    ; one untagged case per nonterminal is allowed, checked there too
    ; (only it sees the whole case list at once).
    (pattern (((~literal unquote) fn:id) c*:rule-case ...+)
      #:fail-when (ormap values (attribute c*.intro-ty))
                  "nested headed form as a field of another case isn't supported yet -- give it its own top-level case and reference it through a meta-variable instead"
      #:attr intro-ty #'fn
      #:attr as-field
        (syntax-property
          #`(#,(let ([g (generate-temporary #'fn)]) #`[#,g : #,(lookup #'fn)]) c*.as-field ...)
          'field #t)
      #:attr shape #f
      #:attr shapes #`((scalar #,(lookup #'fn)) c*.shape ...)
      #:attr untagged? #t)
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
      ; untagged headed form -- same deterministic name rule/expand uses,
      ; prefixed the same way a tagged case's struct type name is
      [(((~literal unquote) fn:id) c* ...) (prefix-id name (untagged-id name))]
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
              (define untagged-flags (attribute c*.untagged?))
              (when (> (length (filter values untagged-flags)) 1)
                (raise-syntax-error 'define-language
                  (format "~a has more than one untagged case -- at most one per nonterminal is supported"
                          (syntax-e orig-name))
                  stx))
              ; an untagged case's struct-name/lead-symbol is derived from
              ; the nonterminal alone (untagged-id) instead of intro-ty's
              ; raw value -- intro-ty there is just a truthy "this
              ; introduces a struct" marker, same role it plays for a
              ; tagged case
              (define struct-names
                (for/list ([ity (attribute c*.intro-ty)] [u? untagged-flags])
                  (if u? (untagged-id name) ity)))
              (list
                (for/list ([struct-name struct-names]
                           [fields (syntax->list #'(scoped-c*.as-field ...))]
                           #:when struct-name)
                  #`(struct #,(prefix-id name struct-name) #,fields #:transparent))
                ; shapes/shape must come from scoped-c*, not c* -- they call
                ; lookup internally, which only resolves scoped identifiers
                (for/list ([struct-name struct-names]
                           [shapes (attribute scoped-c*.shapes)]
                           #:when struct-name)
                  #`(#,struct-name #,(prefix-id name struct-name) (#,@shapes)))
                (for/list ([struct-name struct-names]
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

  ; every nonterminal this table declares, as its bare name (not
  ; lang-prefixed) -- see sx-nonterminal-type? for why
  (define (sx-source-nt-syms table)
    (for/list ([nt-entry (in-list (syntax->list table))])
      (syntax-e (ext-nt-entry-name nt-entry))))

  ; a type-id recurses if its symbol names one of this table's own
  ; nonterminals -- compared by the BARE name (the part after the last
  ; `:`), not the full `lang:NT` symbol: `extends` inherits a case's
  ; field-shapes verbatim, so an inherited field's recorded type is
  ; prefixed with whichever ancestor language originally declared that
  ; case (e.g. `Surface:Expr` on a case Core inherited unchanged), not
  ; necessarily this table's own language -- matching on the bare
  ; nonterminal name is what makes recursion still fire on those
  ; inherited fields instead of silently treating them as terminals.
  (define (sx-nonterminal-type? type-id nt-syms)
    (define parts (string-split (symbol->string (syntax-e type-id)) ":"))
    (and (pair? parts) (memq (string->symbol (car (reverse parts))) nt-syms) #t))

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

  ; an untagged case's lead-id is never user-written -- it's always
  ; untagged-id's reserved-prefixed output -- so it's printed with no tag
  ; at all, `(fn-sexp arg-sexp)`, matching the original untagged syntax
  ; instead of leaking the internal key.
  (define (sx-untagged-lead? lead) (string-prefix? (symbol->string (syntax-e lead)) "#%untagged:"))

  ; one `[(Ctor f ...) (append (list 'lead) part ...)]` match clause (or,
  ; for an untagged case, `(append part ...)` with no lead at all)
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
    (if (sx-untagged-lead? lead)
        #`[(#,ctor #,@field-vars) (append #,@parts)]
        #`[(#,ctor #,@field-vars) (append (list (quote #,lead)) #,@parts)]))

  ; (build-lang->sexp-def name-id table) -> syntax
  ;
  ; `name-id : Any -> Any`, matching every case of every nonterminal `table`
  ; (a language's `<lang>-meta` table) declares, and reconstructing the plain
  ; s-expression that would rebuild it via `lang-construct` -- `(lead field
  ; ...)`, recursing into nonterminal-typed fields via `name-id` itself and
  ; copying terminal-typed fields as-is. A case's own lead name is always
  ; what gets printed; there's no per-case custom pretty name/abbreviation
  ; (write that by hand, e.g. via a plain `r/match*` pass, when one's
  ; wanted).
  (define (build-lang->sexp-def name-id table)
    (define nt-syms (sx-source-nt-syms table))
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

; parser -- the inverse of the unparser block above
(begin-for-syntax
  ; `<lang>:<NT>`, the type <lang>'s NT rule expands to. Context comes from
  ; `lang` for the same reason the extends clause spells it out below: an
  ; inherited nt-name carries the PARENT language's expansion history.
  (define (px-nt-type-id lang-id nt-name)
    (format-id lang-id "~a:~a" (syntax-e lang-id) (syntax-e nt-name)))
  ; `sexp-><lang>:<NT>` -- one parser per nonterminal, not one per language:
  ; a bare s-expression doesn't say which nonterminal it belongs to, and a
  ; language has no privileged entry nonterminal to assume (see README).
  (define (px-parser-id lang-id nt-sym)
    (format-id lang-id "sexp->~a:~a" (syntax-e lang-id) nt-sym))
  ; the nonterminal a field type names, by its bare name -- same
  ; last-`:`-segment rule sx-nonterminal-type? explains
  (define (px-bare-nt-sym type-id)
    (string->symbol (car (reverse (string-split (symbol->string (syntax-e type-id)) ":")))))
  (define (px-recur-id lang-id ty) (px-parser-id lang-id (px-bare-nt-sym ty)))

  (define (px-list-field? fs) (eq? (sx-field-shape-tag fs) 'list))

  ; one value slot: recur through this language's own parser when the field
  ; is a nonterminal, otherwise check the terminal type at runtime.
  ; `pred-for` hands back an identifier bound to that type's `make-predicate`
  ; -- so a terminal type has to be one Typed Racket can build a predicate
  ; for (any flat type is), the one constraint this generated parser adds
  ; over the rest of define-language.
  (define (px-scalar-conv v ty nt-syms lang-id who pred-for)
    (if (sx-nonterminal-type? ty nt-syms)
        #`(#,(px-recur-id lang-id ty) #,v)
        #`(if (#,(pred-for ty) #,v)
              #,v
              (error '#,who "expected ~a, got: ~e" '#,(syntax->datum ty) #,v))))

  ; `,e ...` -- the match pattern already spliced these out as siblings, so
  ; the binding is the whole list
  (define (px-list-conv v ty nt-syms lang-id who pred-for)
    (define one (generate-temporary 'one))
    #`(for/list : (Listof #,ty) ([#,one : Any (in-list #,v)])
        #,(px-scalar-conv one ty nt-syms lang-id who pred-for)))

  ; `[,x ,e] ...` -- one sexp element, a list of arity-N tuples. `assert
  ; list?` is what tells Typed Racket the `Any` this matched really is a
  ; list; the inner `match` does the same job for each tuple's own shape.
  (define (px-tuple-list-conv v tys nt-syms lang-id who pred-for)
    (define one (generate-temporary 'one))
    (define comps (for/list ([_ (in-list tys)]) (generate-temporary 'c)))
    (define converted
      (for/list ([c (in-list comps)] [ty (in-list tys)])
        (px-scalar-conv c ty nt-syms lang-id who pred-for)))
    #`(for/list : (Listof (List #,@tys)) ([#,one : Any (in-list (assert #,v list?))])
        (match #,one
          [(list #,@comps) (list #,@converted)]
          [_ (error '#,who "expected a ~a-element tuple, got: ~e" #,(length tys) #,one)])))

  ; one `[(list 'lead pat ...) (Ctor arg ...)]` match clause (for an untagged
  ; case, `(list pat ...)` with no lead -- mirroring how the unparser prints
  ; it with no tag). A `,e ...` field contributes `pat ...` to the pattern,
  ; every other field contributes exactly one pattern, which is what makes
  ; the positions line up with what <lang>->sexp emitted.
  (define (px-build-case-clause ce nt-syms lang-id who pred-for)
    (define-values (lead ctor field-shapes) (sx-case-entry-parts ce))
    (define untagged? (sx-untagged-lead? lead))
    (cond
      ; two `...` fields in one case can't be split back apart from the
      ; printed form (and `match` won't take two ellipses in one list
      ; pattern either) -- a tagged case still gets a clause, so the failure
      ; names the case instead of just the nonterminal. An untagged one has
      ; no lead to recognize it by, so it gets no clause at all and falls
      ; through to the nonterminal-level error below.
      [(> (length (filter px-list-field? field-shapes)) 1)
       (and (not untagged?)
            #`[(list-rest (quote #,lead) _)
               (error '#,who
                      "case ~a has more than one `...` field -- sexp-> can't parse it back unambiguously"
                      '#,lead)])]
      [else
       (define field-vars (for/list ([_ (in-list field-shapes)]) (generate-temporary 'f)))
       (define pats
         (apply append
           (for/list ([fs (in-list field-shapes)] [v (in-list field-vars)])
             ; `...` reaches the pattern as spliced data, never as template
             ; text -- a `#'` template would read it as an ellipsis instead
             (if (px-list-field? fs) (list v (datum->syntax lang-id '...)) (list v)))))
       (define args
         (for/list ([fs (in-list field-shapes)] [v (in-list field-vars)])
           (define rest (sx-field-shape-rest fs))
           (case (sx-field-shape-tag fs)
             [(scalar) (px-scalar-conv v (car rest) nt-syms lang-id who pred-for)]
             [(list) (px-list-conv v (car rest) nt-syms lang-id who pred-for)]
             [(tuple-list) (px-tuple-list-conv v rest nt-syms lang-id who pred-for)])))
       (if untagged?
           #`[(list #,@pats) (#,ctor #,@args)]
           #`[(list (quote #,lead) #,@pats) (#,ctor #,@args)])]))

  ; (build-sexp->lang-defs lang-id table) -> syntax
  ;
  ; `sexp-><lang>:<NT> : Any -> <lang>:<NT>` for every nonterminal `table`
  ; declares, mutually recursive, undoing what `<lang>->sexp` printed. Cases
  ; are tried in declaration order, the untagged case only after every tagged
  ; one (its pattern has no lead to tell it apart by), and bare terminal
  ; alternatives last, so a structured form is never eaten by a leaf whose
  ; type happens to admit it. Anything left over is a runtime error naming
  ; the nonterminal it failed against -- parsing is the one place a
  ; well-typed program still meets input the grammar can't vouch for.
  (define (build-sexp->lang-defs lang-id table)
    (define nt-syms (sx-source-nt-syms table))
    ; one `make-predicate` per distinct terminal type, hoisted out of the
    ; parsers so it isn't rebuilt per call
    (define preds (make-hash))
    (define pred-defs '())
    (define (pred-for ty)
      (define key (syntax->datum ty))
      (or (hash-ref preds key #f)
          (let ([id (generate-temporary 'terminal?)])
            (hash-set! preds key id)
            (set! pred-defs (cons #`(define #,id (make-predicate #,ty)) pred-defs))
            id)))
    (define parser-defs
      (for/list ([nt-entry (in-list (syntax->list table))])
        (define nt-name (ext-nt-entry-name nt-entry))
        (define fn-id (px-parser-id lang-id (syntax-e nt-name)))
        (define nt-type (px-nt-type-id lang-id nt-name))
        (define x (generate-temporary 'sexp))
        ; the untagged case's pattern has no lead to tell it apart by, so it
        ; goes after every tagged one -- otherwise `(Var x)` would parse as
        ; an application of `Var` in a language that has both
        (define (untagged-case? ce)
          (define-values (lead _ctor _fs) (sx-case-entry-parts ce))
          (sx-untagged-lead? lead))
        (define all-cases (ext-nt-entry-cases nt-entry))
        (define ordered-cases
          (append (filter (lambda (ce) (not (untagged-case? ce))) all-cases)
                  (filter untagged-case? all-cases)))
        (define case-clauses
          (filter values
                  (for/list ([ce (in-list ordered-cases)])
                    (px-build-case-clause ce nt-syms lang-id (syntax-e fn-id) pred-for))))
        (define leaf-clauses
          (for/list ([lt (in-list (ext-nt-entry-leaf-types nt-entry))])
            (define v (generate-temporary 'leaf))
            #`[(? #,(pred-for lt) #,v) #,v]))
        #`(begin
            (: #,fn-id : Any -> #,nt-type)
            (define (#,fn-id #,x)
              (match #,x
                #,@case-clauses
                #,@leaf-clauses
                [_ (error '#,(syntax-e fn-id) "cannot parse as ~a: ~e" '#,(syntax-e nt-type) #,x)])))))
    #`(begin #,@(reverse pred-defs) #,@parser-defs)))

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
     ; of `lang-construct`; nanopass-framework's unparser is the equivalent
     ; this mirrors (see the `unparser` begin-for-syntax block above)
     (define sexp-id (format-id #'lang "~a->sexp" #'lang))
     ; a terminal type only gets typechecked by virtue of landing in a
     ; generated struct field/leaf-type union -- which only happens if some
     ; rule actually uses one of its meta-variables. A terminal declared but
     ; never referenced by any rule (typo'd meta-variable name, dead
     ; leftover, ...) would otherwise compile silently with a bogus type.
     ; Force every declared terminal type through Typed Racket's own checker
     ; regardless of use, same "let TR check it" approach the rest of this
     ; file already relies on instead of hand-rolled validation.
     (define terminal-checks
       (for/list ([ty (in-list (attribute t*.type))])
         #`(define-type #,(generate-temporary 'terminal-check) #,ty)))
     #`(begin (define lang (quote-syntax #,lang-descriptor))
         (define-syntax #,meta-id (quote-syntax #,meta-table))
         (define-syntax #,extends-id (quote-syntax #f))
         #,@terminal-checks
         #,@rule-defs
         #,(build-lang->sexp-def sexp-id meta-table)
         #,(build-sexp->lang-defs #'lang meta-table)))]
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
       #,(build-lang->sexp-def sexp-id new-table)
       #,(build-sexp->lang-defs #'lang new-table))])

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
  ; ... and a parser per nonterminal, `sexp-><lang>:<NT>`, the inverse of
  ; `<lang>->sexp` -- per nonterminal, not per language, since a bare
  ; s-expression doesn't say which one it belongs to
  (check-equal? (sexp->surface:Expr '(+ 1 2)) a)
  (check-equal? (sexp->surface:Expr 5) 5)
  (check-equal? (sexp->surface:Expr (surface->sexp a)) a)
  ; parsing is where a well-typed program meets input the grammar can't
  ; vouch for, so every field is checked: a nonterminal one by recurring,
  ; a terminal one against its own type (see the `let` binder below)
  (check-exn #rx"cannot parse as surface:Expr: 'x"
    (lambda () (sexp->surface:Expr '(+ x 2))))
  (check-exn #rx"cannot parse as surface:Expr"
    (lambda () (sexp->surface:Expr '(- 1 2))))

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
  ; ellipsis fields round-trip: `,e ...` splices into siblings of the lead,
  ; `[,x ,e] ...` stays one bracketed element
  (check-equal? (sexp->with-ellipsis:Expr '(let ((x 1) (y 2)) 3)) b)
  (check-equal? (sexp->with-ellipsis:Expr '(block 1 2 3)) c)
  (check-equal? (sexp->with-ellipsis:Expr (with-ellipsis->sexp b)) b)
  (check-equal? (sexp->with-ellipsis:Expr '(block))
                (with-ellipsis:Expr:block (list)))
  (check-equal? (sexp->with-ellipsis:Expr '(block 1 (block 2) 3))
                (with-ellipsis:Expr:block (list 1 (with-ellipsis:Expr:block (list 2)) 3)))
  (check-exn #rx"expected a 2-element tuple"
    (lambda () (sexp->with-ellipsis:Expr '(let ((x)) 3))))
  (check-exn #rx"expected Symbol, got: 1"
    (lambda () (sexp->with-ellipsis:Expr '(let ((1 1)) 3))))

  (define-language core (extends with-ellipsis) (Expr (- let)))
  (define d : core:Expr (with-ellipsis:Expr:block (list 1 2 3)))
  (check-equal? (core->sexp d) '(block 1 2 3))
  ; an extended language's parser accepts exactly the cases it kept -- a
  ; removed one is no longer parseable, the whole point of removing it
  (check-equal? (sexp->core:Expr '(block 1 2 3)) d)
  (check-exn #rx"cannot parse as core:Expr"
    (lambda () (sexp->core:Expr '(let ((x 1)) 2))))

  ; a headed rule-case's own field can't be another headed form -- must fail
  ; at the offending grammar, not crash inside syntax-parse's internals
  (check-exn #rx"nested headed form as a field"
    (lambda ()
      (convert-compile-time-error
        (define-language Bad-Nested
          (terminals (Integer (n)))
          (Expr (e) ,n (Add ,e ,e) (Neg (Add ,e ,e)))))))

  ; `(,fn ,arg)` -- untagged case, e.g. function application with no
  ; keyword. `<lang>->sexp` prints it with no tag at all, matching the
  ; original untagged syntax.
  (define-language with-app
    (terminals
      (Integer (n))
      (Symbol (x)))
    (Expr (e)
          ,n
          (Var ,x)
          (Lam ,x ,e)
          (,e ,e)))

  (define app : with-app:Expr
    (with-app:Expr:#%untagged:with-app:Expr
     (with-app:Expr:Var 'f) (with-app:Expr:Var 'x)))
  (check-equal? (with-app->sexp app) '((Var f) (Var x)))
  ; nested untagged application: ((f x) y)
  (define nested-app : with-app:Expr
    (with-app:Expr:#%untagged:with-app:Expr
     app (with-app:Expr:Var 'y)))
  (check-equal? (with-app->sexp nested-app) '(((Var f) (Var x)) (Var y)))
  ; the parser tries the untagged case only after every tagged one, so
  ; `(Var f)` is still a Var, not an application of `Var`
  (check-equal? (sexp->with-app:Expr '((Var f) (Var x))) app)
  (check-equal? (sexp->with-app:Expr '(((Var f) (Var x)) (Var y))) nested-app)
  (check-equal? (sexp->with-app:Expr '(Var f)) (with-app:Expr:Var 'f))

  ; extends inherits an untagged case's cases verbatim, including recursion
  ; into an inherited field whose recorded type is prefixed with the
  ; PARENT language's name (with-app:Expr), not the child's own
  ; (with-app-core:Expr) -- <lang>->sexp must still recurse there, not
  ; silently treat it as a terminal
  (define-language with-app-core (extends with-app) (Expr (- Lam)))
  (define core-app : with-app-core:Expr
    (with-app:Expr:#%untagged:with-app:Expr
     (with-app:Expr:Var 'f) (with-app:Expr:Var 'x)))
  (check-equal? (with-app-core->sexp core-app) '((Var f) (Var x)))

  ; a case with two `...` fields can't be split back apart from the printed
  ; form -- it still prints, and says so where it failed when parsed
  (define-language two-ellipsis
    (terminals (Integer (n)))
    (Expr (e) ,n (both ,e ... ,e ...)))
  (check-equal? (two-ellipsis->sexp (two-ellipsis:Expr:both (list 1) (list 2)))
                '(both 1 2))
  (check-exn #rx"more than one `[.][.][.]` field"
    (lambda () (sexp->two-ellipsis:Expr '(both 1 2))))

  ; at most one untagged case per nonterminal
  (check-exn #rx"more than one untagged case"
    (lambda ()
      (convert-compile-time-error
        (define-language Bad-Untagged
          (terminals (Integer (n)) (Symbol (x)))
          (Expr (e) ,n (Var ,x) (,e ,e) (,e ,e ,e)))))))
