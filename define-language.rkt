#lang typed/racket
(provide define-language)
(require syntax/parse/define
         (for-syntax ee-lib
                     fancy-app
                     racket/syntax
                     syntax/stx))

(define-for-syntax (prefix-id prefix id)
  (format-id id #:source id #:props id "~a:~a" prefix id))

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
  (define-syntax-class rule-case
    ; syntax `,x`, which means `x` is a meta variable
    (pattern (unquote meta:id)
      #:attr intro-ty #f
      #:attr as-field #`[#,(generate-temporary #'meta) : #,(lookup #'meta)])
    ; syntax `(+ ,e ,e)`, which means `+` should be a new structure, with fields `([e1 : T] [e2 : T])`
    ; the `T` here is fetching from the language definition
    ;
    ; TODO: The syntax that nested and with splicing `(let ([,x ,e] ...) ,e)`
    (pattern (lead:id c*:rule-case ...+)
      #:attr intro-ty #'lead
      #:attr as-field (syntax-property #'(c*.as-field ...) 'field #t))
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
  (define (rule/expand scoped-stx stx name)
    (syntax-parse scoped-stx
      [(scoped-c*:rule-case ...)
       (with-syntax
           ([(ty ...) (stx-map (rule-case/meta-type _ name) #'(scoped-c* ...))]
            [(case-struct ...) (syntax-parse stx
                                 [(c*:rule-case ...)
                                  (for/list ([struct-name (attribute c*.intro-ty)]
                                             [fields (syntax->list #'(scoped-c*.as-field ...))]
                                             #:when struct-name)
                                    #`(struct #,(prefix-id name struct-name) #,fields #:transparent))])])
         #`((define-type #,name (U ty ...)) case-struct ...))])))

(define-syntax-parser define-language
  [(_ lang:id
      (terminals t*:ty-meta ...)
      rules:rule ...)
   (define rule-names (stx-map (prefix-id #'lang _) #'(rules.name ...)))
   (with-scope lang-scope
     (stx-map meta-variable/bind (add-scope #'(t* ...) lang-scope))
     (stx-map (rule/bind _ _)
              (add-scope #'((rules.meta ...) ...) lang-scope)
              rule-names)
     (with-syntax
         ([((rule/define-types^ ...) ...)
           (stx-map (rule/expand _ _ _)
                    (add-scope #'((rules.case* ...) ...) lang-scope)
                    #'((rules.case* ...) ...)
                    rule-names)])
       #'(begin (define lang #'(language lang
                                         (terminals t* ...)
                                         rules ...))
                rule/define-types^
                ... ...)))])

(module+ test
  (require typed/rackunit)

  (define-language surface
    (terminals
     (Integer (n)))
    (Expr (e)
          ,n
          (+ ,e ,e)))

  (define a : surface:Expr (surface:Expr:+ 1 2))
  (check-equal? a a))
