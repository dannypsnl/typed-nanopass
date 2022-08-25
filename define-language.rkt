#lang typed/racket
(provide define-language)
(require syntax/parse/define
         (for-syntax ee-lib
                     fancy-app
                     racket/list
                     racket/syntax
                     syntax/stx))

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
  (define/hygienic (meta-variable/bind stx) #:definition
    (syntax-parse stx
      [(type (meta:id ...))
       (for-each (bind! _ #'#'type)
                 (syntax->list #'(meta ...)))]))

  (define/hygienic (rule-case/meta-type stx lang name) #:expression
    (syntax-parse stx
      ; lookup a meta-variable associated type
      [((~literal unquote) meta:id) (lookup #'meta)]
      ; build the struct name
      [(lead:id c* ...)
       (format-id #'lead #:source #'lead #:props #'lead
                  "~a:~a:~a" lang name #'lead)]))

  (define/hygienic (rule/expand stx lang) #:definition
    (syntax-parse stx
      [(name:id (meta:id ...+) c*:rule-case ...+)
       (for-each (bind! _ #`#'#,(format-id #'name "~a:~a" lang #'name))
                 (syntax->list #'(meta ...)))
       (with-syntax ([(ty ...) (stx-map (rule-case/meta-type _ lang #'name) #'(c* ...))])
         #'(U ty ...))]))

  (define (gen/case-name stx)
    (syntax-parse stx
      [(name (_ ...) c*:rule-case ...)
       (for/list ([c (attribute c*.intro-ty)]
                  #:when c)
         (format-id c #:source c #:props c
                    "~a:~a" #'name c))]))

  (define (gen/case-field stx)
    (syntax-parse stx
      [(_ (_ ...) c*:rule-case ...)
       (filter (λ (stx) (syntax-property stx 'field))
               (attribute c*.as-field))])))

(define-syntax-parser define-language
  [(_ lang:id
      (terminals t*:ty-meta ...)
      rules:rule ...)
   (define (prefix-lang stx) (format-id stx #:source stx #:props stx
                                        "~a:~a" #'lang stx))
   (with-scope lang-scope
     (stx-map meta-variable/bind (add-scope #'(t* ...) lang-scope))
     (with-syntax
         ([(rule-names ...) (stx-map prefix-lang #'(rules.name ...))]
          [(rule-types^ ...) (stx-map (rule/expand _ #'lang)
                                      (add-scope #'(rules ...) lang-scope))]
          [(rule-case-names ...) (map prefix-lang (flatten (stx-map gen/case-name #'(rules ...))))]
          [(rule-case-fields ...) (flatten (stx-map gen/case-field (add-scope #'(rules ...) lang-scope)))])
       #'(begin (define lang #'(language lang
                                         (terminals t* ...)
                                         rules ...))
                (struct rule-case-names
                  rule-case-fields #:transparent)
                ...
                (define-type rule-names rule-types^)
                ...)))])

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
