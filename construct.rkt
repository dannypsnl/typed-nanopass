#lang typed/racket
(provide lang-construct)
(require syntax/parse/define
         (for-syntax racket/syntax
                     syntax/stx))

(begin-for-syntax
  ; classifies one raw quasiquote piece: 'scalar/'splice wrap the expr
  ; (`,expr`/`,@expr`); 'raw is anything else (e.g. a `[...]` bracket literal)
  (define (parse-piece p)
    (syntax-parse p
      [((~literal unquote) e:expr) (values 'scalar #'e)]
      [((~literal unquote-splicing) e:expr) (values 'splice #'e)]
      [_ (values 'raw p)]))

  ; one tuple in a tuple-list bracket literal, e.g. `[,'x ,1]` in
  ; `([,'x ,1] [,'y ,2])` -- each element resolved via resolve-piece-expr
  (define (parse-tuple-template table t)
    (syntax-parse t
      [(p ...)
       (for/list ([one (in-list (syntax->list #'(p ...)))])
         (resolve-piece-expr table one))]
      [_ (raise-syntax-error 'lang-construct "expected a tuple `[,x ,e ...]`" t)]))

  ; a nested shape's nonterminal isn't known up front, unlike the outermost
  ; call's nt-id, so search every nonterminal for the lead-id
  (define (find-case-entry-anywhere table lead-sym)
    (for/or ([nt-entry (in-list (syntax->list table))])
      (syntax-parse nt-entry
        [(_ (ce ...) _)
         (for/or ([one (in-list (syntax->list #'(ce ...)))])
           (syntax-parse one
             [(lead:id _ _) (and (eq? (syntax-e #'lead) lead-sym) one)]))])))

  ; a raw piece that isn't `,expr`/`,@expr` must be a nested shape, e.g.
  ; `(Mul ,2 ,3)` -- build its constructor call recursively
  (define (build-nested-construct table piece)
    (syntax-parse piece
      [(lead:id sub-piece ...)
       (define ce (find-case-entry-anywhere table (syntax-e #'lead)))
       (unless ce
         (raise-syntax-error 'lang-construct
                              (format "no case ~a in this language" (syntax-e #'lead))
                              piece))
       (define-values (ctor-id field-shapes)
         (syntax-parse ce [(_ ctor:id (fs ...)) (values #'ctor (syntax->list #'(fs ...)))]))
       (define args (consume-fields table field-shapes (syntax->list #'(sub-piece ...)) piece))
       #`(#,ctor-id #,@args)]
      [_ (raise-syntax-error 'lang-construct "expected `,expr` or a nested `(lead ...)` shape" piece)]))

  ; resolves one value-slot piece: `,expr` used directly, or a bare
  ; `(lead ...)` shape resolved recursively -- lets `(Add (Mul ,2 ,3) ,r)`
  ; work without `,(lang-construct ...)` at every level
  (define (resolve-piece-expr table piece)
    (define-values (kind val) (parse-piece piece))
    (case kind
      [(scalar) val]
      [(splice) (raise-syntax-error 'lang-construct "expected `,expr` here, not `,@expr`" piece)]
      [(raw) (build-nested-construct table piece)]))

  ; <lang>-meta table (built by define-language.rkt's rule/expand):
  ;   (nt-entry ...)
  ;   nt-entry    ::= (nt-name-id (case-entry ...) (leaf-type ...))
  ;   case-entry  ::= (lead-id ctor-id (field-shape ...))
  ;   field-shape ::= (scalar type) | (list type) | (tuple-list type ...)
  ; leaf-type isn't used here (only r/match* needs it). lead/nt-name are
  ; compared by symbol, not hygiene -- they're plain labels, not bindings.
  (define (find-nt-entry table nt-sym)
    (for/or ([entry (in-list (syntax->list table))])
      (syntax-parse entry
        [(nt-name:id _ ...) (and (eq? (syntax-e #'nt-name) nt-sym) entry)])))

  (define (find-case-entry nt-entry lead-sym)
    (syntax-parse nt-entry
      [(_ (ce ...) _)
       (for/or ([ce (in-list (syntax->list #'(ce ...)))])
         (syntax-parse ce
           [(lead:id _ _) (and (eq? (syntax-e #'lead) lead-sym) ce)]))]))

  ; consumes pieces left-to-right against field-shapes, one arg expr per
  ; field. tuple-list always takes exactly one piece (self-delimiting: `,@expr`
  ; or a `[...]` list of tuples). list takes one `,@expr` unless it's the
  ; last field, where it may instead collect zero-or-more bare pieces
  ; (unambiguous only at the end).
  (define (consume-fields table field-shapes pieces case-stx)
    (cond
      [(null? field-shapes)
       (unless (null? pieces)
         (raise-syntax-error 'lang-construct "too many pieces" case-stx))
       '()]
      [else
       (define fs (car field-shapes))
       (define rest-shapes (cdr field-shapes))
       (define tag (syntax-e (car (syntax->list fs))))
       (case tag
         [(scalar)
          (when (null? pieces)
            (raise-syntax-error 'lang-construct "missing `,expr`" case-stx))
          (define arg (resolve-piece-expr table (car pieces)))
          (cons arg (consume-fields table rest-shapes (cdr pieces) case-stx))]
         [(list)
          (cond
            [(pair? rest-shapes)
             (when (null? pieces)
               (raise-syntax-error 'lang-construct "missing `,@expr` for list field" case-stx))
             (define-values (kind val) (parse-piece (car pieces)))
             (unless (eq? kind 'splice)
               (raise-syntax-error 'lang-construct
                                   "a list field before other fields needs `,@expr`"
                                   (car pieces)))
             (cons val (consume-fields table rest-shapes (cdr pieces) case-stx))]
            [(and (pair? pieces) (null? (cdr pieces)))
             (define-values (kind val) (parse-piece (car pieces)))
             (list (if (eq? kind 'splice)
                       val
                       #`(list #,(resolve-piece-expr table (car pieces)))))]
            [else
             (define vals
               (for/list ([p (in-list pieces)])
                 (define-values (kind _) (parse-piece p))
                 (when (eq? kind 'splice)
                   (raise-syntax-error 'lang-construct
                                       "expected `,expr` (a single `,@expr` can't be mixed with other pieces here)"
                                       p))
                 (resolve-piece-expr table p)))
             (list #`(list #,@vals))])]
         [(tuple-list)
          (when (null? pieces)
            (raise-syntax-error 'lang-construct "missing value for tuple-list field" case-stx))
          (define-values (kind val) (parse-piece (car pieces)))
          (define arity (sub1 (length (syntax->list fs))))
          (define arg
            (case kind
              [(splice) val]
              [(raw)
               (define tuples (syntax->list (car pieces)))
               (unless tuples
                 (raise-syntax-error 'lang-construct
                                     "expected `,@expr` or a `[...]` list of tuples"
                                     (car pieces)))
               #`(list #,@(for/list ([t (in-list tuples)])
                            (define elems (parse-tuple-template table t))
                            (unless (= (length elems) arity)
                              (raise-syntax-error 'lang-construct
                                                  (format "tuple has ~a element~a, field expects ~a"
                                                          (length elems)
                                                          (if (= 1 (length elems)) "" "s")
                                                          arity)
                                                  t))
                            #`(list #,@elems)))]
              [else (raise-syntax-error 'lang-construct
                                        "expected `,@expr` or a `[...]` list of tuples"
                                        (car pieces))]))
          (cons arg (consume-fields table rest-shapes (cdr pieces) case-stx))])])))

; (lang-construct lang-id nt-id `(lead piece ...))
; e.g. (lang-construct Arith Expr `(Add (Mul ,2 ,3) ,r))
;
; Builds an AST node using the grammar's own `,`/`,@` notation, resolved
; entirely at macro-expansion time against the `<lang>-meta` table
; define-language emits -- no runtime shape check, Typed Racket's own check
; on the struct constructor is the only safety net needed. Nesting (`(Mul
; ,2 ,3)` above) needs no repeated `lang-construct`/backticks; it's just more
; quasiquote data, resolved recursively.
;
; Scope: a scalar field's piece is `,expr` or a nested `(lead ...)` shape.
; tuple-list is one piece, `,@expr` or a `[...]` list of tuples. list is
; `,@expr` unless it's the case's last field, where it may instead be
; zero-or-more collected pieces (see consume-fields for why).
(define-syntax-parser lang-construct
  [(_ lang-id:id nt-id:id ((~literal quasiquote) (lead:id piece ...)))
   (define meta-id (format-id #'lang-id "~a-meta" #'lang-id))
   (define table (syntax-local-value meta-id (lambda () #f)))
   (unless table
     (raise-syntax-error 'lang-construct
                         (format "no such language: ~a" (syntax-e #'lang-id))
                         #'lang-id))
   (define nt-entry (find-nt-entry table (syntax-e #'nt-id)))
   (unless nt-entry
     (raise-syntax-error 'lang-construct
                         (format "~a has no nonterminal ~a" (syntax-e #'lang-id) (syntax-e #'nt-id))
                         #'nt-id))
   (define case-entry (find-case-entry nt-entry (syntax-e #'lead)))
   (unless case-entry
     (raise-syntax-error 'lang-construct
                         (format "~a's ~a has no case ~a" (syntax-e #'lang-id) (syntax-e #'nt-id) (syntax-e #'lead))
                         #'lead))
   (define-values (ctor-id field-shapes)
     (syntax-parse case-entry
       [(_ ctor:id (fs ...)) (values #'ctor (syntax->list #'(fs ...)))]))
   (define args (consume-fields table field-shapes (syntax->list #'(piece ...)) this-syntax))
   #`(#,ctor-id #,@args)])

(module+ test
  (require typed/rackunit "define-language.rkt")

  (define-language surface
    (terminals
      (Integer (n)))
    (Expr (e)
          ,n
          (+ ,e ,e)))

  (check-equal? (lang-construct surface Expr `(+ ,1 ,2))
                (surface:Expr:+ 1 2))
  (check-equal? (lang-construct surface Expr `(+ (+ ,1 ,2) ,3))
                (surface:Expr:+ (surface:Expr:+ 1 2) 3))

  (define-language with-ellipsis
    (terminals
      (Integer (n))
      (Symbol (x)))
    (Expr (e)
          ,n
          (let ([,x ,e] ...) ,e)
          (block ,e ...)))

  (check-equal? (lang-construct with-ellipsis Expr `(block ,1 ,2 ,3))
                (with-ellipsis:Expr:block (list 1 2 3)))
  (check-equal? (lang-construct with-ellipsis Expr `(block))
                (with-ellipsis:Expr:block (list)))

  (define block-items : (Listof with-ellipsis:Expr) (list 1 2 3))
  (check-equal? (lang-construct with-ellipsis Expr `(block ,@block-items))
                (with-ellipsis:Expr:block (list 1 2 3)))

  (check-equal? (lang-construct with-ellipsis Expr `(let ([,'x ,1] [,'y ,2]) ,3))
                (with-ellipsis:Expr:let (list (list 'x 1) (list 'y 2)) 3))

  (define bindings : (Listof (List Symbol with-ellipsis:Expr))
    (list (list 'x 1) (list 'y 2)))
  (check-equal? (lang-construct with-ellipsis Expr `(let ,@bindings ,3))
                (with-ellipsis:Expr:let (list (list 'x 1) (list 'y 2)) 3)))
