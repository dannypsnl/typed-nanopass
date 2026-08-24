#lang typed/racket
(provide lang-construct)
(require syntax/parse/define
         (for-syntax racket/syntax
                     syntax/stx))

(begin-for-syntax
  ; classifies one raw quasiquote piece:
  ;   'scalar + the wrapped expr,  for `,expr`
  ;   'splice + the wrapped expr,  for `,@expr`
  ;   'raw    + the piece itself,  for anything else (e.g. a `[...]` bracket
  ;                                 literal, which is bare syntax, not
  ;                                 `,`/`,@`-headed)
  (define (parse-piece p)
    (syntax-parse p
      [((~literal unquote) e:expr) (values 'scalar #'e)]
      [((~literal unquote-splicing) e:expr) (values 'splice #'e)]
      [_ (values 'raw p)]))

  ; one tuple inside a tuple-list bracket literal, e.g. the `[,'x ,1]` in
  ; `([,'x ,1] [,'y ,2])` -- a bare list whose every element must be `,expr`
  ; (no nested splicing/raw pieces inside a tuple slot)
  (define (parse-tuple-template t)
    (syntax-parse t
      [(p ...)
       (for/list ([one (in-list (syntax->list #'(p ...)))])
         (define-values (kind val) (parse-piece one))
         (unless (eq? kind 'scalar)
           (raise-syntax-error 'lang-construct "tuple element must be `,expr`" one))
         val)]
      [_ (raise-syntax-error 'lang-construct "expected a tuple `[,x ,e ...]`" t)]))

  ; the `<lang>-meta` table (built by define-language.rkt's `rule/expand`) is
  ;   (nt-entry ...)
  ;   nt-entry    ::= (nt-name-id case-entry ...)
  ;   case-entry  ::= (lead-id ctor-id (field-shape ...))
  ;   field-shape ::= (scalar type) | (list type) | (tuple-list type ...)
  ; `lead`/`nt-name`/the shape tags are plain labels, not bound identifiers,
  ; so they're compared by symbol (`syntax-e`), never by hygiene -- comparing
  ; via `~literal`/`bound-id=?` would be wrong here (and would fail across
  ; modules besides): two `let`s typed in different places, even different
  ; modules, should count as the same case name purely by spelling.
  (define (find-nt-entry table nt-sym)
    (for/or ([entry (in-list (syntax->list table))])
      (syntax-parse entry
        [(nt-name:id _ ...) (and (eq? (syntax-e #'nt-name) nt-sym) entry)])))

  (define (find-case-entry nt-entry lead-sym)
    (syntax-parse nt-entry
      [(_ ce ...)
       (for/or ([ce (in-list (syntax->list #'(ce ...)))])
         (syntax-parse ce
           [(lead:id _ _) (and (eq? (syntax-e #'lead) lead-sym) ce)]))]))

  ; consumes `pieces` left-to-right against the ordered `field-shapes`,
  ; producing one argument expression per field. A `scalar` field always
  ; consumes exactly one `,expr`. A `tuple-list` field always consumes
  ; exactly one piece, whatever its position, since it's self-delimiting:
  ; either `,@expr` (an already-built list) or a bare `[...]` list of
  ; `[,x ,e ...]` tuples. A `list` field consumes exactly one `,@expr` UNLESS
  ; it's the last field, in which case it may instead greedily collect
  ; zero-or-more remaining bare `,expr` pieces into a list -- collecting is
  ; only unambiguous at the end, since nothing marks where it would stop
  ; otherwise.
  (define (consume-fields field-shapes pieces case-stx)
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
          (define-values (kind val) (parse-piece (car pieces)))
          (unless (eq? kind 'scalar)
            (raise-syntax-error 'lang-construct "expected `,expr`" (car pieces)))
          (cons val (consume-fields rest-shapes (cdr pieces) case-stx))]
         [(list)
          (cond
            [(pair? rest-shapes)
             ; not the last field: no unambiguous place to stop collecting,
             ; so this field must be filled by a single `,@expr`
             (when (null? pieces)
               (raise-syntax-error 'lang-construct "missing `,@expr` for list field" case-stx))
             (define-values (kind val) (parse-piece (car pieces)))
             (unless (eq? kind 'splice)
               (raise-syntax-error 'lang-construct
                                    "a list field before other fields needs `,@expr`"
                                    (car pieces)))
             (cons val (consume-fields rest-shapes (cdr pieces) case-stx))]
            [(and (pair? pieces) (null? (cdr pieces)))
             ; last field, exactly one piece left: either spelling is fine
             (define-values (kind val) (parse-piece (car pieces)))
             (list (if (eq? kind 'splice)
                       val
                       (begin
                         (unless (eq? kind 'scalar)
                           (raise-syntax-error 'lang-construct "expected `,expr` or `,@expr`" (car pieces)))
                         #`(list #,val))))]
            [else
             ; last field, zero or several pieces left: collect them all as
             ; bare `,expr`s (mixing in a `,@expr` here is ambiguous, so it's
             ; rejected with a clear error instead of guessed at)
             (define vals
               (for/list ([p (in-list pieces)])
                 (define-values (kind val) (parse-piece p))
                 (unless (eq? kind 'scalar)
                   (raise-syntax-error 'lang-construct
                                        "expected `,expr` (a single `,@expr` can't be mixed with other pieces here)"
                                        p))
                 val))
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
                            (define elems (parse-tuple-template t))
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
          (cons arg (consume-fields rest-shapes (cdr pieces) case-stx))])])))

; (lang-construct lang-id nt-id `(lead piece ...))
; e.g. (lang-construct with-ellipsis Expr `(let ,@bindings ,body))
;
; Builds an AST node of `lang-id`'s `nt-id` nonterminal using the same
; `,`/`,@` notation `define-language` uses to declare the grammar, resolved
; entirely at macro-expansion time against the `<lang>-meta` table
; `define-language` emits. There is deliberately no runtime shape check --
; Typed Racket's own check on the underlying struct constructor is the only
; safety net needed, since the field layout is already fully known here.
;
; Scope: a `scalar` field is always `,expr`. A `tuple-list` field is always
; one piece, either `,@expr` or a `[...]` list of `[,x ,e ...]` tuples. A
; `list` field is `,@expr` unless it's the case's last field, in which case
; it may instead be zero-or-more bare `,expr` pieces collected into a list --
; see `consume-fields` above for why only the last field gets that leniency.
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
   (define args (consume-fields field-shapes (syntax->list #'(piece ...)) this-syntax))
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
