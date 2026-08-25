#lang typed/racket
;; compile Arith down to a register-machine, asm-like target language.
;; validates the README's claim #2: a recursive lowering pass produces a
;; flat instruction list per subtree, and those lists are combined with
;; plain `append` before being spliced ONCE into the target AST node's
;; list field via `,@` -- `,@` itself only ever needs to resolve one
;; already-combined list, no matter how deep the source recursion goes.
(require "../main.rkt")

(define-language Arith
  (terminals
   (Integer (n))
   (Symbol (x)))
  (Expr (e)
        ,n
        (Var ,x)
        (Add ,e ,e)
        (Mul ,e ,e)))

(define-language Asm
  (terminals
   (Integer (n))
   (Symbol (r)))
  (Instr (i)
         (mov ,r ,n)         ; r := n
         (movr ,r ,r)        ; dst := src
         (add ,r ,r)         ; dst += src
         (mul ,r ,r)         ; dst *= src
         (block ,i ...)))    ; sequence

(: reg : Integer -> Symbol)
(define (reg i) (string->symbol (format "x~a" i)))

; we assume infinite registers here
(: compile-expr : Arith:Expr Symbol Integer -> (Listof Asm:Instr))
(define (compile-expr e dst depth)
  (r/match* e
    #:lang Arith
    #:on compile-expr ; unused: no clause here recurses via `,[x]`
    [(Add ,l ,r)
     (define scratch (reg depth))
     (define instrs-l (compile-expr l dst depth))
     (define instrs-r (compile-expr r scratch (add1 depth)))
     (append instrs-l instrs-r
             (list (lang-construct Asm Instr `(add ,dst ,scratch))))]
    [(Mul ,l ,r)
     (define scratch (reg depth))
     (define instrs-l (compile-expr l dst depth))
     (define instrs-r (compile-expr r scratch (add1 depth)))
     (append instrs-l instrs-r
             (list (lang-construct Asm Instr `(mul ,dst ,scratch))))]
    [(Var ,x) (list (lang-construct Asm Instr `(movr ,dst ,x)))]
    [,n (list (lang-construct Asm Instr `(mov ,dst ,n)))]))

(: compile-arith : Arith:Expr -> Asm:Instr)
(define (compile-arith e)
  (define instrs (compile-expr e (reg 0) 1))
  (lang-construct Asm Instr `(block ,@instrs)))

(: eval-arith : Arith:Expr (HashTable Symbol Integer) -> Integer)
(define (eval-arith e env)
  (define (self [e2 : Arith:Expr]) (eval-arith e2 env))
  (r/match* e
    #:lang Arith
    #:on self
    [(Add ,[l] ,[r]) (+ l r)]
    [(Mul ,[l] ,[r]) (* l r)]
    [(Var ,x) (hash-ref env x)]
    [,n n]))

(: interp-instr : Asm:Instr (Mutable-HashTable Symbol Integer) -> Void)
(define (interp-instr i env)
  (define (self [i2 : Asm:Instr]) (interp-instr i2 env))
  (r/match* i
    #:lang Asm
    #:on self
    [(mov ,r ,n) (hash-set! env r n)]
    [(movr ,dst ,src) (hash-set! env dst (hash-ref env src))]
    [(add ,dst ,src) (hash-set! env dst (+ (hash-ref env dst) (hash-ref env src)))]
    [(mul ,dst ,src) (hash-set! env dst (* (hash-ref env dst) (hash-ref env src)))]
    [(block ,[is] ...) (void is)]))

(: run-compiled : Asm:Instr (HashTable Symbol Integer) -> Integer)
(define (run-compiled program init-vars)
  (define env : (Mutable-HashTable Symbol Integer) (make-hash (hash->list init-vars)))
  (interp-instr program env)
  (hash-ref env (reg 0)))

(: instr->sexp : Asm:Instr -> Any)
(define (instr->sexp i)
  (r/match* i
    #:lang Asm
    #:on instr->sexp
    [(mov ,r ,n) (list 'mov r n)]
    [(movr ,dst ,src) (list 'mov dst src)]
    [(add ,dst ,src) (list 'add dst src)]
    [(mul ,dst ,src) (list 'mul dst src)]
    [(block ,[is] ...) (cons 'block is)]))

(module+ test
  (require typed/rackunit)

  ; (2 * 3) + (x + 0)
  (define e1
    (lang-construct Arith Expr `(Add (Mul ,2 ,3) (Add (Var ,'x) ,0))))
  ; ((1 + 2) + 3) + 4  -- left-leaning spine, checks register reuse down the left
  (define e2
    (lang-construct Arith Expr
                     `(Add (Add (Add ,1 ,2) ,3) ,4)))
  ; 1 + (2 + 3)  -- right-leaning, checks a fresh scratch chain on the right
  (define e3
    (lang-construct Arith Expr `(Add ,1 (Add ,2 ,3))))
  ; (x + y) * (x + y)  -- same subterm compiled twice, independent registers
  (define e4
    (lang-construct Arith Expr
                     `(Mul (Add (Var ,'x) (Var ,'y)) (Add (Var ,'x) (Var ,'y)))))

  (define (check-compiles-correctly [e : Arith:Expr] [env : (HashTable Symbol Integer)])
    (check-equal? (run-compiled (compile-arith e) env) (eval-arith e env)))

  (define no-vars : (HashTable Symbol Integer) (hash))
  (check-compiles-correctly e1 (hash 'x 10))
  (check-compiles-correctly e2 no-vars)
  (check-compiles-correctly e3 no-vars)
  (check-compiles-correctly e4 (hash 'x 3 'y 4)))

(module+ main
  (define e
    (lang-construct Arith Expr `(Add (Mul ,2 ,3) (Add (Var ,'x) ,0))))
  (define asm (compile-arith e))
  (printf "source: (2 * 3) + (x + 0)\n")
  (printf "asm:    ~a\n" (instr->sexp asm))
  (printf "result: ~a\n" (run-compiled asm (hash 'x 10))))
