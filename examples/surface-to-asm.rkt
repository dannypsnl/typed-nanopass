#lang typed/racket
;; three-stage pipeline: SurfaceArith --(desugar-sub)--> CoreArith --(compile)--> Asm
;;
;; This exists to feel out README's unlisted fourth question: real nanopass's
;; headline feature is that a pass only writes the cases that actually change
;; shape -- every nonterminal case that's identical between the source and
;; target language gets its traversal auto-generated. `desugar-sub` is the
;; proof: SurfaceArith and CoreArith differ by exactly one case (`Sub`), and
;; `r/match*`'s `#:auto` writes every other case (Add, Mul, Var, the leaf) for
;; us -- recurse into nonterminal-typed fields, copy terminal-typed fields,
;; rebuild in the target language, and refuse to compile (naming the missing
;; case) if a source case has no home in the target at all. 1 real
;; transformation, 0 hand-written boilerplate.
(require "../main.rkt")

(define-language SurfaceArith
  (terminals
   (Integer (n))
   (Symbol (x)))
  (Expr (e)
        ,n
        (Var ,x)
        (Add ,e ,e)
        (Sub ,e ,e)       ; not in CoreArith -- desugared to (Add l (Mul r -1))
        (Mul ,e ,e)))

(define-language CoreArith
  (extends SurfaceArith)
  (Expr (- Sub)))

(define-language Asm
  (terminals
   (Integer (n))
   (Symbol (r)))
  (Instr (i)
         (mov ,r ,n)
         (movr ,r ,r)
         (add ,r ,r)
         (mul ,r ,r)
         (block ,i ...)))

;; --- pass 1: SurfaceArith -> CoreArith -----------------------------------
;; Only `Sub` is a real transformation; #:auto fills in Add/Mul/Var/leaf.
(: desugar-sub : SurfaceArith:Expr -> CoreArith:Expr)
(define (desugar-sub e)
  (r/match* e
    #:lang SurfaceArith #:to CoreArith #:on desugar-sub #:auto
    [(Sub ,[l] ,[r]) (lang-construct CoreArith Expr `(Add ,l (Mul ,r ,-1)))]))

;; --- pass 2: CoreArith -> Asm (same Sethi-Ullman codegen as arith-to-asm) --
(: reg : Integer -> Symbol)
(define (reg i) (string->symbol (format "x~a" i)))

(: compile-expr : CoreArith:Expr Symbol Integer -> (Listof Asm:Instr))
(define (compile-expr e dst depth)
  (r/match* e
    #:lang CoreArith
    #:on compile-expr ; unused: no clause here recurses via `,[x]`
    [(Add ,l ,r)
     (define scratch (reg depth))
     (define instrs-l (compile-expr (cast l CoreArith:Expr) dst depth))
     (define instrs-r (compile-expr (cast r CoreArith:Expr) scratch (add1 depth)))
     (append instrs-l instrs-r
             (list (lang-construct Asm Instr `(add ,dst ,scratch))))]
    [(Mul ,l ,r)
     (define scratch (reg depth))
     (define instrs-l (compile-expr (cast l CoreArith:Expr) dst depth))
     (define instrs-r (compile-expr (cast r CoreArith:Expr) scratch (add1 depth)))
     (append instrs-l instrs-r
             (list (lang-construct Asm Instr `(mul ,dst ,scratch))))]
    [(Var ,x) (list (lang-construct Asm Instr `(movr ,dst ,x)))]
    [,n (list (lang-construct Asm Instr `(mov ,dst ,n)))]))

(: compile-core : CoreArith:Expr -> Asm:Instr)
(define (compile-core e)
  (define instrs (compile-expr e (reg 0) 1))
  (lang-construct Asm Instr `(block ,@instrs)))

(: compile-surface : SurfaceArith:Expr -> Asm:Instr)
(define (compile-surface e) (compile-core (desugar-sub e)))

;; --- reference interpreters, for correctness checks ----------------------
(: eval-surface : SurfaceArith:Expr (HashTable Symbol Integer) -> Integer)
(define (eval-surface e env)
  (define (self [e2 : SurfaceArith:Expr]) (eval-surface e2 env))
  (r/match* e
    #:lang SurfaceArith
    #:on self
    [(Add ,[l] ,[r]) (+ l r)]
    [(Sub ,[l] ,[r]) (- l r)]
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

(module+ test
  (require typed/rackunit)

  ; (x - 5) * (3 - x)
  (define e1
    (lang-construct SurfaceArith Expr
                     `(Mul (Sub (Var ,'x) ,5) (Sub ,3 (Var ,'x)))))
  ; (10 - (2 - 3)) - 1  -- nested Sub, checks desugaring composes
  (define e2
    (lang-construct SurfaceArith Expr
                     `(Sub (Sub ,10 (Sub ,2 ,3)) ,1)))

  (define (check-pipeline [e : SurfaceArith:Expr] [env : (HashTable Symbol Integer)])
    (check-equal? (run-compiled (compile-surface e) env) (eval-surface e env)))

  (define no-vars : (HashTable Symbol Integer) (hash))
  (check-pipeline e1 (hash 'x 7))
  (check-pipeline e2 no-vars))

(module+ main
  (define e
    (lang-construct SurfaceArith Expr
                     `(Mul (Sub (Var ,'x) ,5) (Sub ,3 (Var ,'x)))))
  (define core (desugar-sub e))
  (define asm (compile-core core))
  (printf "surface: (x - 5) * (3 - x)\n")
  (printf "asm:     ~a\n" (Asm->sexp asm))
  (define x 7)
  (printf "With x = ~a, result = ~a\n" x (run-compiled asm (hash 'x x))))
