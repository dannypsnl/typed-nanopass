#lang typed/racket
;; constant folding + algebraic-identity optimization, written with r/match*
;; and lang-construct
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

#|
n1 + n2 => [[n1 + n2]]
n1 * n2 => [[n1 * n2]]
e + 0 => [[e]], 0 + e => [[e]]
e * 1 => [[e]], 1 * e => [[e]]
e * 0 => [[0]], 0 * e => [[0]]
|#
(: optimize : Arith:Expr -> Arith:Expr)
(define (optimize e)
  (r/match* e
    #:lang Arith
    #:on optimize
    [(Add ,[l] ,[r])
     (cond
       [(and (integer? l) (integer? r)) (+ l r)]
       [(equal? l 0) r]
       [(equal? r 0) l]
       [else (lang-construct Arith Expr `(Add ,l ,r))])]
    [(Mul ,[l] ,[r])
     (cond
       [(and (integer? l) (integer? r)) (* l r)]
       [(or (equal? l 0) (equal? r 0)) 0]
       [(equal? l 1) r]
       [(equal? r 1) l]
       [else (lang-construct Arith Expr `(Mul ,l ,r))])]
    [(Var ,x) (lang-construct Arith Expr `(Var ,x))]
    [,n n]))

(: expr->sexp : Arith:Expr -> Any)
(define (expr->sexp e)
  (r/match* e
    #:lang Arith
    #:on expr->sexp
    [(Add ,[l] ,[r]) (list '+ l r)]
    [(Mul ,[l] ,[r]) (list '* l r)]
    [(Var ,x) x]
    [,n n]))

(module+ test
  (require typed/rackunit)

  ; (2 * 3) + (x + 0)  =>  6 + x
  (define e1 (lang-construct Arith Expr `(Add (Mul ,2 ,3) (Add (Var ,'x) ,0))))
  (check-equal? (expr->sexp (optimize e1)) '(+ 6 x))

  ; (x * 1) * 0  =>  0
  (define e2 (lang-construct Arith Expr `(Mul (Mul (Var ,'x) ,1) ,0)))
  (check-equal? (expr->sexp (optimize e2)) 0))

(module+ main
  (define e (lang-construct Arith Expr `(Add (Mul ,2 ,3) (Add (Var ,'x) ,0))))
  (printf "before: ~a\n" (expr->sexp e))
  (printf "after:  ~a\n" (expr->sexp (optimize e))))
