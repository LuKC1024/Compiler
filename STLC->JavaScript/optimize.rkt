#lang racket
(provide optimize)
(require "./ind-Exp.rkt")


(define (empty-env) (hash))
(define (extend-env x v env) (hash-set env x v))
(define (apply-env env x) (hash-ref env x))

(define (optimize e)
  ;; introduced in cps
  (rec e (extend-env 'exit (Var 'exit) (empty-env))))

(define (subst2 arg env)
  (match arg
    [(Var id) (apply-env env id)]
    [(Quote datum) (Quote datum)]))

(define (subst1 se env)
  (match se
    [(Lambda x body)
     (Lambda x (rec body (extend-env x (Var x) env)))]
    [(Apply rator rand) (Apply (subst2 rator env)
                               (subst2 rand env))]
    [(Inl v) (Inl (subst2 v env))]
    [(Inr v) (Inr (subst2 v env))]
    [(Which target onl onr)
     (Which (subst2 target env)
            (subst2 onl env)
            (subst2 onr env))]
    [(Car v) (Car (subst2 v env))]
    [(Cdr v) (Cdr (subst2 v env))]
    [(Cons a d) (Cons (subst2 a env)
                      (subst2 d env))]
    [(Delta op rands)
     (Delta op (map (λ (arg) (subst2 arg env)) rands))]
    [arg (subst2 arg env)]))

(define (rec e env)
  (match e
    [(Let x (Var y) body)
     (rec body (extend-env x (apply-env env y) env))]
    [(Let x (Quote datum) body)
     (rec body (extend-env x (Quote datum) env))]
    [(Let x init body)
     (Let x (subst1 init env)
          (rec body (extend-env x (Var x) env)))]
    [_ (subst1 e env)]))