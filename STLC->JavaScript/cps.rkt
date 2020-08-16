#lang racket
(provide cps)
(require "./ind-Exp.rkt")

(define new
  (let ([counter (box 0)])
    (λ ()
      (set-box! counter (add1 (unbox counter)))
      (string->symbol
       (format "cps_~a" (unbox counter))))))

(define (cps e)
  (rec e (Var 'exit)))

(define (cps-lambda x body)
  (let ([c (new)])
    (Lambda c
            (Lambda x
                    (rec body (Var c))))))

(define (rec e k)
  (match e
    [(Let x (Apply rator rand) body)
     (let ([t1 (new)]
           [xk (new)])
       (Let xk (Lambda x (rec body k))
            (Let t1 (Apply rator (Var xk))
                 (Apply (Var t1) rand))))]
    [(Let x (Call/cc f) body)
     (let ([t1 (new)]
           [t2 (new)]
           [t3 (new)])
       (Let t1 (Lambda x (rec body k))
            (Let t2 (Apply f (Var t1))
                 (Let t3 (Lambda (new) (Var t1))
                      (Apply (Var t2) (Var t3))))))]
    [(Let x (Lambda y body*) body)
     (Let x (cps-lambda y body*) (rec body k))]
    [(Let x init body) (Let x init (rec body k))]
    [(Lambda x body) (let ([t (new)])
                       (Let t (cps-lambda x body)
                            (Apply k (Var t))))]
    [(Apply rator rand) (let ([f (new)])
                          (Let f (Apply rator k)
                               (Apply (Var f) rand)))]
    [(Call/cc f) (let ([x (new)]
                       [y (new)])
                   (Let x (Apply f k)
                        (Let y (Lambda (new) k)
                             (Apply (Var x) (Var y)))))]
    [(Which target onl onr)
     (let ([f (new)]
           [g (new)])
       (Let f (Apply onl k)
            (Let g (Apply onr k)
                 (Which target (Var f) (Var g)))))]
    [_ (let ([t (new)])
         (Let t e
              (Apply k (Var t))))]))

