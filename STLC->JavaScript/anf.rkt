#lang racket
(provide anf)
(require "./ind-Exp.rkt")

(define (bind e f)
  (let rec ([e e])
    (match e
      [(Let x init body) (Let x init (rec body))]
      [e (let ([x (new)])
           (Let x e (f (Var x))))])))

(define new
  (let ([counter (box 0)])
    (λ ()
      (set-box! counter (add1 (unbox counter)))
      (string->symbol
       (format "anf_~a" (unbox counter))))))

(define (anf e)
  (ind-Exp e
    (λ (id) (Var id))
    (λ (datum) (Quote datum))
    (λ (f) (bind f (λ (v) (Call/cc v))))
    (λ (x init body) (bind init
                       (λ (v)
                         (Let x v body))))
    (λ (x body) (Lambda x body))
    (λ (rator rand)
      (bind rator
        (λ (x)
          (bind rand
            (λ (y) (Apply x y))))))
    (λ (v) (bind v (λ (v) (Inl v))))
    (λ (v) (bind v (λ (v) (Inr v))))
    (λ (tgt onl onr)
      (bind tgt
        (λ (x)
          (bind onl
            (λ (y)
              (bind onr
                (λ (z)
                  (Which x y z))))))))
    (λ (v) (bind v (λ (v) (Car v))))
    (λ (v) (bind v (λ (v) (Cdr v))))
    (λ (a d)
      (bind a
        (λ (a)
          (bind d
            (λ (d) (Cons a d))))))
    (λ (op rands)
      (let rec ([rands rands]
                [k (λ (args) (Delta op args))])
        (cond
          [(null? rands) (k '())]
          [else (bind (car rands)
                  (λ (v)
                    (rec (cdr rands)
                      (λ (vs) (k (cons v vs))))))])))))
