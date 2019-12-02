#lang racket
(require "environments.rkt")

; environment (represented/w hash)

(define-syntax letM
  (syntax-rules ()
    [(letM ([x init]) body)
     (mbind init (λ (x) body))]))

;; This set of definitions implement an interpreter
#;
(begin  
  (define (return v)
    (box v))
  
  (define (mbind v f)
    (f (unbox v)))

  (define (run mv)
    (unbox mv))

  (define (δ-zero? n)
    (return (zero? n)))
  (define (δ-sub1 n)
    (return (sub1 n)))
  (define (δ-* n m)
    (return (* n m)))
  (define (δ-call/cc v)
    (call/cc
     (λ (k)
       (apply-closure v (λ (u) (k (return u)))))))
  (define (δ-if b k1 k2)
    (if b (k1) (k2)))
  
  (define (make-closure env x body)
    (return
     (λ (arg)
       (valof body (extend-env x arg env)))))

  (define (apply-closure clos arg)
    (clos arg)))

;; uniquify
#;
(begin
  (define (return v)
    (λ (s)
      (values v s)))
  
  (define (mbind mv f)
    (λ (s)
      (let-values ([(v s) (mv s)])
        ((f v) s))))

  (define (run mv)
    (let-values ([(v _) (mv 0)])
      v))

  (define (get-state)
    (λ (s) (values s s)))

  (define (set-state s*)
    (λ (s) (values (void) s*)))

  (define (δ-zero? n)
    (return `(zero? ,n)))
  (define (δ-sub1 n)
    (return `(sub1 ,n)))
  (define (δ-* n m)
    (return `(* ,n ,m)))
  (define (δ-call/cc v)
    (return `(call/cc ,v)))
  (define (δ-if b k1 k2)
    (letM ([thn (k1)])
      (letM ([els (k2)])
        (return `(if ,b ,thn ,els)))))
  
  (define (make-closure env x body)
    (letM ([counter (get-state)])
      (letM ([_ (set-state (add1 counter))])
        (let ([x^ (string->symbol (string-append "x." (number->string counter)))])
          (letM ([body^ (valof body (extend-env x x^ env))])
            (return `(λ (,x^) ,body^)))))))

  (define (apply-closure clos arg)
    (return `(,clos ,arg))))

;; ANFize
#;
(begin
  
  (define (return v)
    (cons '() v))
  
  (define (mbind mv f)
    (match-let ([(cons stm*1 v) mv])
      (match-let ([(cons stm*2 u) (f v)])
        (cons (append stm*1 stm*2) u))))

  (define (run mv)
    `(let* ,(car mv)
       ,(cdr mv)))

  (define (save v)
    (if (or (number? v)
            (symbol? v))
        (cons '() v)
        (let ([x (gensym)])
          (cons (list (list x v)) x))))

  (define (δ-zero? n)
    (letM ([x (save n)])
      (return `(zero? ,x))))
  (define (δ-sub1 n)
    (letM ([x (save n)])
      (return `(sub1 ,x))))
  (define (δ-* n m)
    (letM ([x (save n)])
      (letM ([y (save m)])
        (return `(* ,x ,y)))))
  (define (δ-call/cc v)
    (letM ([x (save v)])
      (return `(call/cc ,x))))
  (define (δ-if b k1 k2)
    (return `(if ,b
                 ,(run (k1))
                 ,(run (k2)))))
  
  (define (make-closure env x body)
    (return `(λ (,x) ,(run (valof body (extend-env x x env))))))

  (define (apply-closure clos arg)
    (letM ([x (save clos)])
      (letM ([y (save arg)])
        (return `(,x ,y))))))

;; CPSed interpreter

#;
(begin
  
  (define (return v)
    (λ (k)
      (k v)))
  
  (define (mbind mv f)
    (λ (k)
      (mv (λ (v) ((f v) k)))))

  (define (run mv)
    (let ([kx (gensym)])
      (mv (λ (v) v))))

  (define (mcall/cc f)
    (λ (k)
      (let ([k-as-v (λ (v) (λ (k^) (k v)))])
        ((f k-as-v) k))))

  (define (δ-zero? n)
    (return (zero? n)))
  (define (δ-sub1 n)
    (return (sub1 n)))
  (define (δ-* n m)
    (return (* n m)))
  
  (define (δ-call/cc clos)
    (mcall/cc
     (λ (klos)
       (apply-closure clos klos))))
  
  (define (δ-if b k1 k2)
    (if b (k1) (k2)))
  
  (define (make-closure env x body)
    (return
     (λ (arg)
       (valof body (extend-env x arg env)))))

  (define (apply-closure clos arg)
    (clos arg)))

;; CPSer
(begin
  
  (define (return v)
    (λ (k)
      (k v)))
  
  (define (mbind mv f)
    (λ (k)
      (mv (λ (v) ((f v) k)))))

  (define (run mv)
    (let ([kx (gensym)])
      (mv (λ (v) v))))

  (define (mcall/cc f)
    (λ (k)
      (let ([k-as-v `(λ (v) (λ (k^) ,(k 'v)))])
        ((f k-as-v) k))))

  (define (δ-zero? n)
    (return `(zero? ,n)))
  (define (δ-sub1 n)
    (return `(sub1 ,n)))
  (define (δ-* n m)
    (return `(* ,n ,m)))
  
  (define (δ-call/cc clos)
    (mcall/cc
     (λ (klos)
       (apply-closure clos klos))))
  
  (define (δ-if b k1 k2)
    #;(if b (k1) (k2))
    #;(λ (k) (if b ((k1) k) ((k2) k)))
    (λ (k) `(if ,b ,((k1) k) ,((k2) k))))
  
  (define (make-closure env x body)
    #;(return (λ (arg)
                (valof body (extend-env x arg env))))
    #;(return (λ (arg)
                (λ (k)
                  ((valof body (extend-env x arg env)) k))))
    #;(return (λ (arg)
                (λ (k)
                  ((valof body (extend-env x arg env))
                   (λ (v) (k v))))))
    (let ([arg (gensym)])
      (return `(λ (,arg)
                 (λ (k)
                   ,((valof body (extend-env x arg env))
                     (λ (v) `(k ,v))))))))

  (define (apply-closure clos arg)
    #;(clos arg)
    #;(λ (k) ((clos arg) k))
    #;(λ (k) ((clos arg) (λ (v) (k v))))
    (λ (k) `((,clos ,arg) (λ (v) ,(k 'v))))))

(define (valof exp env)
  (match exp
    [`,y
     #:when (symbol? y)
     (return (apply-env env y))]
    [`,n
     #:when (number? n)
     (return n)]
    [`,b
     #:when (boolean? b)
     (return b)]
    [`(zero? ,n)
     (letM ([v (valof n env)])
       (δ-zero? v))]
    [`(sub1 ,n)
     (letM ([v (valof n env)])
       (δ-sub1 v))]
    [`(* ,n ,m)
     (letM ([v (valof n env)])
       (letM ([u (valof m env)])
         (δ-* v u)))]
    [`(if ,cnd ,thn ,els)
     (letM ([v (valof cnd env)])
       (δ-if v
             (λ () (valof thn env))
             (λ () (valof els env))))]
    [`(call/cc ,e)
     (letM ([v (valof e env)])
       (δ-call/cc v))]
    [`(λ (,x) ,body)
     (make-closure env x body)]
    [`(,rator ,rand)
     (letM ([v (valof rator env)])
       (letM ([u (valof rand env)])
         (apply-closure v u)))]))

(run
 (valof
  '(* 5
      (call/cc
       (λ (k)
         (* 5
            (k ((λ (fact)
                  ((fact fact) 4))
                (λ (fact)
                  (λ (n)
                    (if (zero? n)
                        1
                        (* ((fact fact) (sub1 n)) n))))))))))
  (empty-env)))