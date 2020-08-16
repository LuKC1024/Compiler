#lang racket
(provide print-js)
(require "./ind-Exp.rkt")

(define (T2 e)
  (match e
    [(Var 'exit) "TOP"]
    [(Var id) (symbol->string id)]
    [(Quote datum) #:when (symbol? datum)
     (format "\"~a\"" datum)]
    [(Quote datum) #:when (integer? datum)
     (number->string datum)]))

(define (T1 e)
  (match e
    [(Lambda x body)
     (format "function(~a){~a}" x (T-body body))]
    [(Apply rator rand)
     (format "(~a)(~a)" (T2 rator) (T2 rand))]
    [(Inl v) (format "{which:true,val:~a}" (T2 v))]
    [(Inr v) (format "{which:false,val:~a}" (T2 v))]
    [(Car v) (format "~a.car" (T2 v))]
    [(Cdr v) (format "~a.cdr" (T2 v))]
    [(Cons a d) (format "{car:~a,cdr:~a}" (T2 a) (T2 d))]
    [(Delta '+ (list n m)) (format "(~a+~a)" (T2 n) (T2 m))]
    [(Delta '- (list n m)) (format "(~a-~a)" (T2 n) (T2 m))]
    [(Delta '* (list n m)) (format "(~a*~a)" (T2 n) (T2 m))]
    [(Delta '/ (list n m)) (format "(~a/~a)" (T2 n) (T2 m))]
    [(Delta '= (list n m))
     (format "{which:~a===~a,val:null}" (T2 n) (T2 m))]
    [_ (T2 e)]))

(define (T-body e)
  (match e
    [(Let x init body)
     (format "let ~a = ~a; ~a" x (T1 init) (T-body body))]
    [(Which tgt onl onr)
     (string-join
      (list
       (format "if(~a.which){F = ~a}else{F = ~a}"
               (T2 tgt) (T2 onl) (T2 onr))
       (format "V = ~a.val;" (T2 tgt))))]
    [(Apply rator rand)
     (format "F = ~a; V = ~a;" (T2 rator) (T2 rand))]
    [_ (format "return ~a;" (T1 e))]))

(define (translate e)
  (format
   (string-join
    (list "(function(){"
          "var TOP = {};"
          "var F = null;"
          "var V = [];"
          "~a"
          "while(true){"
          "if (F === TOP) {return V;}"
          "F(V)"
          "}})()"))
   (T-body e)))

(define (print-js e)
  (display (translate e)))
