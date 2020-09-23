#lang eopl
;; ex. 1.19
; Write a procedure free-vars that takes a list structure representing an expression
; in the lambda calculus syntax given above and returns a set (a list without duplicates)
; of all the variables that occur free in the expression. Similarly, write a procedure
; bound-vars that returns a set of all the variables that occur bound in its argument.

; <expression> := <identifier>
;              := (lambda (<identifier>) <expression>)
;              := (<expression> <expression>)

(define free-var?
  (lambda (v exp)
    (cond ((symbol? exp)
           (eqv? v exp))
          ((eqv? (car exp) 'lambda)
           (and (not (eqv? (caadr exp) v))
                (free-var? v (caddr exp))))
          (else (or (free-var? v (car exp))
                     (free-var? v (cadr exp)))))))
; test expressions
(define test-exp0 '(lambda (x) y))
(define test-exp1 '(lambda (f) (lambda (x) (f x))))
(define test-exp2 '((lambda (a) (a b)) (car x)))

(define get-all-vars
  (lambda (exp)
    (cond ((symbol? exp) (list exp))
          ((eqv? (car exp) 'lambda)
           (get-all-vars (caddr exp)))
          (else (append
                 (get-all-vars (car exp))
                 (get-all-vars (cadr exp)))))))

(define free-vars
  (lambda (exp)
    (define aux
      (lambda (vars free)
        (cond ((null? vars) free)
              ((free-var? (car vars) exp)
               (if (not (member (car vars) free))
                   (aux (cdr vars) (cons (car vars) free))
                   (aux (cdr vars) free)))
              (else (aux (cdr vars) free)))))
    (aux (get-all-vars exp) '())))

               