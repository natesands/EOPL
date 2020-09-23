#lang eopl

#| Exercise 2.11

Extend lambda calculus expression to include constants 3, *, and +.

|#

;; Do we need both a lit-exp and a const-exp??

(define-datatype expression expression?
  (const-exp (c (lambda (x) (memv x '(* + 3)))))
  (lit-exp
   (datum number?))
  (var-exp
   (id symbol?))
  (if-exp
   (test-exp expression?)
   (true-exp expression?)
   (false-exp expression?))
  (lambda-exp
     (ids (list-of symbol?))
     (body expression?))
  (app-exp
   (rator expression?)
   (rands (list-of expression?)))
  (lex-info
   (id symbol?)
   (depth number?)
   (position number?))
  (free-info
   (id symbol?)))

(define e1 (app-exp (const-exp '+) (list (const-exp 3) (const-exp 3))))
(define e2 (lambda-exp '(a b) (app-exp (const-exp '*) (list (var-exp 'a) (var-exp 'b)))))



(define unparse-expression
  (lambda (exp)
    (cases expression exp
      (const-exp (c) c)
      (lit-exp (datum) datum)
      (var-exp (id) id)
      (if-exp (test-exp true-exp false-exp)
              (append '(if) (list
                         (unparse-expression test-exp)
                         (unparse-expression true-exp)
                         (unparse-expression false-exp))))
      (lambda-exp (ids body)
                  (list 'lambda ids (unparse-expression body)))
      (app-exp (rator rands)
               (define unparse-rands
                 (lambda (rnds)
                   (cond ((null? rnds) '())
                         (else (cons (unparse-expression (car rnds)) (unparse-rands (cdr rnds)))))))
               (cons (unparse-expression rator) (unparse-rands rands)))
      (lex-info (id depth position)
                (list id ': depth position))
      (free-info (id)
                 (list id 'free)))))


(define parse-expression
  (lambda (datum)
    (cond ((eqv? datum '+) (const-exp '+))
          ((eqv? datum '*) (const-exp '*))
          ((eqv? datum 3) (const-exp 3))
          ((number? datum) (lit-exp datum))
          ((symbol? datum) (var-exp datum))
          ((list? datum)
           (cond ((eqv? (car datum) 'if)
                  (if-exp
                   (parse-expression (cadr datum))
                   (parse-expression (caddr datum))
                   (parse-expression (caddr datum))))
                 ((eqv? (car datum) 'lambda)
                  (lambda-exp
                   (cadr datum) (parse-expression (caddr datum))))
                 (else
                  (define parse-rands
                    (lambda (rnds)
                      (cond ((null? rnds) '())
                            (else (cons (parse-expression (car rnds))
                                        (parse-rands (cdr rnds)))))))
                  (app-exp (parse-expression (car datum))
                           (parse-rands (cdr datum))))))   
          (else (eopl:error 'parse-expression "Invalid concrete syntax ~s" datum)))))

#|
Modify subst-exp to prevent capturing by binding occurrence of variable.
|#

(define fresh-id
  (lambda (exp s)
    (let ((syms (all-ids exp)))
      (letrec
          ((loop (lambda (n)
                   (let ((sym (string->symbol
                               (string-append s
                                              (number->string n)))))
                     (if (memv sym syms) (loop (+ n 1)) sym)))))
        (loop 0)))))


(define all-ids
  (lambda (exp)
    (cases expression exp
      (const-exp (c) (list (const-exp c)))
      (lit-exp (datum) (list datum))
      (var-exp (id) (list id))
      (if-exp (test-exp true-exp false-exp)
              (list
               (all-ids test-exp)
               (all-ids true-exp)
               (all-ids false-exp)))
      (lambda-exp (ids body)
                  (append ids (all-ids body)))
      (app-exp (rator rands)
               (append (all-ids rator)
                       (letrec ((aux (lambda (rnds)
                                       (cond ((null? rnds) '())
                                             (else (append (all-ids (car rnds))
                                                           (aux (cdr rnds))))))))
                         (aux rands))))
      (lex-info (id depth position) '())
      (free-info (id) (list id)))))


(define e3 (lambda-exp (list 'w2) (app-exp (const-exp '+) (list (var-exp 'w1) (var-exp 'w2)))))
(define e4 (app-exp e3 (list (var-exp 'w3))))


;; NOTE:
;> (car '((var-exp w3)))
;(var-exp w3)
;
;  BUT!
;
;> (car (list (var-exp 'w3)))
;#(struct:var-exp w3)
;
; What is the difference?
;
; CHECK FOR THIS BUG
#|

This version does not prevent capturing of variables yet....

|#

(define lambda-calculus-subst
  (lambda (exp subst-exp subst-id)
    (letrec
        ((subst
          (lambda (exp)
            (cases expression exp
              (const-exp (c)
                         (const-exp c))
              (lit-exp (datum)
                       (lit-exp datum))
              (var-exp (id)
                       (if (eqv? id subst-id) subst-exp exp))
              (if-exp (test-exp true-exp false-exp)
                      (if-exp (subst test-exp)
                              (subst true-exp)
                              (subst false-exp)))
              (lambda-exp (id body)
                          (lambda-exp id (subst body)))
              (app-exp (rator rands)
                       (letrec
                           ((subst-rands
                            (lambda (rands)
                              (cond ((null? rands) '())
                                    (else (cons (subst (car rands))
                                                (subst-rands (cdr rands))))))))
                         (app-exp (subst rator) (subst-rands rands))))
              (lex-info (id depth position)
                        (lex-info id depth position))
              (free-info (id)
                         (free-info id)))
            )))
      (subst exp))))


;; helper function that will 
