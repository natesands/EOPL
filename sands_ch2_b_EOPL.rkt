#lang eopl

#|
EOPL Chapter 2
Nate Sands
17 June 2020

|#

;; 2.6
;; draw the abstract syntax tree for the lambda calculus expression
;; ((lambda (a) (a b)) c)
#|
                                               
                         ((lambda (a) (a b)) c)
                                               
                                               
                         +------------+        
                         |   app-exp  |        
                         +------------+        
                               / \             
                              /   \            
                    rator    /     \   rand    
                            /       \          
                           /         \         
                          /           -        
                         /         +---------+ 
                        /          | var-exp | 
                       /           +---------+ 
                      /                 |      
                     -                  | id   
              +-----------+             |      
              | lambda-exp|             c      
              +-----/-----+                    
                   /  \                        
                  /    \                       
           +---------+  \                      
           | var-exp |   \                     
           +---------+    \  body           
              /            \                   
         id  /              \                  
            /                \                 
           a             +---------+           
                         | app-exp |           
                         +----\----+           
                             / \               
                      rator /   \ rand         
                           /     \             
                          /       \            
                    +--------+   +--------+    
                    | var-exp|   |var-exp |    
                    +--------+   +--------+    
                         |           |         
                     id  |           | id      
                         |           |         
                         a           b         



|#

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


#| Exercise 2.7

Define the datatype for the following grammar:

<expression> := <number>
             := <var-exp>
             := (if <expression> <expression> <expression>)
             := (lambda ({<identifier>}*) <expression>)
             := (<expression> {<expression>}*)

Implement parse-expression, unparse-expression and lexical-address
|#

(define-datatype expression expression?
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


(define unparse-expression
  (lambda (exp)
    (cases expression exp
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

(define test-exp-1
  (lambda-exp '(a b) (app-exp (var-exp 'cons) (list (var-exp 'a) (var-exp 'b)))))

(define test-exp-2
  (lambda-exp '(a b) (app-exp (var-exp 'cons) (list (var-exp 'c)))))


(define parse-expression
  (lambda (datum)
    (cond ((number? datum) (lit-exp datum))
          ((symbol? datum) (var-exp datum))
          ((list? datum)
           (cond ((eqv? (car datum) 'if)
                  (if-exp
                   (parse-expression (cadr datum))
                   (parse-expression (caddr datum))
                   (parse-expression (cadddr datum))))
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

 
 
(define lexical-address
  (lambda (exp)
    (define aux
      (lambda (exp bound-vars-stack)
        (cases expression exp
          (lit-exp (datum) (lit-exp datum))
          (var-exp (id)
                   (cond ((free? id bound-vars-stack)
                          (free-info id))
                         (else (get-lex-info id bound-vars-stack))))
          (if-exp (test-exp true-exp false-exp)
                  (if-exp
                   (lexical-address (test-exp))
                   (lexical-address (true-exp))
                   (lexical-address (false-exp))))
          (lambda-exp (ids body)
                      (lambda-exp
                       ids
                       (aux body (cons ids bound-vars-stack))))
          (app-exp (rator rands)
                   (app-exp
                    (aux rator bound-vars-stack)
                    (letrec ((lex-add-lst-exp
                              (lambda (lst-of-exp bound-vars)
                                      (cond ((null? lst-of-exp) '())
                                            (else
                                             (cons (aux (car lst-of-exp) bound-vars)
                                                   (lex-add-lst-exp (cdr lst-of-exp) bound-vars)))))))
                      (lex-add-lst-exp rands bound-vars-stack))))
          (lex-info (id depth position)
                    (lex-info id depth position))
          (free-info (id)
                     (free-info id)))))
    (aux exp '())))
                                     
(define test
    (lambda (x y)
      (define aux
        (lambda (a b c)
          (+ a b c)))
      (aux x y 3)))
           
          
(define free?
  (lambda (var bound-vars-stack)
    (cond ((null? bound-vars-stack) #t)
          (else (and (not (member? var (car bound-vars-stack)))
                          (free? var (cdr bound-vars-stack)))))))



;; pre: id occurs in at least one
;; element of bound-vars-stack
(define get-lex-info
  (lambda (id bound-vars-stack)
    (define aux
      (lambda (id vars depth)
        (cond ((null? vars)
               (eopl:error 'bound-vars-stack "element ~s not found" id))
              ((member? id (car vars))
               (letrec ((find-pos (lambda (id var-lst pos)
                                    (cond ((eq? (car var-lst) id)
                                           (lex-info id depth pos))
                                          (else (find-pos id (cdr var-lst) (+ 1 pos)))))))
                 (find-pos id (car vars) 0)))
              (else (aux id (cdr vars) (+ 1 depth))))))
      (aux id bound-vars-stack 0)))
                         
(define member?
  (lambda (elem lst)
    (cond ((null? lst) #f)
          (else
           (or (eq? (car lst) elem)
               (member elem (cdr lst)))))))

;; reads string, parses, gets lexical adresses, unparses

(define print-lex-address
  (lambda (string)
    (unparse-expression
     (lexical-address
      (parse-expression string)))))

;; test expressions

(define exp-1 '(lambda (x) (f (f x))))
;; (lambda (x) ((f free) ((f free) (x : 0 0))))

(define exp-2 '(lambda (x)
                 (lambda (y)
                   ((lambda (x)
                      (f (x)))
                    x))))
;; (lambda (x) (lambda (y) ((lambda (x) ((f free) ((x : 0 0)))) (x : 1 0))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

#| Exercise 1.19

 Write a procedure free-vars that takes a list structure representing an expression
 in the lambda calculus syntax given above and returns a set (a list without duplicates)
 of all the variables that occur free in the expression. Similarly, write a procedure
 bound-vars that returns a set of all the variables that occur bound in its argument.

 <expression> := <identifier>
              := (lambda (<identifier>) <expression>)
              := (<expression> <expression>)
|#

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


#| Exercise 2.8

Rewrite the solution to exercise 1.19 using abstract syntax.
Then compare this version to the original solution.
|#

;; input a expression in list form, parse, convert to lexical address form,
;; read variables off free-info constructor

(define free-vars-2
  (lambda (exp)
    (cases expression exp
      (lit-exp (datum) '())
      (var-exp (id) '())
      (if-exp (test-exp true-exp false-exp)
              (append (free-vars-2 test-exp)
                      (free-vars-2 true-exp)
                      (free-vars-2 false-exp)))
      (lambda-exp (ids body)
                  (free-vars-2 body))
      (app-exp (rator rands)
               (append (free-vars-2 rator)
                       (letrec ((aux (lambda (rnds)
                                       (cond ((null? rnds)
                                              '())
                                             (else (append (free-vars-2 (car rnds))
                                                           (aux (cdr rnds))))))))
                         (aux rands))))
      (lex-info (id depth position) '())
      (free-info (id) (list id)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

#| Exercise 2.9

Make parse-expression non-fragile

|#

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

#| Exercise 2.10

Define the function all-ids which returns a list of all symbols in an expression.

fresh-id uses all-ids to produce the next available id e.g.
if exp contains w1,w2,w3,w4 then fresh-id returns w5

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
      

(define exp-3 '((lambda (w2) (w1 w0)) w3))
;
;> (all-ids (parse-expression exp-3))
;(w2 w1 w0 w3)
;> (fresh-id (parse-expression exp-3) "w")
;w4

 



