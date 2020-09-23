#lang eopl

#|

Problems 2.6 - 2.13
Problems 2.14 - 2.17

|#

;; lambda expressions

;(define-datatype expression expression?
;  (var-exp
;   (id symbol?))
;  (lambda-exp
;   (id symbol?)
;   (body expression?))
;  (app-exp
;   (rator expression?)
;   (rand expression?)))

;; ex. 2.6
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

;; occurs-free? using abstract syntax tree

;(define occurs-free?
;  (lambda (var exp)
;    (cases expression exp
;      (var-exp (id) (eqv? id var))
;      (lambda-exp (id body)
;                  (and (not (eqv? id var))
;                       (occurs-free? var body)))
;      (app-exp (rator rand)
;               (or (occurs-free? var rator)
;                    (occurs-free? var rand))))))

;; convert abstract syntax tree back to a list-and-symbol representation

;(define unparse-expression
;  (lambda (exp)
;    (cases expression exp
;      (var-exp (id) id)
;      (lambda-exp (id body)
;                  (list 'lambda (list id)
;                        (unparse-expression body)))
;      (app-exp (rator rand)
;               (list (unparse-expression rator)
;                     (unparse-expression rand))))))

;; e.g ((lambda (a) (a b)) c)
;
;(define lexp-1
;  (let ((rtr (lambda-exp 'a (app-exp (var-exp 'a) (var-exp 'b))))
;        (rnd (var-exp 'c)))
;    (app-exp rtr rnd)))
; > (unparse-expression lexp-1)
; ((lambda (a) (a b)) c)


;(define parse-expression
;  (lambda (datum)
;    (cond
;      ((symbol? datum) (var-exp datum))
;      ((pair? datum)
;       (if (eqv? (car datum) 'lambda)
;           (lambda-exp (caadr datum)
;                       (parse-expression (caddr datum)))
;           (app-exp
;            (parse-expression (car datum))
;            (parse-expression (cadr datum)))))
;      (else (eopl:error 'parse-expression
;                   "Invalid concrete syntax ~s" datum)))))


;; ex. 2.7
#| Define the datatype for the following grammar:

<expression> := <number>
             := <var-exp>
             := (if <expression> <expression> <expression>)
             := (lambda ({<identifier>}*) <expression>)
             := (<expression> {<expression>}*)
|#

(define list-of-symbols?
  (lambda (lst)
    (cond ((null? lst) #t)
          (else
           (and (symbol? (car lst))
                (list-of-symbols? (cdr lst)))))))

(define list-of-expressions?
  (lambda (lst)
    (cond ((null? lst) #t)
          (else
           (and (expression? (car lst))
                (list-of-expressions? (cdr lst)))))))
    

(define-datatype expression expression?
  (lit-exp
   (datum number?))
  (var-exp
   (id symbol?))
  (if-exp
   (test-exp expression?) (true-exp expression?) (false-exp expression?))
  (lambda-exp
     (ids list-of-symbols?) (body expression?))
  (app-exp
   (rator expression?) (rands list-of-expressions?)))

;; define parse and unparse procedures for this grammar

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
               (letrec ((unparse-rands (lambda (rnds)
                                         (cond ((null? rnds) '())
                                               (else
                                                (cons (unparse-expression (car rnds)) (unparse-rands (cdr rnds))))))))
                 (cons (unparse-expression rator) (unparse-rands rands)))))))

;; test expressions

(define app-exp-1
  (app-exp (var-exp 'f) (list (var-exp 'a) (var-exp 'b))))    ;; (f a b)

(define lambda-exp-1
  (lambda-exp '(a b) app-exp-1))     ;; (lambda (a b) (f a b))

(define if-exp-1
  (if-exp (app-exp lambda-exp-1 (list (var-exp 'x) (var-exp  'y))) (var-exp 'd) (lit-exp 1))) ;; (if ((lambda (a b) (f a b)) x y) d 1)

(define parse-expression
  (lambda (datum)
    (cond ((number? datum) (lit-exp datum))
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
                  (letrec ((aux (lambda (sublist)
                                  (cond ((null? sublist) '())
                                        (else (cons (parse-expression (car sublist))
                                                    (aux (cdr sublist))))))))
                    (app-exp (parse-expression (car datum)) (aux (cdr datum)))))))
          (else (eopl:error 'parse-expression "Invalid concrete syntax ~s" datum)))))

;; tests...
;> (parse-expression '(f a b))
;#(struct:app-exp #(struct:var-exp f) (#(struct:var-exp a) #(struct:var-exp b)))
;> (unparse-expression (parse-expression '(f a b)))
;(f a b)
;> (parse-expression '(lambda (a b) c))
;#(struct:lambda-exp (a b) #(struct:var-exp c))
;> (parse-expression '(lambda (a b ) (f a b)))
;#(struct:lambda-exp (a b) #(struct:app-exp #(struct:var-exp f) (#(struct:var-exp a) #(struct:var-exp b))))
;> (parse-expression '(if ((lambda (a b) (f a b)) x y) d 1))
;#(struct:if-exp
;  #(struct:app-exp
;    #(struct:lambda-exp (a b) #(struct:app-exp #(struct:var-exp f) (#(struct:var-exp a) #(struct:var-exp b))))
;    (#(struct:var-exp x) #(struct:var-exp y)))
;  #(struct:var-exp d)
;  #(struct:var-exp d))

;; implement lexical-address 

;; NOTES

#|
Bound and Free Variables in Lambda Calculus Expressions
-------------------------------------------------------

A variable x occurs free in a λ calculus expression E iff

1.  E is a variable reference and E is the same as x;
2.  E is of the form (lambda (y) E') where y is different from x and x occurs
    free in E'
3.  E is of the form (E_1 E_2) and x occurse free in E_1 or E_2.

A variable x occurs bound in a lambda expression E iff

1.  E is of the form (lambda (y) E') where x occurs bound in E' or x and y
    are the same variable and y occurs free in E'
2.  E is of the form (E_1 E_2) and x occurse bound in E_1 or E_2.


|#



;The declaration of a variable v has a scope that includes all references to v that occur free
;in the region associated with the declaration. Those references to v that occur bound in the
;region associated with its declaration are shadowed by inner declarations.

(lex-info
(id symbol?) (depth number?) (position number?))
(free-info
(id symbol?))
