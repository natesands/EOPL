#lang eopl


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
     (ids list-of-symbols?)
     (body expression?))
  (app-exp
   (rator expression?)
   (rands list-of-expressions?))
  (lex-info
   (id symbol?)
   (depth number?)
   (position number?))
  (free-info
   (id symbol?)))

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
                 (cons (unparse-expression rator) (unparse-rands rands))))
      (lex-info (id depth position)
                (list id ': depth position))
      (free-info (id)
                 (list id 'free)))))



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

