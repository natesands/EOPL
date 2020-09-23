#lang eopl


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


;; parse and un-parse
;; (note parse will not take strings with lexical-depth-info)

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




