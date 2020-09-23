#lang eopl
#| Exercise 2.11

<expression> := <number>
             := <symbol>
             := (<prim> {<expression>}*)
             := (if <expression> <expression> <expression>)
             := (lambda ({<identifier>}*) <expression>)
             := (<expression> {<expression>}*)

|#

(define-datatype expression expression?
  (lit-exp
   (datum number?))
  (var-exp
   (id symbol?))
  (primapp-exp
   (prim primative?)
   (rands (list-of expression?)))
  (if-exp
   (test-exp expression?)
   (true-exp expression?)
   (false-exp expression?))
  (lambda-exp
   (ids (list-of symbol?))
   (body expression?))
  (app-exp
   (rator expression?)
   (rands (list-of expression?))))

(define-datatype primative primative?
  (+-prim)
  (*-prim))

(define unparse-expression
  (lambda (exp)
    (cases expression exp
      (lit-exp (datum) datum)
      (var-exp (id) id)
      (primapp-exp (prim rands)
                   (cases primative prim
                     (+-prim () (cons '+ (map unparse-expression rands)))
                     (*-prim () (cons '* (map unparse-expression rands)))))
      (if-exp (test-exp true-exp false-exp)
              (list 'if
                    (unparse-expression test-exp)
                    (unparse-expression true-exp)
                    (unparse-expression false-exp)))
      (lambda-exp (ids body)
                  (list 'lambda ids (unparse-expression body)))
      (app-exp
       (rator rands)
       (cons (unparse-expression rator)
             (map unparse-expression rands))))))

(define exp0
  (primapp-exp (*-prim) (list (var-exp 'a) (var-exp 'b)))) ;  (* a b)

(define exp1
 (lambda-exp '(x) (var-exp 'x)))   ; (lambda (x) x)

(define exp2
  (lambda-exp '(x y) (primapp-exp (*-prim) (list (var-exp 'x) (var-exp 'y)))))   ;  (lambda (x y) (* x y))

(define exp3
  (lambda-exp '(a b) (app-exp (var-exp 'cons) (list (var-exp 'a) (var-exp 'b)))))   ; (lambda (a b) (cons a b))




(define parse-expression
  (lambda (exp)
    (cond ((number? exp) (lit-exp exp))
          ((symbol? exp) (var-exp exp))
          ((pair? exp)
           (cond ((eq? (car exp) '*)
                  (primapp-exp (*-prim) (map parse-expression (cdr exp))))
                 ((eq? (car exp) '+)
                  (primapp-exp (+-prim) (map parse-expression (cdr exp))))
                 ((eq? (car exp) 'if)
                  (if-exp
                   (parse-expression (cadr exp))
                   (parse-expression (caddr exp))
                   (parse-expression (cadddr exp))))
                 ((eq? (car exp) 'lambda)
                  (lambda-exp
                   (cadr exp)
                   (parse-expression (caddr exp))))
                 (else
                  (app-exp
                   (parse-expression (car exp))
                   (map parse-expression (cdr exp))))))
           (else ((eopl:error 'parse-expression "Invalid concrete syntax ~s" exp))))))

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
      (primapp-exp (prim rands)
                   (map all-ids rands))
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
      )))

(define exp4 (parse-expression '((lambda (w2) (w1 w0)) w3)))


                  

        


