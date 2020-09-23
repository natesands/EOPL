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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define (check x)
  (unparse-expression (parse-expression x)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
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
      (lit-exp (datum) '())
      (var-exp (id) (list id))
      (primapp-exp (prim rands)
                   (cases primative prim
                     (*-prim () (union-list-of-sets (map all-ids rands)))
                     (+-prim () (union-list-of-sets (map all-ids rands)))))
      (if-exp (test-exp true-exp false-exp)
              (union-list-of-sets (map all-ids (list test-exp true-exp false-exp))))
      (lambda-exp (ids body)
                  (union-set ids (all-ids body)))
      (app-exp (rator rands)
               (union-set (all-ids rator) (union-list-of-sets (map all-ids rands)))))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; SET FUNCTIONS a la Prof. Troeger

;; We require sets to be flat lists with no repeating elements

(define element-of?
  (lambda (element set)
    (cond ((null? set) #f)
          ((eq? (car set) element) #t)
          (else (element-of? element (cdr set))))))

(define union-set
  (lambda (set1 set2)
    (cond ((null? set1) set2)
          ((element-of? (car set1) set2)
           (union-set (cdr set1) set2))
          (else (cons (car set1)
                      (union-set (cdr set1) set2))))))

(define union-list-of-sets
  (lambda (list-of-sets)
    (cond ((null? list-of-sets) '())
          (else (union-set (car list-of-sets) (union-list-of-sets (cdr list-of-sets)))))))

(define intersection
  (lambda (s1 s2)
    (cond ((null? s1) '())
          ((element-of? (car s1) s2)
           (cons (car s1) (intersection (cdr s1) s2)))
          (else (intersection (cdr s1) s2)))))
  

(define difference
 (lambda (set1 set2)
   (cond ((null? set1) '())
         ((element-of? (car set1) set2)
          (difference (cdr set1) set2))
         (else (cons (car set1)
                     (difference (cdr set1) set2))))))

(define replace-elem
  (lambda (set elem subst-elem)
    (cond ((null? set) '())
          ((eq? (car set) elem)
           (cons subst-elem (cdr set)))
          (else (cons (car set) (replace-elem (cdr set) elem subst-elem))))))


(define los (list '(a b c) '(b g f) '(a d r)))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; returns set of free variables in expression

(define free-vars
  (lambda (exp)
    (cases expression exp
      (lit-exp (datum) '())
      (var-exp (id) (list id))
      (primapp-exp (prim rands)
                   (cases primative prim
                     (+-prim () (union-list-of-sets (map free-vars rands)))
                     (*-prim () (union-list-of-sets (map free-vars rands)))))
      (if-exp (test-exp true-exp false-exp)
              (union-list-of-sets (list (free-vars test-exp)
                                        (free-vars true-exp)
                                        (free-vars false-exp))))
      (lambda-exp (ids body)
                  (difference (free-vars body) ids))
      (app-exp (rator rands)
               (union-set (free-vars rator)
                      (union-list-of-sets (map free-vars rands)))))))

(define bound-vars
  (lambda (exp)
    (cases expression exp
      (lit-exp (datum) '())
      (var-exp (id) '())
      (primapp-exp (prim rands) '())
      (if-exp (test-exp true-exp false-exp)
              (union-list-of-sets (list (bound-vars test-exp)
                                        (bound-vars true-exp)
                                        (bound-vars false-exp))))
      (lambda-exp (ids body)
                  (union-set
                   (intersection (free-vars body) ids)
                   (bound-vars body)))
      (app-exp (rator rands)
               (union-set (bound-vars rator)
                          (union-list-of-sets (map bound-vars rands)))))))
    
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ids
  (lambda (lambda-expression)
    (cadr (unparse-expression lambda-expression))))

(define body
  (lambda (lambda-expression)
    (parse-expression (caddr (unparse-expression lambda-expression)))))


(define alpha-convert
  (lambda (id lambda-expression)
    (let ((fresh (fresh-id lambda-expression (symbol->string id))))
     (lambda-exp (replace-elem (ids lambda-expression) id fresh)
                 (subst-var (body lambda-expression) id fresh)))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; test expressions

(define exp0
  (primapp-exp (*-prim) (list (var-exp 'a) (var-exp 'b)))) ;  (* a b)

(define exp1
 (lambda-exp '(x) (var-exp 'x)))   ; (lambda (x) x)

(define exp2
  (lambda-exp '(x y) (primapp-exp (*-prim) (list (var-exp 'x) (var-exp 'y)))))   ;  (lambda (x y) (* x y))

(define exp3
  (lambda-exp '(a b) (app-exp (var-exp 'cons) (list (var-exp 'a) (var-exp 'b)))))   ; (lambda (a b) (cons a b))

(define exp4 (parse-expression '((lambda (w2) (w1 w0)) w3)))

(define exp5 (parse-expression '(lambda (p) (if q r s))))

(define exp6 (parse-expression '(lambda (p) (+ p x))))

(define exp7 (parse-expression '(lambda (x) ((lambda (x) (+ x 1)) x))))
    
    
    