#lang eopl

(define-datatype expression expression?
  (var-exp
   (id symbol?))
  (lambda-exp
   (id symbol?)
   (body expression?))
  (app-exp
   (rator expression?)
   (rand expression?))
  (lex-info
   (id symbol?)
   (depth number?)
   (position number?))
  (free-info
   (id symbol?)))


(define occurs-free?
  (lambda (var exp)
    (cases expression exp
      (var-exp (id) (eqv? id var))
      (lambda-exp (id body)
                  (and (not (eqv? id var))
                       (occurs-free? var body)))
      (app-exp (rator rand)
               (or (occurs-free? var rator)
                    (occurs-free? var rand)))
      (lex-info (id depth position)
                (eqv? id var))
      (free-info (id)
                 (eqv? id var)))))

(define unparse-expression
  (lambda (exp)
    (cases expression exp
      (var-exp (id) id)
      (lambda-exp (id body)
                  (list 'lambda (list id)
                        (unparse-expression body)))
      (app-exp (rator rand)
               (list (unparse-expression rator)
                     (unparse-expression rand)))
      (lex-info (id depth position)
                (list id ': depth position))
      (free-info (id)
                 (list id 'free)))))




(define parse-expression
  (lambda (datum)
    (cond
      ((symbol? datum) (var-exp datum))
      ((pair? datum)
       (if (eqv? (car datum) 'lambda)
           (lambda-exp (caadr datum)
                       (parse-expression (caddr datum)))
           (app-exp
            (parse-expression (car datum))
            (parse-expression (cadr datum)))))
      (else (eopl:error 'parse-expression
                   "Invalid concrete syntax ~s" datum)))))


(define lexical-address
  (lambda (exp)
    (define aux
      (lambda (orig-exp lambda-depth exp bound-var)
        (cases expression exp
          (var-exp (id)
                   (cond ((occurs-free? id orig-exp)
                          (free-info id))
                         ((eqv? id bound-var)
                          (lex-info id 0 0))
                         (else (lex-info id lambda-depth 0))))
          (lambda-exp (id body)
                      (lambda-exp id (aux orig-exp (+ 1 lambda-depth) body id)))
          (app-exp (rator rand)
                   (app-exp (aux orig-exp lambda-depth rator bound-var)
                            (aux orig-exp lambda-depth rand bound-var)))
          (lex-info (id depth position)
                    (lex-info id depth position))
          (free-info (id)
                     (free-info (id))))))
    (define get-bound-var
      (lambda (exp)
        (cases expression exp
          (var-exp (id) id)
          (lambda-exp (id body) id)
          (app-exp (rator rand)
                   (get-bound-var rator))
          (lex-info (id depth position)
                    id)
          (free-info (id) id))))
    (aux exp -1 exp (get-bound-var exp))))



;; e.g ((lambda (a) (a b)) c)

(define lexp-1
  (let ((rtr (lambda-exp 'a (app-exp (var-exp 'a) (var-exp 'b))))
        (rnd (var-exp 'c)))
    (app-exp rtr rnd)))

(define lexp-2
  (parse-expression '(lambda (a) ((lambda (x) (f a)) c) x) ))

(define lexp-3
  (parse-expression '(lambda (a) (lambda (b) ((lambda (x) (f a)) (f b))))))
; (lambda (a) (lambda (b) ((lambda (x) (f a)) (f b))))

; (lambda (a) (lambda (b) ((lambda (x) ((f free) (a : 2 0))) ((f free) (b : 0 0)))))