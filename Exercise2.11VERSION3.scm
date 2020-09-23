
#lang eopl


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; EOPL Second Edition Exercises 2.11 and 2.12
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; DRAFT SOLUTION V 3.0
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; STATUS: seems to be working. and to yield to a proof by structural induction
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; D. Troeger
;; July 1 2020




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; auxiliary code for free-vars from my solution to Exercise 1.19
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; sets are represented here as lists without repetition

(define (remove-element-from-set element set)
  (cond ((null? set) set)
	((eq? (car set) element) (cdr set))
	(else (cons (car set) (remove-element-from-set element (cdr set))))))

(define (remove-elements-from-set elements set)
  (cond ((or (null? elements) (null? set)) set)
	(else (remove-elements-from-set (cdr elements)
					(remove-element-from-set
					 (car elements)
					 set)))))

(define (element-of? element set)
  (cond ((null? set) #f)
	((eq? element (car set)) #t)
	(else (element-of? element (cdr set)))))

(define (union-set set1 set2)
  (cond ((null? set1) set2)
	((element-of? (car set1) set2)
	 (union-set (cdr set1) set2))
	(else (cons (car set1) (union-set (cdr set1) set2)))))

(define (union-list-of-sets list-of-sets)
  (cond ((null? list-of-sets) '())
        (else (union-set (car list-of-sets) (union-list-of-sets (cdr list-of-sets))))))


(define (intersect-set set1 set2)
  (cond ((null? set1) '())
        ((element-of? (car set1) set2) (cons (car set1) (intersect-set (cdr set1) set2)))
        (else (intersect-set (cdr set1) set2))))


(define difference
  (lambda (set1 set2)
    (cond
      ((null? set1) '())
      ((memv (car set1) set2)
       (difference (cdr set1) set2))
      (else (cons (car set1) (difference (cdr set1) set2))))))

(define (equal-sets? set1 set2)
  (and (null? (difference set1 set2))
       (null? (difference set2 set1))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; First: extend parse-expression and unparse-expression to allow the constants 3, * and +
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-datatype expression expression?
    (lit-exp
     (datum number?))
    (var-exp
     (id symbol?))
    (primapp-exp
     (prim primitive?)
     (rands (list-of expression?)))
    (if-exp 
     (test-exp expression?)
     (true-exp expression?)
     (false-exp expression?))
    (lambda-exp 
     (ids  (list-of symbol?))  ;; I retain ids as a list of symbols.  So when lambda is
                               ;; restricted (below) to a single parameter, I am working with
                               ;; a singleton list.   This in anticipation of generalizing
                               ;; the substitution function at a later point. 
     (body expression?))
    (app-exp
     (app-rator expression?)
     (app-rands (list-of expression?))))              
  
(define-datatype primitive primitive?
    (add-prim)
    (mult-prim))

(define parse-expression
  (lambda (datum)
    (cond ((number? datum) (lit-exp datum))
          ((symbol? datum) (var-exp datum))
          ((pair? datum)
           (cond ((eq? (car datum) '+)
                  (primapp-exp (add-prim) 
                               (map parse-expression (cdr datum))))                           
                 ((eq? (car datum) '*)
                  (primapp-exp (mult-prim)
                               (map parse-expression (cdr datum))))
                 ((eq? (car datum) 'if)
                  (if-exp (parse-expression (cadr datum))
                          (parse-expression (caddr datum))
                          (parse-expression (cadddr datum))))
                 
                 ((eq? (car datum) 'lambda)
                  (lambda-exp
                   (cadr datum)
                   (parse-expression (caddr datum))))
                 
                 (else 
                  (app-exp
                   (parse-expression (car datum))
                   (map parse-expression (cdr datum))))))
          )))


(define (unparse-expression exp)
  (cases expression exp
    (lit-exp (lit) lit)
    (var-exp (id) id)
    (primapp-exp (prim rands)
      (cases primitive prim
        (add-prim () (cons '+ (map unparse-expression rands)))
        (mult-prim () (cons '* (map unparse-expression rands)))))
    (app-exp (app-rator app-rands)
        (cons (unparse-expression app-rator)
              (map unparse-expression app-rands)))
    (if-exp (test-exp true-exp false-exp)
        (list 'if (unparse-expression test-exp)
                  (unparse-expression true-exp)
                  (unparse-expression false-exp)))
    (lambda-exp (ids body)
        (list 'lambda ids (unparse-expression body)))
    
    ))


(define (check x)
  (unparse-expression (parse-expression x)))

; if everything is working correctly, we should have

;   (equal? (check x) x) 

; whenever x is legal concrete syntax


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Second Part:  adjust all-ids and fresh-id to take account of the extended language
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; the function lambda-calculus-subst given in the text is designed for the restricted language
;; in which there is just one formal parameter for each lambda form.  So the language they
;; want is both an extension, and a restriction, of the language used in Exercise 2.10

;; setting up for alpha-variation of multi-parameter lambdas could be done iteratively --
;; would need to consider the possibility of multiple captures.  This is NOT attempted here. 

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(define (free-vars exp)   ;; exp is an expression; returns a list of symbols
  (cases expression exp
    (lit-exp (datum) '())
    
    (var-exp (id) (list id))

    (primapp-exp (prim rands)
                 (cases primitive prim
                   (add-prim () (union-list-of-sets (map free-vars rands)))
                   (mult-prim () (union-list-of-sets (map free-vars rands)))))

    (if-exp (test-exp true-exp false-exp)
        (union-set (free-vars test-exp)
                   (union-set (free-vars true-exp) (free-vars false-exp))))
    
    (lambda-exp (ids body)
        (difference (free-vars body) ids))  ; remember that ids is a list 
    
    (app-exp (rator rands)
        (union-set (free-vars rator) (union-list-of-sets (map free-vars rands))))
    
    (else (eopl:error 'free-vars "Concrete syntax does not match grammar:~s" exp))))


(define (bound-vars exp)  ;; exp is an expression, and bound-vars returns a list of symbols
  (cases expression exp
    (lit-exp (datum) '())
    
    (var-exp (id) '())

    (primapp-exp (prim rands)
                 (cases primitive prim
                   (add-prim () (union-list-of-sets (map bound-vars rands)))
                   (mult-prim () (union-list-of-sets (map bound-vars rands)))))


    (if-exp (test-exp true-exp false-exp)
        (union-set (bound-vars test-exp)
                   (union-set (bound-vars true-exp) (bound-vars false-exp))))
    
    (lambda-exp (ids body)
        (union-set (bound-vars body) (intersect-set ids (free-vars body))))  ; again, ids is a list
    
    (app-exp (rator rands)
        (union-set (bound-vars rator) (union-list-of-sets (map bound-vars rands))))

    (else (eopl:error 'bound-vars "Concrete syntax does not match grammar:~s" exp))))



(define (bound-vars-and-lambda-vars-for-which-there-are-no-bound-occurrences exp)
  (cases expression exp
    (lit-exp (datum) '())
    
    (var-exp (id) '())

    (primapp-exp (prim rands)
                 (cases primitive prim
                   (add-prim () (union-list-of-sets (map bound-vars-and-lambda-vars-for-which-there-are-no-bound-occurrences rands)))
                   (mult-prim () (union-list-of-sets (map bound-vars-and-lambda-vars-for-which-there-are-no-bound-occurrences rands)))))


    (if-exp (test-exp true-exp false-exp)
        (union-set (bound-vars-and-lambda-vars-for-which-there-are-no-bound-occurrences test-exp)
                   (union-set (bound-vars-and-lambda-vars-for-which-there-are-no-bound-occurrences true-exp)
                              (bound-vars-and-lambda-vars-for-which-there-are-no-bound-occurrences false-exp))))
    
    (lambda-exp (ids body)
        (union-set (bound-vars-and-lambda-vars-for-which-there-are-no-bound-occurrences body) ids))
    
    (app-exp (rator rands)
        (union-set (bound-vars-and-lambda-vars-for-which-there-are-no-bound-occurrences rator)
                   (union-list-of-sets (map bound-vars-and-lambda-vars-for-which-there-are-no-bound-occurrences rands))))


    (else (eopl:error 'bound-vars-and-lambda-vars-for-which-there-are-no-bound-occurrences "Concrete syntax does not match grammar:~s" exp))))




(define all-ids
  (lambda (exp)
    (union-set (free-vars exp)
               (bound-vars-and-lambda-vars-for-which-there-are-no-bound-occurrences exp))))


(define fresh-id
  (lambda (exp s)
    (let ((syms (all-ids exp)))
      (letrec ((loop (lambda (n)
                       (let ((sym (string->symbol (string-append s (number->string n)))))
                         (if (memv sym syms)
                             (loop (+ n 1))
                             sym)))))
        (loop 0)))))







;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Likely a good idea to test these reworked functions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; (unparse-expression (parse-expression '(lambda (p) (+ p x))))

;; (unparse-expression (parse-expression '(lambda (p) (* p x))))

;; (unparse-expression (parse-expression '(lambda (p) (if q r s))))

;; (unparse-expression (parse-expression '(lambda (p) (+ p 3))))

;; (free-vars '(lambda (p) (+ p x)))

;; (bound-vars '(lambda (p) (+ p x)))

;; (all-ids '(lambda (p) (+ p x)))

;; (all-ids '(lambda (p) (+ x 1)))





;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Third Part:  Some Basic Debugging Utilities
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;; n > 0
(define (newlines n)
  (cond ((= n 1) (newline))
        (else (begin
                (newline)
                (newlines (- n 1))))))


(define (displayList lst)
  (begin
    (newlines 2)
    (for-each (lambda (x)
                (begin
                  (newline)
                  (display x)
                  (newline)))
              lst)
    ))






;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Fourth Part:  fix lambda-calculus-subst, given in the text, so that it performs renaming when necessary
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; the class of expressions is defined by define-datatype, above

;; exp and subst-exp are expressions, given as abstract syntax
;; subst-id is also given as abstract syntax


(define lambda-calculus-subst
  (lambda (exp subst-exp subst-id)

    (let ((free-vars-exp (free-vars exp))                ;; type check: free-vars expects an expression
          (free-vars-subst-exp (free-vars subst-exp)))   ;; and returns a list of symbols

       (cases expression exp
                          (lit-exp (datum) (lit-exp datum))
         
                          (var-exp (id) ;; id is a symbol
                                   (if
                                    
                                    (and (element-of? (unparse-expression subst-id) free-vars-exp)
                                         (equal? (parse-expression id) subst-id))

                                    subst-exp

                                    exp))
                                  
                          (if-exp (test-exp true-exp false-exp)
                                  (if-exp (lambda-calculus-subst test-exp subst-exp subst-id)
                                          (lambda-calculus-subst true-exp subst-exp subst-id)
                                          (lambda-calculus-subst false-exp subst-exp subst-id)))

                           (primapp-exp (prim rands)  ;; rands is a list of expressions
                                        (letrec
                                            ((subst (lambda (e) (lambda-calculus-subst e subst-exp subst-id))))
                                          (primapp-exp prim (map subst rands))))

                            (app-exp (rator rands)
                                     (letrec
                                         ((subst (lambda (e) (lambda-calculus-subst e subst-exp subst-id))))
                                     (app-exp (subst rator) (map subst rands))))

                             (lambda-exp (ids body)
                                         
                                         (cond ((and
                                                 (element-of? (car ids) free-vars-subst-exp) ;; ids is a list of (just one) symbol
                                                 (element-of? (unparse-expression subst-id) free-vars-exp))

                                                (let ((old (car ids))   ;; old is given as concrete syntax
                                                      (fresh (fresh-id exp "x")))  ;; fresh is given as concrete syntax

                                                  (lambda-calculus-subst
                                                   
                                                   ;; modify exp to avoid capturing a free variable in subst-exp,
                                                   ;; and then proceed with the desired substitution
                                                   (lambda-exp
                                                    (list fresh)
                                                    (lambda-calculus-subst body (parse-expression fresh) (parse-expression old)))

                                                   subst-exp
                                                   subst-id)))

                                               ((element-of? (unparse-expression subst-id) free-vars-exp)
                                                (lambda-exp ids (lambda-calculus-subst body subst-exp subst-id)))

                                               (else exp)))
                                               
         ))))
                                            
                  
                                         
         

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Here is a rudimentary test harness
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; inputs are given here in concrete syntax

(define (correct? input-exp subst-exp subst-id hand-computed-concrete-output)
  (let ((abstr-input-exp (parse-expression input-exp))
        (abstr-subst-exp (parse-expression subst-exp))
        (abstr-subst-id (parse-expression subst-id)))
    (let ((abstr-output (lambda-calculus-subst abstr-input-exp abstr-subst-exp abstr-subst-id)))
      (equal? (unparse-expression abstr-output) hand-computed-concrete-output))))
      

;; inputs are given here in concrete syntax

(define (concrete-output input-exp subst-exp subst-id)
 (let ((abstr-input-exp (parse-expression input-exp))
        (abstr-subst-exp (parse-expression subst-exp))
        (abstr-subst-id (parse-expression subst-id)))
   (let ((abstr-output (lambda-calculus-subst abstr-input-exp abstr-subst-exp abstr-subst-id)))
      (unparse-expression abstr-output))))


   
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Here are some tests
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;  


;; (concrete-output '(lambda (x) x) 'y 'x)  gives (lambda (x) x)

;; (concrete-output '(lambda (x) x) '(+ x y) 'x)  gives (lambda (x) x)

;; (concrete-output '(lambda (x) (+ x y)) '(+ x y) 'x) gives (lambda (x) (+ x y))

;; (concrete-output '(lambda (x) (+ x y)) '(+ x y) 'y)  gives (lambda (x0) (+ x0 (+ x y)))

;; (concrete-output '(lambda (x) (+ x y (lambda (x) (* x 3)))) '(* x y) 'y) gives
;;    (lambda (x0) (+ x0 (* x y) (lambda (x) (* x 3))))

;; (concrete-output '(lambda (x) (+ x y (lambda (x) (* x y 3)))) '(* x y) 'y) gives
;;    (lambda (x0) (+ x0 (* x y) (lambda (x0) (* x0 (* x y) 3))))

;; (concrete-output '(lambda (x) (+ x y (lambda (y) (* x (lambda (z) (* x y z)))))) '(+ x y z) 'y)  gives
;;    (lambda (x0) (+ x0 (+ x y z) (lambda (y) (* x0 (lambda (z) (* x0 y z))))))

;; (concrete-output '(lambda (x) (+ x w (lambda (y) (* x w (lambda (z) (+ x y w)))))) '(+ x y z) 'w) gives
;;    (lambda (x0) (+ x0 (+ x y z) (lambda (x1) (* x0 (+ x y z) (lambda (x2) (+ x0 x1 (+ x y z)))))))

;; (concrete-output '(+ (lambda (x) (+ x y)) (lambda (y) (* x y))) 'z 'x) gives 
;;    (+ (lambda (x) (+ x y)) (lambda (y) (* z y)))

;; (concrete-output '((lambda (x) (+ x ((lambda (y) (+ y ((lambda (z) (+ u z)) 3))) 2))) 1) '(* x y z) 'u) 


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; it appears, then, that (lambda-calculus-subst E1 E2 x) computes E1[E2/x] as referred to in Exercise 2.12,
;; with E1, E2 and x all given as abstract syntax. 
;;
;; We can further test lambda-calculus-subst by verifying that it permits ready definition of the operators
;; alpha, beta and eta defined in Exercise 2.12
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; (lambda (y) E) alpha-converts to (lambda (x) E[x/y]), if x is not free in E

;; alpha-convert will input an expression e = (lambda (y) E) -- in abstract syntax -- as well as a variable x (also abstract
;; syntax) which is not free in E, and return (lambda (x) E[x/y])

;; because cases is the only way of extracting the components from abstract syntax, and because cases will
;; reject any other than a complete selection of variants for the given input type, we cannot simply assume that
;; the input has the form (lambda (y) E) --  rather it is necessary to rhttps://opendsa-server.cs.vt.edu/ODSA/Books/eject all other cases.

;; or is this too restrictive a conception of alpha-conversion?  Should it be applied recursively, and not just
;; at the top level?

;; the definition given above suggests not: the body of the new lambda is just the substitution


(define (alpha-convert e x)
  (let ((free-vars-e (free-vars e))
        (unparsed-x (unparse-expression x))
        (error-message "alpha-convert can only be applied to a lambda form"))
    (cases expression e
      (lambda-exp (ids body)
                  (if (not (element-of? unparsed-x (free-vars e)))
                      (lambda-exp (list unparsed-x) (lambda-calculus-subst body x (parse-expression (car ids))))
                      (eopl:error 'alpha-convert "the new variable ~s occurs free in the expression ~s"
                                  unparsed-x (unparse-expression e))))
      (else (eopl:error 'alpha-convert error-message)))))




;; a few tests

;; (unparse-expression (alpha-convert (parse-expression '(lambda (x) x)) (parse-expression 'y)))

;; (unparse-expression (alpha-convert (parse-expression '(lambda (x) x)) (parse-expression 'x)))


;; (unparse-expression (alpha-convert (parse-expression '((lambda (x) ((lambda (y) (+ y x)) w )) z)) (parse-expression 'u)))
;; for an error

;; (unparse-expression (alpha-convert (parse-expression '(lambda (x) ((lambda (y) (+ y x)) w ))) (parse-expression 'u)))


 ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; now let's implement beta-reduction:  ((lambda (x) E1) E2) = E1[E2/x]


(define (beta-reduce exp)
  (let ((unparsed-exp (unparse-expression exp))
        (error-message "wrong form for beta-reduction:  ~s"))
    (cases expression exp
      (app-exp (rator rands)
               (cases expression rator
                 (lambda-exp (ids body)
                             ;; assumes just one operand
                             (lambda-calculus-subst body (car rands) (parse-expression (car ids))))
                 (else (eopl:error 'beta-reduce "rator is not a lambda expression"))))
      (else (eopl:error 'beta-reduce "input is not an application: ~s"  unparsed-exp)))))

                                                                      

;; a few tests

;; (unparse-expression (beta-reduce (parse-expression '((lambda (x) (+ x y)) w))))
  
;; (unparse-expression (beta-reduce (parse-expression '((lambda (x) (+ x y)) (* x w)))))


;; still want to test what happens when inappropriate input is provided


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;; finally, eta-reduction removes an unnecessary lambda:  if x is not free in E, then (lambda (x) (E x)) eta-reduces
;; to E.  The text claims that eta-reduction can be given in terms of sustitution.  Indeed,  given that x is not free
;; in E, ((lambda (x) E) x) beta-reduces to E[x/x] = E.  Not sure why one would do this, however, when a simpler approach
;; is available:  after checking whether the input expression has the right form, simply check whether x is free in
;; E.  If it is, reject the reduction; if not, return E.  I'll go with the latter approach.

(define (eta-reduce exp)
  (let ((unparsed-exp (unparse-expression exp))
        (error-message "wrong form for eta-reduction: ~s"))
    (cases expression exp
      (lambda-exp (ids body)
                  (cases expression body
                    (app-exp (rator rands)
                             (if (element-of? (car ids) (free-vars rator))
                                 (eopl:error 'eta-reduce "free variable violation")
                                 rator))
                    (else (eopl:error 'eta-reduce "lambda body has wrong form: ~s" (unparse-expression body)))))
      (else (eopl:error 'eta-reduce error-message unparsed-exp)))))


;; a few tests

;; (unparse-expression (eta-reduce (parse-expression '(lambda (x) ((lambda (y) (+ 2 y)) x))  )))

;; (unparse-expression (eta-reduce (parse-expression '(lambda (x) ((lambda (y) (+ x y)) x))  )))

;; (unparse-expression (eta-reduce (parse-expression '(lambda (x) x))))


      


 

