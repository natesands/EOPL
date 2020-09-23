#lang eopl

#|
EOPL
CHAPTER 2
Notes and Exercises
2.1 and 2.2, and 2.4 and 2.5

Nate Sands
6/10/2020
Prof. Troeger


*** NOTES **** 
Representations or non-neg integers
1. Unary : for n >= 0, rep(n) = (#t #t ... <n times>)


(define zero '())
(define iszero? null?)
(define succ (lambda (n) (cons #t n)))
(define pred cdr)


2. Scheme rep:

(define zero 0)
(define iszero? zero?)
(define succ (lambda (n) (+ n 1)))
(define pred (lambda (n) (- n 1)))


3. Bignum representation:
We work base N with (N-1) symbols
rep (n) = () if n=0,
        = (cons r rep(q)), n = qN + r, 0<= r < N

e.g.
N = 16
rep(33) = rep(2*16 + 1) = (cons 1 (rep (2))  = (cons 1 (rep(0*N + 2))
        = (cons 1 (cons 2 (rep (0)) = (cons 1 (cons 2 ())) = (1 2).
rep(258) = rep(16*16+2) = (cons 2 (rep 16)) = (cons 2 (rep(1*16 + 0)))
         = (cons 2 (cons 0 (rep(1)))) = (cons 2 (cons 0 (cons 1 (rep(0))))
         = (cons 2 (cons 0 (cons 1 ()))) = (2 0 1)
|#
;:::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::;

;; Ex. 2.1

;;;;;;;;;;;;;;

(define int-to-bigit
  (lambda (n N)
    (if (= n 0) '()
        (cons (remainder n  N) (int-to-bigit (quotient n N) N)))))

(define bigit-to-int
  (lambda (b N)
    (define bigit-iter
      (lambda (b N power sum)
        (cond ((null? b) sum)
              (else
               (bigit-iter (cdr b) N (* power N) (+ sum (* (car b) power)))))))
    (bigit-iter b N 1 0)))
    

;;;;;;;;;;;;;;
;; must deal with multiple represenatations of zero...
;; '(), '(0), '(0 0 0 0)
(define zero '())

(define iszero?
  (lambda (n)
    (cond ((null? n) #t)
     (else
      (and (eq? (car n) 0) (iszero? (cdr n)))))))


(define succ
  (lambda (n N)
    (cond ((eq? n '()) (cons 1 '()))
          ((< (car n) (- N 1))
           (cons (+ 1 (car n)) (cdr n)))
          (else
           (cons 0 (succ (cdr n) N))))))


;; pred returns zero if called on zero

(define pred
  (lambda (n N)
    (cond ((iszero? n) zero)
          ((> (car n) 0)
           (cons (- (car n) 1) (cdr n)))
          (else
           (cons (- N 1) (pred (cdr n) N))))))

(define plus
  (lambda (a b N)
    (cond ((iszero? b) a)
          (else
           (succ (plus a (pred b N) N) N)))))

(define mult
  (lambda (n m N)
    (cond ((iszero? m) zero)
          (else
           (plus n (mult n (pred m N) N) N)))))

(define fac
  (lambda (n N)
    (if (iszero? n) '(1)
    (mult n (fac (pred n N) N) N))))
;; better way to calculate factorial?
;; 10! = (5*2)(9)(2*4)(7)(2*3)(5)(2*2)(3)(2)
;;       = (9*7*5*3)(5*2)(2*4)(2*3)(2*2)(2)
  ;;     = (9*7*5*3)(5*4*3)(2*2*2*2*2*2)
    ;;   = (9*7*5*3)(5*3)(2^8)

;; The run time of pred, succ depends on the number of digits in the representation of
;; integer n, which is approximately log_N (n).

#|

2.2 An Abstraction for Inductive Data Types

<bintree> ::== <number> | (<symbol> <bintree> <bintree>)

|#

(define-datatype bintree bintree?
  (leaf-node
   (datum number?))
  (interior-node
   (key symbol?)
   (left bintree?)
   (right bintree?)))

;; Scheme values belong to a discriminated union of all primitive types (each has a type 'tag').

;; Inductively defined data types are represented as a discriminated union of
;; record types (elements are accessed via field name).

;; (define-datatype <type-name> <type-predicate-name>
;; {(variant-name {(field-name predicate)}*)}*)

;; find the sum of integers in the leaes of a bintree

(define leaf-sum
  (lambda (tree)
    (cases bintree tree
      (leaf-node (datum) datum)
      (interior-node (key left right)
                     (+ (leaf-sum left) (leaf-sum right))))))



;; Exercise 2.4
;; turns binary tree into list
(define bintree-to-list
  (lambda (tree)
    (cases bintree tree
      (leaf-node (datum) (cons 'leaf-node
                               (cons datum '())))
      (interior-node (key left right)
                     (cons 'interior-node
                           (cons key
                                 (cons (bintree-to-list left)
                                       (cons (bintree-to-list right) '()))))))))


;; Test Trees
(define tree-d (interior-node 'a (interior-node 'b (leaf-node 1) (leaf-node 2)) (leaf-node 3)))
(define tree-a (interior-node 'a (leaf-node 2) (leaf-node 3)))
(define tree-b (interior-node 'b (leaf-node -1) tree-a))
(define tree-c (interior-node 'c tree-b (leaf-node 1)))

; > (bintree-to-list tree-d)
;(interior-node a (interior-node b (leaf-node 1) (leaf-node 2)) (leaf-node 3))

;; Exercise 2.5
;; (This is very sloppy but seems to get the job done)

(define node-sums
  (lambda (tree)
    (cases bintree tree
      (leaf-node (datum) '())
      (interior-node (key left right)
                     (cons
                       (cons key (cons (+ (leaf-sum left)
                                           (leaf-sum right))
                                        '()))
                       (cons (node-sums left) (node-sums right)))))))
;> (node-sums tree-c)
;((c 5) ((b 4) () (a 5) ()))
;> (node-sums tree-a)
;((a 5) ())
;> (node-sums tree-b)
;((b 4) () (a 5) ())

(define (flatten lst)
  (cond ((null? lst) '())
        ((pair? lst)
         (append (flatten (car lst)) (flatten (cdr lst))))
        (else (list lst))))

;> (flatten (node-sums tree-c))
;(c 5 b 4 a 5)

(define get-max
  (lambda (lst node sum)
    (cond ((null? lst) node)
          ((> (cadr lst) sum) (get-max (cddr lst) (car lst) (cadr lst)))
          (else (get-max (cddr lst) node sum)))))
 
;> (get-max '(c 5 b 4 a 5) 'd 6)
;d
;> (get-max '(c 5 b 4 a 5) 'd 3)
;c    

;; putting it alllllll together...


(define max-interior
  (lambda (tree)
    (let ((node-list (flatten (node-sums tree)))
      (b (list 4 5 6)))
     (get-max (cddr node-list) (car node-list) (cadr node-list)))))

;> (max-interior tree-b)
;a
;> (max-interior tree-c)
;c