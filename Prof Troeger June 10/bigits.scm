

;; representing numbers to the base n, with least significant digit first.

;; 31 comes out as (15 1) = ((makeRep 16) 31)
;; 256 as (0 0 1), 257 as (1 0 1), 273 as (1 1 1), etc.

;; see Exercise 2.1 for the inductive definition


(define (makeRep n)
  (letrec ((rep (lambda (m)
                  (cond ((zero? m) '())
                        (else (let ((r (remainder m n))
                                    (q (rep (quotient m n))))
                                (cons r q)))))))
    rep))



;; now, working entirely inside this representation -- that is, without converting back and forth from base 10

(define iszero? null?)

(define zero '())


;; assumes m is a legitimate representation, base n
(define (succBase n)
  (letrec ((succ (lambda (m)
                   (cond ((iszero? m) '(1))
                         ((= (- n 1) (car m)) (cons 0 (succ (cdr m))))
                         (else (cons (+ (car m) 1) (cdr m)))))))
    succ))


;; assumes m is a legitimate representation of a positive number, base n
;; that is: no trailing zeros -- eg, (1), but not (1 0 0) etc
(define (predBase n)
  (letrec ((pred (lambda (m)
                   (cond ((equal? m '(1)) zero)
                         ((> (car m) 0) (cons (- (car m) 1) (cdr m)))
                         (else (cons (- n 1) (pred (cdr m))))))))
    pred))



;; Responding to Exercise 2.2 will require verification, for arbitrary m, of

;;  (succ (representation of m)) = (representation of (m + 1))

;;  (pred (representation of (m + 1))) = (representation of m)


;; for example, 

;; ((succBase 16) ((makeRep 16) 101)) = ((makeRep 16) 102)

;; and

;; ((predBase 16) ((makeRep 16) 102)) = ((makeRep 16) 101)


;; Of course, the argument must hold for all bases n >= 2 as well

