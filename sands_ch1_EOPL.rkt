#lang eopl

;; EOSL

;; Chapter 1

#|

Backus-Naur Form (BNF)


<list-of-numbers> ::= () | (<number> . <list-of-numbers>)

Kleene star {...}* (0 or more instances)

<list-of-numbers> = ({<number>}*)

{...}+ indicates 1 or more

<nontermexp>, {<nontermexp>}*^(c) sequence of any number of instances of expression, separated by non-empty
character sequence c.

  Ex 1.1

syntactic derivation  that proves that (-7 . (3 . (14 .()))) is a list of numbers.

<list-of-numbers>
• (<number> . <list-of-numbers>)
• (-7 . (<number> . <list-of-numbers>))
• (-7 . ( 3 . (<number> . <list-of-numbers>)))
• (-7 . ( 3 . (14 . ())))

e.g. s-list
<s-list>  ::= ({<symbol-expression>}*)
<symbol-expression> ::= <symbol> | <s-list>

( a (b c) ((d)))

<s-list>
(<symexp> <symexp> <symexp>)
(<symbol> <symexp> <symexp>)
( a <s-list> <s-list> )
( a (<symbol> <symbol>) (<symexp>))
( a (b c) (<s-list>))
( a (b c) ((<symexp>)))
( a (b c) ((<symbol>)))
( a (b c) ((d)))

e.g binary-tree with numeric leaves and labelled nodes

<bintree> ::= <number> | (<symbol> <bintree> <bintree>)

e.g. lambda calculus
variable references, lambda expressions with a single formal parameter,
and procedure calls. 

<expression> ::= <identifier>
             :: (lambda (<identifier>) <expression>)
             :: (<expression> <expression>)

e.g. syntactic category of data in Scheme

<list> ::= ({<datum>}*)
<dotted-datum> ::= ({<datum>}^+ . <datum>)
<vector> ::= #({<datum>}^*)
<datum> ::= <number> | <symbol> | <boolean> | <string>
        ::= <list> | <dotted-datum> | <vector>

Ex 1.4
Induction on # of lambdas

|#

(define e
  (lambda (x n)
    (if (zero? n) 1
        (* x (e x (- n 1))))))

; use inductive def's to write recursive procedures
(define count-nodes
  (lambda (s)
    (if (number? s) 1
        ( + (count-nodes (cadr s))
            (count-nodes (caddr s))
            1))))

#|

When defining a program based on structural induction, the structure
of the program should be patterned after the structure of the data.

Typically this means that we will need one procedure for each syntactic
category in the grammar.  Each procedure will examine the input to see
which production it corresponds to; for each nonterminal that
appears in the right-hand side, we will have a recursive call to the pro-
cedure for that nonterminal.
e.g.
<list-of-numbers> ::= () | (<number> . <list-of-numbers>)

define the set of lists
<list> ::= () | (<datum>.<list>)
|#

(define list-of-numbers?
  (lambda (lst)
    (if (null? lst)
        #t 
        ;; if list not empty, then input is (<datum>.<list>)
        (and (number? (car lst))
            (list-of-numbers? (cdr lst))))))

#| Proof of correctness:
Using induction on length of lst
1.  procedure works on a list of length 0.
2.  assume it works correctly on a list of length k
3.  let lst be a list of length k+1.  by the def. of
list, lst = (<datum>.<list>), where <list> has length k.
list is a list-of-numbers iff its car is a number and
its cdr is a list-of-numbers. since cdr lst is a list
of length k, the procedure correctly determines its
membership in list-of-numbers.
|#

(define nth-elt
  (lambda (lst n)
    (if (null? lst)
        (eopl:error 'nth-elt
                    "List too short by ~s elements" (+ n 1))
        (if (= n 0)
            (car lst)
            (nth-elt (cdr lst) (- n 1))))))

(define list-length
  (lambda (lst)
    (cond ((null? lst) 0)
          (else (+ 1 (list-length (cdr lst)))))))

(define remove-first
  (lambda (los s)
    (cond ((null? los) '())
          ((eq? (car los) s) (cdr los))
          (else (cons (car los) (remove-first (cdr los) s))))))

(define remove
  (lambda (los s)
    (cond ((null? los) '())
          ((eq? (car los) s) (remove (cdr los) s))
          (else (cons (car los) (remove (cdr los) s))))))

;; <s-list> ::= ()
;;          :: = (<symbol-expression . <s-list>)
;; <symbol-expression> ::= <symbol> | <s-list>
;; grammar for its input contains two non-terminals, so
;; we should have two procedures, one for each non-terminal


(define subst
  (lambda (slist old new)
    (cond ((null? slist) '())
          (else (cons (subst-in-sym-exp (car slist) old new)
                      (subst (cdr slist) old new))))))

(define subst-in-sym-exp
  (lambda (se old new)
    (cond ((symbol? se)
           (if (eq? se old) new
               se))
          (else (subst se old new)))))


(define partial-vector-sum
  (lambda (von n)
    (if (zero? n)
        0
        (+ (vector-ref von (- n 1))
           (partial-vector-sum von (- n 1))))))

(define vector-sum
  (lambda (von n)
    (partial-vector-sum von (length von))))
;; Note that von does not change.
;; so we can also write
(define vector-sum2
  (lambda (von)
    (letrec
        ((partial-sum
          (lambda (n)
            (if (zero? n)
                0
                (+ (vector-ref von (- n 1))
                   (partial-sum (- n 1)))))))
    (partial-sum (vector-length von)))))


#| 1.3 Scoping and Binding of Variables |#

#| Definition 1.3.1 (Binding Rule for Lambda Calculus Expressions)
   In (lambda (<identifier>) <expression>), the occurence of <identifier>
   is a declaration that binds all occurrences of that variable in <expression>
   unless some intervening declarartion of the same variable occurs. |#

(define foop
  (lambda (y)
    ((lambda (x) x) y)))

;; the value of am expression depends only on the values associated
;; with the variables that occur free within the expression

;; conversely, the value of an exression is independent of the bindings
;; of variables that do not occur free in the expression.

;; thus the meaning of an expression with no free variables is fixed.

;; e.g. (lambda (x) x) has a fixed meaning (identity function)
;; other lambda calculus expressions without free variables also have
;; fixed meanings
;; (e.g.)
;; (lambda (f)
;;   (lambda (x)
;;      (f x)))

;; LC expressions w/out free variables are called combinators

#| recall the grammar of lambda-calculus expressions:
LcExp ::= Indentifier
      ::= (lambda (Identifier) LcExp
      ::= (LcExp LcExp)
A variable is 'free' in and expression exp if it has some occurrence in exp
that is not inside some lambda binding of the same variable.
Rules:
  If expression e is a variable, then the variable x occurs free in e iff
  x = e.

  If the expression e is of the form (lambda (y) e'), then the variable x
  occurs free in e iff y is different from x and x occurs free in e'

  If the expression e is of the form (e1 e2), then x occurs free in e iff
  it occurs free in e1 OR e2.  
|#

(define occurs-free?
  (lambda (x e)
    (cond
      ((symbol? e) (eq? x e))
      ((eq? (car e) 'lambda)
       (and (not (eq? (x (car (cadr e)))))
            (occurs-free? x (caddr e))))
      (else
       (or
        (occurs-free? x (car e))
        (occurs-free? x (cadr e)))))))

#| Scope and Lexical Address |#

(define x
  (lambda (x)
    (map
     (lambda (x)
       (+ x 1))
    x)))