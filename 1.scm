;; 1.1.1 Expressions
;;
;; combinations - expressions formed by delimiting a list of
;; expressions withing parenthesis in order to denote procedure
;; application
;;
;; operator - leftmost element in a combination
;;
;; operands - elements in a combination that are not the operand
;;
;; value of a combination - obtained by applying the procedure
;; specified by the operator to the arguments, which are the values of
;; the operands
;;
;; prefix notation - convention of placing the operator to the left of
;; the operands

;; 1.1.2 Naming and the Environment
;;
;; variable - the name used to refer to computational objects
;;
;; value - the object to which the variable refers


(define size 2)
size
(* 5 size)

(define pi 3.14159)
(define radius 10)
(* pi (* radius radius))
(define circumference (* 2 pi radius))
circumference

;; environment (global) - memory in which interpreter keeps track of name-object
;; pairs

;; 1.1.3 Evaluating Combinations
;;
;; to evaluate a combination
;; - evaluate subexpressions of combination
;; - apply the proc of, the val of the leftmost subexpression (operator) to the
;;   arguments, the values of the other subexpressions (operands)
;;
;; can think of expression as tree of subexpressions -- nodes are subexpressions
;; and leaves are operators or primitives
;;
;; evaluating primitives can be thought of a special case:
;; - values of numerals are numbers they name
;; - values of built-in operators are the instruction sequences to carry out the
;;   named operation
;; - values of other names are objects assoced with those names in the env
;;
;; (second rule is really special case of third rule)
;;
;; * all symbols meaning derives from its env -- e.g., (+ x 1) is meaningful
;; only wrt to the env in which + and x have some defined meaning
;;
;; nb- define is not a combination -- (define x 3) does not apply define on x
;; and 3, as x does not have meaning yet!
;;
;; special forms - exceptions to the general evaluation rule


;; 1.1.4 Compound Procedures
;;
;; elements that must appear in any powerful programming language
;; - numbs and arith operations are prim data and procs
;; - nesting of combinations is a means of combining operations
;; - defns that assoc names w/vals provide a (limited) means of abstraction
;;
;; procedure definitions - a compound operation can be given a name and then
;;                         referred to as a unit (abstraction technique)
;;
;; * define actually does 2 things: 1- create a proc, 2- assoc a name w/the proc
;;
;; compound procedure - procedure resulting from compounding primitive procs

(define (square x) (* x x))
(define (sum-of-squares x y) (+ (square x) (square y)))
(define (f a) (sum-of-squares (+ a 1) (* a 2)))

;; 1.1.5 The Substitution Model for Procedure Application
;;
;; to eval a combination whose oper names a comp proc, the interpreter follows
;; same process as for combinations whose operators name prim procs
;;
;; can assume the mechanism to apply prim procs to args is built into the interp
;;
;; * substitution model for proc application - to apply a compound proc to args,
;; eval the body of the proc with each formal param replaced by the
;; corresponding arg
;;
;; normal-order evaluation - fully expand substitutions and then reduce
;; applicative-order evaluation - reduce before substituting
;;
;; Lisp uses applicative-order -- 1. more efficient, 2. nromal-order becomes
;; complicated to deal with for procs that cannot be modeled by substitution


;; 1.1.6 Conditional Expressions and Predicates
;;
;; case analysis - special form - no way from above to do branching - in lisp
;;                 use cond

(define (abs x)
  (cond ((> x 0) x)
        ((= x 0) 0)
        ((< x 0) (- x))))

;; clause - pair of expressions in a cond -- first is pred, second is
;; consequeent expression to eval if pred is true (in lisp, true = not false =
;; not #f) 
;;
;; predicate - an expression/proc whose value is either true or false
;;
;; cond goes through its clauses until it hits a true pred, and returns that
;; consequeuent expression. if there does not exist true pred,
;;
;; if, and, or, not ...
;;
;; cond, and, or, if -- special forms b.c. not all subexps are evaled

;; Excercise 1.1

;; 10
10

;; 12
(+ 5 3 4)

;; 8
(- 9 1)

;; 3
(/ 6 2)

;; 6
(+ (* 2 4) (- 4 6))

;; a
(define a 3)

;; b
(define b (+ a 1))

;; 19
(+ a b (* a b))

;; 4 (b)
(if (and (> b a) (< b (* a b)))
    b
    a)

;; 16 (+ 6 7 a)
(cond ((= a 4) 6)
      ((= b 4) (+ 6 7 a))
      (else 25))

;; 6
(+ 2 (if (> b a) b a))

;; 16
(* (cond ((> a b) a)
         ((< a b) b)
         (else -1))
   (+ a 1))

;; Exercise 1.2

(/ (+ 5 4 (- 2 (- 3 (+ 6 (/ 4 5)))))
   (* 3 (- 6 2) (- 2 7)))

;; Exercise 1.3

(define (sum-of-larger-squares x y z)
  (cond
   ((and (<= x y) (<= x z)) (sum-of-squares y z))
   ((and (<= y x) (<= y z)) (sum-of-squares x z))
   (else (sum-of-squares x y))))

;; Exercise 1.4
;; returns a + |b| by adding b if b is pos or subtracting b if b is neg

(define (a-plus-abs-b a b)
  ((if (> b 0) + -) a b))

;; Exercise 1.5

(define (p) (p))
(define (test x y)
  (if (= x 0) 0 y))

;; (test 0 (p))
;; if applicative-order: infinite-loop!! will try and eval p, and get caught
;; evaling itself forever!
;; (test 0 (p)) => (test 0 (p)) => ....
;; if normal-order: will return 0. substitutes then reduces, so (p) is never
;; evaled
;; (test 0 (p)) => (if (= 0 0) 0 (p)) => 0

;; 1.1.7 Example: Square roots by Newton's Method

;; a procedure is imperative, as opposed to math functions which are declaritive

(define (good-enough? guess x)
  (< (abs (- (square guess) x))
     0.001))

(define (average x y)
  (/ (+ x y) 2))

(define (improve guess x)
  (average guess (/ x guess)))

(define (sqrt-iter guess x)
  (if (good-enough? guess x)
      guess
      (sqrt-iter (improve guess x) x)))

(define (sqrt x)
  (sqrt-iter 1.0 x))

;; Example 1.6

(define  (new-if predicate then-clause else-clause)
  (cond (predicate then-clause)
        (else else-clause)))

(define (new-sqrt-iter guess x)
  (new-if (good-enough? guess x)
          guess
          (new-sqrt-iter (improve guess x) x)))

(sqrt-iter 1.0 1000.0)
(new-sqrt-iter 1.0 1000.0)

;; using new-if gives us an infinite loop! cond is a special-form, but new-if is
;; not, so the interpreter evals the new-iff args in applicative order, meaning
;; the recursive call is always evaled w/o end :(

;; Exercise 1.7

;; good-enough? will fail for very small numbers, b.c. the constant epsilon here
;; (0.001) may be an order of magnitude larger than the number we are actually
;; seeking:

(good-enough? 0.0001 0.00001) ;; #t

;; on the other side of the coin, the test will fail for very large numbers, as
;; we will find a delta interval that exceeds the precision available ie, there
;; exists x s.t guess^2 < x < (guess + delta)^2, and precision available means
;; we cannot consider a number between guess and guess + delta

;; Exercise 1.8

(define (good-enough-cbrt? guess x)
  (< (abs (- (* guess guess guess) x))
     0.001))

(define (improve-cbrt guess x)
  (/ (+ (/ x (square guess))
        (* 2 guess))
     3))

(define (cbrt-iter guess x)
  (if (good-enough-cbrt? guess x)
      guess
      (cbrt-iter (improve-cbrt guess x) x)))

(define (cbrt x)
  (cbrt-iter 1.0 x))

;; 1.1.8 Procedures as Black-Box Abstractions

;; procedural abstraction - an abstraction of a procedure
;;
;; bound variable - name of a formal parameter in a procedure defn
;;
;; free variable - variable that is not bound
;;
;; scope - (of a name) the set of expressions of which a binding defines a name
;;
;; capturing - (a variable) overriding a var in a scope (?)
;;
;; lexical scoping - free vars in a proc are taken to refer to bindings made by
;; enclosing proc defns


;; 1.2 Procedures and the Processes They Generate

;; 1.2.1 Linear Recursion and Iteration

(define (factorial n)
  (if (= n 1)
      1
      (* n (factorial (- n 1)))))

(define (factorial n)
  (define (iter product counter)
    (if (> counter n)
        product
        (iter (* counter product)
              (+ counter 1))))
  (iter 1 1))

;; re: factorial processes above
;; first: linear (in n) recurssive process
;; secnd: linear (in n) iterative process
;;
;; recursive process - process characterized by a chain of deferred operations.
;;   requires the iterpreter to keep track of the operations to be performed
;;   later.
;;
;; iterative process - process in which the state can be summarized by a fixed
;;   number of state variables with a fixed rule that describes how state
;;   variables shold be updated as the process moves from state to state, and an
;;   optional end test that specifies conditions under with the process should
;;   terminate
;;
;; iterative process has all information at any point, recursive process
;; requires hidden outside information. former can be done on fixed set of
;; registers and no aux memory. latter requires a stack

;; Exercise 1.9

;; first + implementation (recursive)
;; (+ 4 5)
;; (inc (+ 3 5))
;; (inc (inc (+ 2 5)))
;; (inc (inc (inc (+ 1 5))))
;; (inc (inc (inc (inc (+ 0 5)))))
;; (inc (inc (inc (inc 5)))))
;; (inc (inc (inc 6)))
;; (inc (inc 7)
;; (inc 8) => 9
;;
;; second + implementation (iterative)
;; (+ 4 5)
;; (+ 3 6)
;; (+ 2 7)
;; (+ 1 8)
;; (+ 0 9) => 9

;; Exercise 1.10

(define (A x y)
  (cond ((= y 0) 0)
        ((= x 0) (* 2 y))
        ((= y 1) 2)
        (else (A (- x 1)
                 (A x (- y 1))))))

(A 1 10) ;; 1024
(A 2 4)  ;; 65536
(A 3 3)  ;; 65536

(define (f n) (A 0 n)) ;; f(n) = 2 * n
(define (g n) (A 1 n)) ;; g(n) = 2^n
(define (h n) (A 2 n)) ;; g(n) = 2^2^...^2^n

(define (fib n)
  (cond ((= n 0) 0)
        ((= n 1) 1)
        (else (+ (fib (- n 1))
                 (fib (- n 2))))))

(define (fib n)
  (define (iter a b count)
    (if (= count 0)
        b
        (iter (+ a b) a (- count 1))))
  (iter 0 1 n))

;; Exercise 1.11

(define (f-rec n)
  (if (< n 3)
      n
      (+ (f-rec (- n 1))
            (* 2 (f-rec (- n 2)))
            (* 3 (f-rec (- n 3))))))

;; maintain state of f(n-i) i = 1..3

(define (f-iter n)
  (define (iter fn-1 fn-2 fn-3 count)
    (if (= count n)
        fn-1
        (iter (+ fn-1 (* 2 fn-2) (* 3 fn-3))
              fn-1
              fn-2
              (+ count 1))))
  (if (< n 3)
      n
      (iter 2 1 0 2)))

(= (f-rec 5) (f-iter 5))

;; Exercise 1.12

(define (binomial n k)
  (if (or (= k 0)
          (= k n))
      1
      (+ (binomial (- n 1) (- k 1))
         (binomial (- n 1) k))))

(= 6 (binomial 4 2))
(= 4 (binomial 4 1))

;; Exercise 1.13

;; F(n) = (phi^n - psi^n)/sqrt(5) (solve the linear recurrence)
;; psi = phi - 1 => -0.6 < psi < -0.7 => |psi|^n/sqrt(5) < 1/sqrt(5) < 1/2
;; => closet integer to phi^n/sqrt(5) is F(n)


;; 1.2.3 Orders of Growth

;; Exercise 1.14 TODO

;; Exercise 1.15

(define (cube x) (* x x x))
(define (p x) (- (* 3 x) (* 4 (cube x))))
(define (sine angle)
  (if (not (> (abs angle) 0.1))
      angle
      (p (sine (/ angle 3.0)))))

;; A. p is applied 5 times
;; B. alg is O(log a) in space and time


;; 1.2.4 Exponentiation

;; recursive
(define (expt b n)
  (if (= n 0)
      1
      (* b (expt b (- n 1)))))

;; iterative
(define (expt b n)
  (define (iter counter product)
    (if (= counter 0)
        product
        (iter (- counter 1)
              (* b product))))
  (iter n 1))

(define (even? n)
  (= (remainder n 2) 0))

(define (fast-expt b n)
  (cond ((= n 0) 1)
        ((even? n) (square (fast-expt b (/ n 2))))
        (else (* b (fast-expt b (- n 1))))))

;; Exercise 1.16
;; keep ab^n invariant
(define (fast-exp-iter b n)
  (define (iter b n a)
    (cond ((= n 0) a)
          ((even? n) (iter (square b) (/ n 2) a)) 
          (else (iter b (- n 1) (* a b)))))
  (iter b n 1))

;; Exercise 1.17

(define (fast-* a b)
  (cond
   ((= b 0) 0)
   ((= b 1) a)
   ((even? b) (fast-* (double a) (halve b)))
   (else (+ a (fast-* a (- b 1))))))

;; Exercise 1.18

(define (fast-*-iter a b)
  (define (iter a b prod) ;; ab is invariant
    (cond
     ((= b 0) prod) 
     ((even? b) (iter (double a) (halve b) prod))
     (else (iter a (- b 1) (+ prod a)))))
  (iter a b 0))

;; Exercise 1.19
;;
;; p' = p^2 + q^2
;; q' = 2pq + q^2
;;
;; Tp,q(a, b) = (bq + aq + ap, bp + aq)
;; Tp,q(bq + aq + ap, bp + aq)
;;      = (q(bp + aq) + (p+q)(bq + aq + ap), p(bp + aq) + q(bq + aq + ap))
;;      = (bpq + aq^2 + bpq + apq + ap^2 + bq^2 + aq^2 + apq,
;;         bp^2 + apq + bq^2 + aq^2 + apq)
;;      = (b(2pq + q^2) + a((p^2 + q^2) + (2pq + p^2)),
;;         b(p^2 + q^2) + a(2pq + q^2))
;;      = T(p^2 + q^2),(2pq + q^2)(a, b)

;; 1.2.5 Greatest Common Divisors

(define (gcd a b)
  (if (= b 0)
      a
      (gcd b (remainder a b))))

;; Exercise 1.20
;; todo

;; 1.2.6  Example: Testing for Primality

(define (smallest-divisor n) (find-divisor n 2))

(define (find-divisor n test-divisor)
  (cond ((> (square test-divisor) n) n)
        ((divides? test-divisor n) test-divisor)
        (else (find-divisor n (+ test-divisor 1)))))

(define (divides? a b)
  (= (remainder b a) 0))

;; O(sqrt(n))
(define (prime? n)
  (= n (smallest-divisor n)))

;; Fermat's Little T: n prime => a^n equiv a mod n

(define (expmod base exp m)
  (cond ((= exp 0) 1)
        ((even? exp) (remainder (square (expmod base (/ exp 2) m))
                                m))
        (else (remainder (* base (expmod base (- exp 1) m))
                         m))))

(define (fermat-test n)
  (define (try-it a)
    (= (expmod a n n) a))
  (try-it (+ 1 (random (- n 1)))))

(define (fast-prime? n times)
  (cond ((= times 0) true)
        ((fermat-test n) (fast-prime? n (- times 1)))
        (else false)))

;; Exercise 1.21

(smallest-divisor 199) ; 199, prime
(smallest-divisor 1999) ; 1999, prime
(smallest-divisor 19999) ; 7, not-prime

;; Exercise 1.22

(define (timed-prime-test n)
  (start-prime-test n (runtime)))

(define (start-prime-test n start-time) 
  (if (prime? n) 
      (report-prime n (- (runtime) start-time))))

(define (report-prime n elapsed-time)
  (newline)
  (display n)
  (display " *** ") 
  (display elapsed-time))
  
(define (search-for-primes a b)
  (define (iter a b)
    (if (<= a b) (timed-prime-test a))
    (if (<= a b) (iter (+ 2 a) b)))
  (if (even? a)
      (iter (+ 1 a) b)
      (iter a b)))

(search-for-primes 10000000000 10000000050) ;.24, .24
(search-for-primes 100000000000 100000000050) ; .78, .78
(search-for-primes 1000000000000 1000000000050) ; 2.349
(search-for-primes 10000000000000 10000000000050) ; 7.38

;; See O(sqrt(n)) growth!

;; Exercise 1.23

(define (next n)
  (if (= n 2)
      3
      (+ n 2)))

(define (find-divisor n test-divisor)
  (cond ((> (square test-divisor) n) n)
        ((divides? test-divisor n) test-divisor)
        (else (find-divisor n (next test-divisor)))))

(search-for-primes 10000000000 10000000050) ; .16, .15 => 2/3 ratio
(search-for-primes 100000000000 100000000050) ; .47, .46 => 2/3 ratio
(search-for-primes 1000000000000 1000000000050) ; 1.47 => 2/3 ratio
(search-for-primes 10000000000000 10000000000050) ; 4.64 => 2/3 ratio

;; change does not drop by factor of 2, but by factor of 3/2. presumably the
;; reason we don't see full asymptoic 2 drop is b.c. of the cost of checking
;; equality to 2.

;; Exercise 1.24

(define (start-prime-test n start-time) 
  (if (fast-prime? n 1000) 
      (report-prime n (- (runtime) start-time))))

(search-for-primes 100000000000000000000 100000000000000000100) ; 0.04
(search-for-primes 10000000000000000000000000000000000000000
                   10000000000000000000000000000000000001000) ; 0.079, 0.80, 079...

;; doubling number of digits doubles time, as expected

;; Exercise 1.25

;; Alyssa's method will work, but will be extremely inefficient, as it will
;; compute large intermediate results, rather than just the modulo

;; Exercise 1.26

;; Every time even exp is called by Louis's expmod, we call expmod twice. Call
;; the number of calls a function f. f(n) ~ O(1 + 2*f(n - 1)). Inductively we have
;; f(n) ~ O(n + ... + 4 + 2 + 1) ~ O(n).

;; Exercise 1.27

(define (fool-me-once n)
  (define (pass? x)
    (= x (expmod x n n)))
  (define (iter a)
    (cond
     ((= a n) #t)
     ((pass? a) (iter (+ 1 a)))
     (else #f)))
  (iter 1))

(apply boolean/and
       (map fool-me-once
            (list 561 1105 1729 2465 2821 6601))) ;#t

;; Exercise 1.28

