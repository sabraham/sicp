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

(define (miller-rabin-test-once n)
  (define (non-trivial x x-squared-mod)
    (if (and (= 1 x-squared-mod)
             (not (= x 1))
             (not (= x (- n 1))))
        0
        x-squared-mod))
  (define (square-mod x)
    (non-trivial x (remainder (square x) n)))
  (define (expmod base exp m)
    (cond ((= exp 0) 1)
          ((even? exp) (square-mod (expmod base (/ exp 2) m)))
          (else (remainder (* base (expmod base (- exp 1) m))
                           m))))
  (define (try-it a)
    (= (expmod a (- n 1) n) 1))
  (try-it (+ 1 (random (- n 1)))))

(define (miller-rabin-test n times)
  (cond
   ((= times 0) #t)
   ((miller-rabin-test-once n) (miller-rabin-test n (- times 1)))
   (else #f)))


(apply boolean/or
       (map (lambda (x) (miller-rabin-test x 200))
            (list 561 1105 1729 2465 2821 6601)))

;; #f -- carmichael numbers are all false

(apply boolean/and
       (map (lambda (x) (miller-rabin-test x 500))
            (list 3571 27751 89041)))

;; #t -- primes pass

;; 1.3 Formulating Abstractions with Higher-Order Procedures

;; higher-order procedures - procs that manipulate procs

;; 1.3.1 Procedures as Arguments

(define (sum f next a b)
  (if (> a b)
      0
      (+ (f a)
         (sum f next (next a) b))))

(define (identity x) x)
(define (inc x) (+ x 1))
(define (dec x) (- x 1))

(define (sum-integers a b)
  (sum identity inc a b))

(define (sum-cubes a b)
  (sum cube inc a b))

(define (pi-sum a b)
  (define (pi-term x)
    (/ 1.0 (* x (+ x 2))))
  (define (pi-next x)
    (+ x 4))
  (sum pi-term pi-next a b))

(sum-integers 0 10)
(sum-cubes 1 3)
(* 8 (pi-sum 1 10000))

(define (integral f a b dx)
  (define (add-dx x) (+ x dx))
  (* (sum f add-dx (+ a (/ dx 2.0))  b) dx))

(integral cube 0 1 0.01)

;; Exercise 1.29

(define (simpson-int f a b n)
  (define step (/ (- b a) n))
  (define (next-step x) (+ x step))
  (define (nnext-step x) (+ x step step))
  (define (prev-step x) (- x step))
  (* (+ (f a)
        (* 2 (sum f next-step (next-step a) (prev-step b)))
        (* 2 (sum f nnext-step (next-step a) (prev-step b)))
        (f b))
     (/ step 3)))

(map (lambda (x) (< (abs (- (simpson-int cube 0 1 x) 0.25))
               (abs (- (integral cube 0 1 (/ 1 x)) 0.25))))
     (list 10 100 1000))

;; simpson rule is more accurate in cases n = 10, 100, 1000

;; Exercise 1.30

(define (sum f next a b)
  (define (iter a res)
    (if (> a b)
        res
        (iter (next a) (+ (f a) res))))
  (iter a 0))

;; Exercise 1.31

(define (product f next a b)
  (if (> a b)
      1
      (* (product f next (next a) b)
         (f a))))

(define (factorial n)
  (product identity inc 1 n))

(define (wallis n)
  (define (term n)
    (if (even? n)
        (/ (+ n 2) (+ n 1))
        (/ (+ n 1) (+ n 2))))
  (product term inc 1.0 n))

(* 4 (wallis 1000))

(define (product f next a b)
  (define (iter a res)
    (if (> a b)
        res
        (iter (next a) (* (f a) res))))
  (iter a 1))

;; Exercise 1.32

(define (accumulate combiner null-value f next a b)
  (if (> a b)
      null-value
      (combiner (f a) (accumulate combiner null-value f next (next a) b))))

(define (sum f next a b)
  (accumulate + 0 f next a b))

(define (product f next a b)
  (accumulate * 1 f next a b))

(define (accumulate combiner null-value f next a b)
  (define (iter a res)
    (if (> a b)
        res
        (iter (next a) (combiner res (f a)))))
  (iter a null-value))

;; Exercise 1.33

(define (filtered-accumulate combiner null-value f next a b pred)
  (define (iter a res)
    (if (> a b)
        res
        (iter (next a) (if (pred a) (combiner res (f a)) res))))
  (iter a null-value))

(define (sum-of-squared-primes a b)
  (filtered-accumulate + 0 square inc a b prime?))

(define (relatively-prime? n i)
  (= 1 (gcd n i)))

(define (product-of-relatively-prime n)
  (define (relatively-prime-to-n? i) (relatively-prime? n i))
  (filtered-accumulate * 1 identity inc 1 (dec n) relatively-prime-to-n?))

;; 1.3.2 Constructing Procedures Using Lambda

;; lambda -- special form that creates procedures; used to create procs in the same
;; way as define, but no name specified for the proc, so proc is not assoced
;; with any name in the env

;; let - special form to make anonymous bindings -- syntactic sugar over a lambda,
;; meaning that scope is specified by the body of the let

;; Exercise 1.34

;; (define (f g) (g 2))
;; (f f) => (f 2) => (2 2) => Error, object 2 is not applicable. ie 2 is not an
;; operator. nb- expansion is independent of whether using
;; applicative/normal-order evaluation.

;; 1.3.3 Procedures as General Methods

(define (close-enough? x y) (< (abs (- x y)) 0.001))

(define (search f neg-point pos-point)
  (let ((midpoint (average neg-point pos-point)))
    (if (close-enough? neg-point pos-point)
        midpoint
        (let ((test-value (f midpoint)))
          (cond ((positive? test-value)
                 (search f neg-point midpoint))
                ((negative? test-value)
                 (search f midpoint pos-point))
                (else midpoint))))))

(define (half-interval-method f a b)
  (let ((a-value (f a))
        (b-value (f b)))
    (cond ((and (negative? a-value) (positive? b-value))
           (search f a b))
          ((and (negative? b-value) (positive? a-value))
           (search f b a))
          (else
           (error "Values are not of opposite sign" a b)))))

(define tolerance 0.00001)

(define (fixed-point f first-guess)
  (define (close-enough? v1 v2)
    (< (abs (- v1 v2)) tolerance))
  (define (try guess)
    (let ((next (f guess)))
      (if (close-enough? guess next)
          next
          (try next))))
  (try first-guess))

(fixed-point cos 1.0)

;; average damping - technique of averaging successive approximations to a soln

;; Exercise 1.35

(fixed-point (lambda (x) (+ 1 (/ 1 x))) 1.0)

;; Exercise 1.36

(define (fixed-point f first-guess)
  (define (close-enough? v1 v2)
    (< (abs (- v1 v2)) tolerance))
  (define (try guess)
    (let ((next (f guess)))
      (display guess)
      (newline)
      (if (close-enough? guess next)
          next
          (try next))))
  (try first-guess))

;; 35 steps
(fixed-point (lambda (x) (/ (log 1000) (log x))) 2.0)
;; 9 steps w/average dampening
(fixed-point (lambda (x) (* 0.5 (+ x (/ (log 1000) (log x))))) 2.0)

;; Exercise 1.37

(define (cont-frac n d k)
  (define (rec n d i)
    (if (= i k)
        (/ (n i) (d i))
        (/ (n i) (+ (d i) (rec n d (inc i))))))
  (rec n d 1))

(cont-frac (lambda (i) 1.0)
           (lambda (i) 1.0)
           12)

;; k=12 gets us 4-decimal place accuracy
;; b- iterative version

(define (cont-frac-iter n d k)
  (define (iter n d i state)
    (if (= i 0)
        state
        (iter n d (dec i) (/ (n i) (+ (d i) state)))))
  (iter n d (dec k) (/ (n k) (d k))))

(cont-frac-iter (lambda (i) 1.0)
                (lambda (i) 1.0)
                12)

;; Exercise 1.38
(define (approx-e k)
  (define (decimal-approx k)
    (cont-frac-iter (lambda (i) 1.0)
                    (lambda (i)
                      (if (= (remainder i 3) 2)
                          (+ (* (/ (- i 2) 3) 2) 2)
                          1.0))
                    k))
  (+ 2 (decimal-approx k)))

(approx-e 10)

;; Exercise 1.39
(define (tan-cf x k)
  (define (n i) (if (= i 1)
                    x
                    (* -1 (square x))))
  (define (d i) (dec (* 2 i)))
  (cont-frac-iter n d k))

;; 1.3.4 Procedures as Returned Values

(define (average-damp f)
  (lambda (x) (average x (f x))))

(define (sqrt x)
  (fixed-point (average-damp (lambda (y) (/ x y)))
               1.0))

(define (cube-root x)
  (fixed-point (average-damp (lambda (y) (/ x (square y))))
               1.0))


(define dx 0.00001)
(define (deriv g)
  (lambda (x)
    (/ (- (g (+ x dx)) (g x))
       dx)))

(define (cube x) (* x x x))
((deriv cube) 5)

(define (newton-transform g)
  (lambda (x)
    (- x (/ (g x) ((deriv g) x)))))

(define (newtons-method g guess)
  (fixed-point (newton-transform g) guess))

(define (fixed-point-of-transform g transform guess)
  (fixed-point (transform g) guess))

;; 2 ways to write sqrt, both using fixed-point

(define (sqrt x)
  (fixed-point-of-transform (lambda (y) (/ x y))
                            average-damp
                            1.0))

(define (sqrt x)
  (fixed-point-of-transform (lambda (y) (-  (square y) x))
                            newton-transform
                            1.0))

;; first-class elements:
;; - may be named by variables
;; - may be passed as arguments to procedures
;; - may be returned as the result of procedures
;; - may be included in data structures

;; major implementation cost of first-class procedures: 
;; allowing procs to be returned as vals requires reserving storage for the
;; procs free variables, even while the proc is not executing

;; Exercise 1.40

(define (cubic a b c)
  (lambda (x) (+ (cube x) (* a (square x)) (* b x) c)))

(newtons-method (cubic 1 1 1) 1)

;; Exercise 1.41

(define (double f)
  (lambda (x) (f (f x))))

;; (((double (double double)) inc) 5)
;; psuedocode =
;; (((double 4x) inc) 5)
;; ((4x 4x) inc) 5)
;; ((16x inc) 5)
;; 21

;; Exercise 1.42

(define (compose f g)
  (lambda (x) (f (g x))))

((compose square inc) 6)

;; Exercise 1.43

(define (repeated f n)
  (if (= n 1)
      f
      (compose f (repeated f (dec n)))))

((repeated square 2) 5)

;; Exercise 1.44

(define (smooth f)
  (lambda (x) (/ (+ (f (- x dx))
               (f x)
               (f (+ x dx)))
            3.0)))

(define (n-fold-smoothed f n)
  (lambda (x) ((repeated smooth n)
          f)))

;; Exercise 1.45
TODO

;; Exercise 1.46

(define (iterative-improve good-enough? do-better)
  (define (ret guess)
    (if (good-enough? guess)
        guess
        (ret (do-better guess))))
  ret)

(define (sqrt x)
  (define (good-enough? guess)
    (< (abs (- (square guess) x)) 0.0001))
  (define (do-better guess)
    (average guess (/ x guess)))
  ((iterative-improve good-enough? do-better) 1.0))

(sqrt 25.0)

(define (fixed-point f first-guess)
  (define (good-enough? guess)
    (< (abs (- (f guess) guess)) 0.0001))
  (define (do-better guess)
    ((average-damp f) guess))
  ((iterative-improve good-enough? do-better) first-guess))

