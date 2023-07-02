(declare-var a (Array Int Int))
(declare-var a1 (Array Int Int))
(declare-var b (Array Int Int))
(declare-var b1 (Array Int Int))
(declare-var i Int)
(declare-var i1 Int)
(declare-var j Int)
(declare-var j1 Int)
(declare-var k Int)

(declare-var N Int)
(declare-var N1 Int)

(declare-rel inv1 ((Array Int Int) (Array Int Int) Int Int Int ))
(declare-rel inv2 ((Array Int Int) (Array Int Int) Int Int Int))
(declare-rel fail ())

;; (rule (inv1 a 0 j N))

;; (rule (=> (and (inv1 a i j N) (< i N) (= j1 (ite (> j (select a i)) (select a i) j)) (= i1 (+ i 1))) (inv1 a i1 j1 N)))

(rule (=> (and (inv1 a b i j N) (> N 0) (= N1 N)) (inv2 a b 0 j N1)))

(rule (=> (and (inv2 a b i j N) (< i N) (= a1 (store a i (select a i))) (= (store b i (select a (- N i))) b1) (= i1 (+ i 1))) (inv2 a1 b1 i1 j N)))

(rule (=> (and (inv2 a b i j N) (>= i N) (<= 0 i1) (< i1 N) (not (>= (select b i1) j))) fail))

(query fail)
