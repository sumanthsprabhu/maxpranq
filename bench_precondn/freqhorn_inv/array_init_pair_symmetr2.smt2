(declare-var a (Array Int Int))
(declare-var a1 (Array Int Int))
(declare-var b (Array Int Int))
(declare-var b1 (Array Int Int))
(declare-var c (Array Int Int))
(declare-var c1 (Array Int Int))
(declare-var i Int)
(declare-var i1 Int)
(declare-var x Int)
(declare-var y Int)
(declare-var N Int)

(declare-rel inv1 ((Array Int Int) (Array Int Int) Int Int))
;; (define-fun inv1 ((_FH_0 (Array Int Int))(_FH_1 (Array Int Int))(_FH_2 Int)(_FH_3 Int)) Bool
;;   (forall ((i1 Int)) (or (<= i1 0) (< _FH_2 _FH_3) (< i1 0) (<= _FH_3 i1) (> (+ (select _FH_0 i1) (* (- 1) (select _FH_1 i1))) 0))))
(declare-rel inv2 ((Array Int Int) (Array Int Int) (Array Int Int) Int Int))
(declare-rel fail ())

(rule (inv1 a b 0 N))

(rule (=> (and (inv1 a b i N) (< i N) (= (store a i x) a1) (> x y) (= (store b i y) b1) (= i1 (+ i 1))) (inv1 a1 b1 i1 N)))

(rule (=> (and (inv1 a b i N) (>= i N)) (inv2 a b c 0 N)))

(rule (=> (and (inv2 a b c i N) (< i N) (= (store c i (- (select a i) (select b i))) c1) (= i1 (+ i 1))) (inv2 a b c1 i1 N)))

(rule (=> (and (inv2 a b c i N) (>= i N) (< 0 i1) (< i1 N) (not (> (select c i1) 0))) fail))

(query fail)
