(declare-var a (Array Int Int))
(declare-var a1 (Array Int Int))
(declare-var b (Array Int Int))
(declare-var b1 (Array Int Int))
(declare-var i Int)
(declare-var i1 Int)
(declare-var j Int)
(declare-var j1 Int)

(declare-var N Int)

;; (declare-rel inv1 ((Array Int Int) Int Int Int ))
(define-fun inv1 ((_FH_0 (Array Int Int))(_FH_1 Int)(_FH_2 Int)(_FH_3 Int)) Bool
  (forall ((i1 Int)) (or (<= i1 0) (< _FH_1 _FH_3) (< i1 0) (<= _FH_3 i1) (<= _FH_2 (select _FH_0 i1)))))
(declare-rel inv2 ((Array Int Int) (Array Int Int) Int Int Int))
(declare-rel fail ())

;; (rule (inv1 a 0 j N))

;; (rule (=> (and (inv1 a i j N) (< i N) (= j1 (ite (> j (select a i)) (select a i) j)) (= i1 (+ i 1))) (inv1 a i1 j1 N)))

(rule (=> (and (inv1 a i j N) (>= i N)) (inv2 a b 0 j N)))

(rule (=> (and (inv2 a b i j N) (< i N) (= (store b i (- (select a i) j)) b1) (= i1 (+ i 1))) (inv2 a b1 i1 j N)))

(rule (=> (and (inv2 a b i j N) (>= i N) (< 0 i1) (< i1 N) (not (>= (select b i1) 0))) fail))

(query fail)
