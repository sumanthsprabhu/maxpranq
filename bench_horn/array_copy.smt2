(declare-var a (Array Int Int))
(declare-var b (Array Int Int))
(declare-var b1 (Array Int Int))
(declare-var i Int)
(declare-var i1 Int)
(declare-var n Int)
(declare-var n1 Int)

(declare-rel inv ((Array Int Int) (Array Int Int) Int Int))
(declare-rel fail ())

(rule (inv a b 0 n))

(rule (=> (and (inv a b i n) (< i n) (= n1 n) (= (store b i (select a i)) b1) (= i1 (+ i 1))) (inv a b1 i1 n1)))

(rule (=> (and (inv a b i n) (>= i n) (< 0 i1) (< i1 n) (not (= (select a i1) (select b i1)))) fail))

(query fail)
