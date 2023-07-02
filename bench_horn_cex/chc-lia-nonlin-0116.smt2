;; Original file: sum_2x3_false-unreach-call_true-termination.c.smt2
(set-logic HORN)
(set-info :source "CHC Constraint Logic: QF_LIA
                   Contains non-linear Horn clauses: true")
(declare-fun sum_sumEXIT (Int Int Int Int Int Int Bool) Bool)
(declare-fun sum_sumFINAL (Int Int Int Int Int Int Bool) Bool)
(declare-fun ULTIMATE.start_ULTIMATE.startENTRY (Int Int Int Int Int Int Bool) Bool)
(declare-fun ULTIMATE.start_ULTIMATE.startFINAL (Int Int Int Int Int Int Bool) Bool)
(declare-fun ULTIMATE.start_L11 (Int Int Int Int Int Int Bool) Bool)
(declare-fun ULTIMATE.start_L14 (Int Int Int Int Int Int Bool) Bool)
(declare-fun sum_sumENTRY (Int Int Int Int Int Int Bool) Bool)
(declare-fun ULTIMATE.start_L16 (Int Int Int Int Int Int Bool) Bool)
(declare-fun ULTIMATE.start_L15 (Int Int Int Int Int Int Bool) Bool)
(declare-fun ULTIMATE.start_L14-1 (Int Int Int Int Int Int Bool) Bool)
(declare-fun sum_L4 (Int Int Int Int Int Int Bool) Bool)
(declare-fun sum_L7-1 (Int Int Int Int Int Int Bool) Bool)
(declare-fun sum_L7 (Int Int Int Int Int Int Bool) Bool)
(declare-fun ULTIMATE.start_ULTIMATE.startEXIT (Int Int Int Int Int Int Bool) Bool)
(assert (forall ((hhv_ULTIMATE.start_L14_0_Int Int) (hhv_ULTIMATE.start_L14_1_Int Int) (hhv_ULTIMATE.start_L14_2_Int Int) (hhv_ULTIMATE.start_L14_3_Int Int) (hhv_ULTIMATE.start_L14_4_Int Int) (hhv_ULTIMATE.start_L14_5_Int Int) (hhv_ULTIMATE.start_L14_6_Bool Bool) (hbv_ULTIMATE.start_ULTIMATE.startENTRY_0_Int Int) (hbv_ULTIMATE.start_ULTIMATE.startENTRY_1_Int Int) (hbv_ULTIMATE.start_ULTIMATE.startENTRY_2_Int Int) (hbv_ULTIMATE.start_ULTIMATE.startENTRY_3_Int Int) (hbv_ULTIMATE.start_ULTIMATE.startENTRY_4_Int Int) (hbv_ULTIMATE.start_ULTIMATE.startENTRY_5_Int Int) (hbv_ULTIMATE.start_ULTIMATE.startENTRY_6_Bool Bool)) (=> (and (or hhv_ULTIMATE.start_L14_6_Bool (and (= hhv_ULTIMATE.start_L14_2_Int 2) (= hhv_ULTIMATE.start_L14_4_Int 3))) (ULTIMATE.start_ULTIMATE.startENTRY hbv_ULTIMATE.start_ULTIMATE.startENTRY_0_Int hhv_ULTIMATE.start_L14_1_Int hbv_ULTIMATE.start_ULTIMATE.startENTRY_2_Int hbv_ULTIMATE.start_ULTIMATE.startENTRY_3_Int hbv_ULTIMATE.start_ULTIMATE.startENTRY_4_Int hbv_ULTIMATE.start_ULTIMATE.startENTRY_5_Int hhv_ULTIMATE.start_L14_6_Bool)) (ULTIMATE.start_L14 hhv_ULTIMATE.start_L14_0_Int hhv_ULTIMATE.start_L14_1_Int hhv_ULTIMATE.start_L14_2_Int hhv_ULTIMATE.start_L14_3_Int hhv_ULTIMATE.start_L14_4_Int hhv_ULTIMATE.start_L14_5_Int hhv_ULTIMATE.start_L14_6_Bool))))
(assert (forall ((hhv_ULTIMATE.start_L15_0_Int Int) (hhv_ULTIMATE.start_L15_1_Int Int) (hhv_ULTIMATE.start_L15_2_Int Int) (hhv_ULTIMATE.start_L15_3_Int Int) (hhv_ULTIMATE.start_L15_4_Int Int) (hhv_ULTIMATE.start_L15_5_Int Int) (hhv_ULTIMATE.start_L15_6_Bool Bool) (hbv_ULTIMATE.start_L14-1_0_Int Int) (hbv_ULTIMATE.start_L14-1_1_Int Int) (hbv_ULTIMATE.start_L14-1_2_Int Int) (hbv_ULTIMATE.start_L14-1_3_Int Int) (hbv_ULTIMATE.start_L14-1_4_Int Int) (hbv_ULTIMATE.start_L14-1_5_Int Int) (hbv_ULTIMATE.start_L14-1_6_Bool Bool)) (=> (and (ULTIMATE.start_L14-1 hbv_ULTIMATE.start_L14-1_0_Int hhv_ULTIMATE.start_L15_1_Int hhv_ULTIMATE.start_L15_2_Int hhv_ULTIMATE.start_L15_3_Int hhv_ULTIMATE.start_L15_4_Int hbv_ULTIMATE.start_L14-1_5_Int hhv_ULTIMATE.start_L15_6_Bool) (or hhv_ULTIMATE.start_L15_6_Bool (and (<= hbv_ULTIMATE.start_L14-1_0_Int 2147483647) (= hhv_ULTIMATE.start_L15_5_Int hbv_ULTIMATE.start_L14-1_0_Int) (<= 0 (+ hbv_ULTIMATE.start_L14-1_0_Int 2147483648))))) (ULTIMATE.start_L15 hhv_ULTIMATE.start_L15_0_Int hhv_ULTIMATE.start_L15_1_Int hhv_ULTIMATE.start_L15_2_Int hhv_ULTIMATE.start_L15_3_Int hhv_ULTIMATE.start_L15_4_Int hhv_ULTIMATE.start_L15_5_Int hhv_ULTIMATE.start_L15_6_Bool))))
(assert (forall ((hhv_sum_L4_0_Int Int) (hhv_sum_L4_1_Int Int) (hhv_sum_L4_2_Int Int) (hhv_sum_L4_3_Int Int) (hhv_sum_L4_4_Int Int) (hhv_sum_L4_5_Int Int) (hhv_sum_L4_6_Bool Bool) (hbv_sum_sumENTRY_0_Int Int) (hbv_sum_sumENTRY_1_Int Int) (hbv_sum_sumENTRY_2_Int Int) (hbv_sum_sumENTRY_3_Int Int) (hbv_sum_sumENTRY_4_Int Int) (hbv_sum_sumENTRY_5_Int Int) (hbv_sum_sumENTRY_6_Bool Bool)) (=> (and (sum_sumENTRY hhv_sum_L4_0_Int hhv_sum_L4_1_Int hbv_sum_sumENTRY_2_Int hbv_sum_sumENTRY_3_Int hhv_sum_L4_4_Int hhv_sum_L4_5_Int hhv_sum_L4_6_Bool) (or hhv_sum_L4_6_Bool (and (= hhv_sum_L4_2_Int hhv_sum_L4_5_Int) (= hhv_sum_L4_3_Int hhv_sum_L4_4_Int)))) (sum_L4 hhv_sum_L4_0_Int hhv_sum_L4_1_Int hhv_sum_L4_2_Int hhv_sum_L4_3_Int hhv_sum_L4_4_Int hhv_sum_L4_5_Int hhv_sum_L4_6_Bool))))
(assert (forall ((hhv_ULTIMATE.start_L16_0_Int Int) (hhv_ULTIMATE.start_L16_1_Int Int) (hhv_ULTIMATE.start_L16_2_Int Int) (hhv_ULTIMATE.start_L16_3_Int Int) (hhv_ULTIMATE.start_L16_4_Int Int) (hhv_ULTIMATE.start_L16_5_Int Int) (hhv_ULTIMATE.start_L16_6_Bool Bool) (hbv_ULTIMATE.start_L15_0_Int Int) (hbv_ULTIMATE.start_L15_1_Int Int) (hbv_ULTIMATE.start_L15_2_Int Int) (hbv_ULTIMATE.start_L15_3_Int Int) (hbv_ULTIMATE.start_L15_4_Int Int) (hbv_ULTIMATE.start_L15_5_Int Int) (hbv_ULTIMATE.start_L15_6_Bool Bool)) (=> (and (or hhv_ULTIMATE.start_L16_6_Bool (= hhv_ULTIMATE.start_L16_5_Int (+ hhv_ULTIMATE.start_L16_2_Int hhv_ULTIMATE.start_L16_4_Int))) (ULTIMATE.start_L15 hhv_ULTIMATE.start_L16_0_Int hhv_ULTIMATE.start_L16_1_Int hhv_ULTIMATE.start_L16_2_Int hhv_ULTIMATE.start_L16_3_Int hhv_ULTIMATE.start_L16_4_Int hhv_ULTIMATE.start_L16_5_Int hhv_ULTIMATE.start_L16_6_Bool)) (ULTIMATE.start_L16 hhv_ULTIMATE.start_L16_0_Int hhv_ULTIMATE.start_L16_1_Int hhv_ULTIMATE.start_L16_2_Int hhv_ULTIMATE.start_L16_3_Int hhv_ULTIMATE.start_L16_4_Int hhv_ULTIMATE.start_L16_5_Int hhv_ULTIMATE.start_L16_6_Bool))))
(assert (forall ((hhv_ULTIMATE.start_L11_0_Int Int) (hhv_ULTIMATE.start_L11_1_Int Int) (hhv_ULTIMATE.start_L11_2_Int Int) (hhv_ULTIMATE.start_L11_3_Int Int) (hhv_ULTIMATE.start_L11_4_Int Int) (hhv_ULTIMATE.start_L11_5_Int Int) (hhv_ULTIMATE.start_L11_6_Bool Bool) (hbv_ULTIMATE.start_L15_0_Int Int) (hbv_ULTIMATE.start_L15_1_Int Int) (hbv_ULTIMATE.start_L15_2_Int Int) (hbv_ULTIMATE.start_L15_3_Int Int) (hbv_ULTIMATE.start_L15_4_Int Int) (hbv_ULTIMATE.start_L15_5_Int Int) (hbv_ULTIMATE.start_L15_6_Bool Bool)) (=> (and (ULTIMATE.start_L15 hhv_ULTIMATE.start_L11_0_Int hhv_ULTIMATE.start_L11_1_Int hhv_ULTIMATE.start_L11_2_Int hhv_ULTIMATE.start_L11_3_Int hhv_ULTIMATE.start_L11_4_Int hhv_ULTIMATE.start_L11_5_Int hhv_ULTIMATE.start_L11_6_Bool) (or hhv_ULTIMATE.start_L11_6_Bool (not (= hhv_ULTIMATE.start_L11_5_Int (+ hhv_ULTIMATE.start_L11_4_Int hhv_ULTIMATE.start_L11_2_Int))))) (ULTIMATE.start_L11 hhv_ULTIMATE.start_L11_0_Int hhv_ULTIMATE.start_L11_1_Int hhv_ULTIMATE.start_L11_2_Int hhv_ULTIMATE.start_L11_3_Int hhv_ULTIMATE.start_L11_4_Int hhv_ULTIMATE.start_L11_5_Int hhv_ULTIMATE.start_L11_6_Bool))))
(assert (forall ((hhv_sum_sumFINAL_0_Int Int) (hhv_sum_sumFINAL_1_Int Int) (hhv_sum_sumFINAL_2_Int Int) (hhv_sum_sumFINAL_3_Int Int) (hhv_sum_sumFINAL_4_Int Int) (hhv_sum_sumFINAL_5_Int Int) (hhv_sum_sumFINAL_6_Bool Bool) (hbv_sum_L4_0_Int Int) (hbv_sum_L4_1_Int Int) (hbv_sum_L4_2_Int Int) (hbv_sum_L4_3_Int Int) (hbv_sum_L4_4_Int Int) (hbv_sum_L4_5_Int Int) (hbv_sum_L4_6_Bool Bool)) (=> (and (or (and (= hhv_sum_sumFINAL_0_Int (+ hhv_sum_sumFINAL_2_Int hhv_sum_sumFINAL_3_Int)) (<= hhv_sum_sumFINAL_2_Int 0)) hhv_sum_sumFINAL_6_Bool) (sum_L4 hbv_sum_L4_0_Int hhv_sum_sumFINAL_1_Int hhv_sum_sumFINAL_2_Int hhv_sum_sumFINAL_3_Int hhv_sum_sumFINAL_4_Int hhv_sum_sumFINAL_5_Int hhv_sum_sumFINAL_6_Bool)) (sum_sumFINAL hhv_sum_sumFINAL_0_Int hhv_sum_sumFINAL_1_Int hhv_sum_sumFINAL_2_Int hhv_sum_sumFINAL_3_Int hhv_sum_sumFINAL_4_Int hhv_sum_sumFINAL_5_Int hhv_sum_sumFINAL_6_Bool))))
(assert (forall ((hhv_sum_L7_0_Int Int) (hhv_sum_L7_1_Int Int) (hhv_sum_L7_2_Int Int) (hhv_sum_L7_3_Int Int) (hhv_sum_L7_4_Int Int) (hhv_sum_L7_5_Int Int) (hhv_sum_L7_6_Bool Bool) (hbv_sum_L4_0_Int Int) (hbv_sum_L4_1_Int Int) (hbv_sum_L4_2_Int Int) (hbv_sum_L4_3_Int Int) (hbv_sum_L4_4_Int Int) (hbv_sum_L4_5_Int Int) (hbv_sum_L4_6_Bool Bool)) (=> (and (sum_L4 hhv_sum_L7_0_Int hhv_sum_L7_1_Int hhv_sum_L7_2_Int hhv_sum_L7_3_Int hhv_sum_L7_4_Int hhv_sum_L7_5_Int hhv_sum_L7_6_Bool) (or (not (<= hhv_sum_L7_2_Int 0)) hhv_sum_L7_6_Bool)) (sum_L7 hhv_sum_L7_0_Int hhv_sum_L7_1_Int hhv_sum_L7_2_Int hhv_sum_L7_3_Int hhv_sum_L7_4_Int hhv_sum_L7_5_Int hhv_sum_L7_6_Bool))))
(assert (forall ((hhv_ULTIMATE.start_ULTIMATE.startEXIT_0_Int Int) (hhv_ULTIMATE.start_ULTIMATE.startEXIT_1_Int Int) (hhv_ULTIMATE.start_ULTIMATE.startEXIT_2_Int Int) (hhv_ULTIMATE.start_ULTIMATE.startEXIT_3_Int Int) (hhv_ULTIMATE.start_ULTIMATE.startEXIT_4_Int Int) (hhv_ULTIMATE.start_ULTIMATE.startEXIT_5_Int Int) (hhv_ULTIMATE.start_ULTIMATE.startEXIT_6_Bool Bool) (hbv_ULTIMATE.start_L16_0_Int Int) (hbv_ULTIMATE.start_L16_1_Int Int) (hbv_ULTIMATE.start_L16_2_Int Int) (hbv_ULTIMATE.start_L16_3_Int Int) (hbv_ULTIMATE.start_L16_4_Int Int) (hbv_ULTIMATE.start_L16_5_Int Int) (hbv_ULTIMATE.start_L16_6_Bool Bool)) (=> (and (ULTIMATE.start_L16 hhv_ULTIMATE.start_ULTIMATE.startEXIT_0_Int hhv_ULTIMATE.start_ULTIMATE.startEXIT_1_Int hhv_ULTIMATE.start_ULTIMATE.startEXIT_2_Int hhv_ULTIMATE.start_ULTIMATE.startEXIT_3_Int hhv_ULTIMATE.start_ULTIMATE.startEXIT_4_Int hhv_ULTIMATE.start_ULTIMATE.startEXIT_5_Int hbv_ULTIMATE.start_L16_6_Bool) hhv_ULTIMATE.start_ULTIMATE.startEXIT_6_Bool) (ULTIMATE.start_ULTIMATE.startEXIT hhv_ULTIMATE.start_ULTIMATE.startEXIT_0_Int hhv_ULTIMATE.start_ULTIMATE.startEXIT_1_Int hhv_ULTIMATE.start_ULTIMATE.startEXIT_2_Int hhv_ULTIMATE.start_ULTIMATE.startEXIT_3_Int hhv_ULTIMATE.start_ULTIMATE.startEXIT_4_Int hhv_ULTIMATE.start_ULTIMATE.startEXIT_5_Int hhv_ULTIMATE.start_ULTIMATE.startEXIT_6_Bool))))
(assert (forall ((hhv_ULTIMATE.start_L11_0_Int Int) (hhv_ULTIMATE.start_L11_1_Int Int) (hhv_ULTIMATE.start_L11_2_Int Int) (hhv_ULTIMATE.start_L11_3_Int Int) (hhv_ULTIMATE.start_L11_4_Int Int) (hhv_ULTIMATE.start_L11_5_Int Int) (hhv_ULTIMATE.start_L11_6_Bool Bool) (hbv_ULTIMATE.start_L16_0_Int Int) (hbv_ULTIMATE.start_L16_1_Int Int) (hbv_ULTIMATE.start_L16_2_Int Int) (hbv_ULTIMATE.start_L16_3_Int Int) (hbv_ULTIMATE.start_L16_4_Int Int) (hbv_ULTIMATE.start_L16_5_Int Int) (hbv_ULTIMATE.start_L16_6_Bool Bool)) (=> (and hhv_ULTIMATE.start_L11_6_Bool (ULTIMATE.start_L16 hhv_ULTIMATE.start_L11_0_Int hhv_ULTIMATE.start_L11_1_Int hhv_ULTIMATE.start_L11_2_Int hhv_ULTIMATE.start_L11_3_Int hhv_ULTIMATE.start_L11_4_Int hhv_ULTIMATE.start_L11_5_Int hhv_ULTIMATE.start_L11_6_Bool)) (ULTIMATE.start_L11 hhv_ULTIMATE.start_L11_0_Int hhv_ULTIMATE.start_L11_1_Int hhv_ULTIMATE.start_L11_2_Int hhv_ULTIMATE.start_L11_3_Int hhv_ULTIMATE.start_L11_4_Int hhv_ULTIMATE.start_L11_5_Int hhv_ULTIMATE.start_L11_6_Bool))))
(assert (forall ((hhv_ULTIMATE.start_ULTIMATE.startFINAL_0_Int Int) (hhv_ULTIMATE.start_ULTIMATE.startFINAL_1_Int Int) (hhv_ULTIMATE.start_ULTIMATE.startFINAL_2_Int Int) (hhv_ULTIMATE.start_ULTIMATE.startFINAL_3_Int Int) (hhv_ULTIMATE.start_ULTIMATE.startFINAL_4_Int Int) (hhv_ULTIMATE.start_ULTIMATE.startFINAL_5_Int Int) (hhv_ULTIMATE.start_ULTIMATE.startFINAL_6_Bool Bool) (hbv_ULTIMATE.start_L11_0_Int Int) (hbv_ULTIMATE.start_L11_1_Int Int) (hbv_ULTIMATE.start_L11_2_Int Int) (hbv_ULTIMATE.start_L11_3_Int Int) (hbv_ULTIMATE.start_L11_4_Int Int) (hbv_ULTIMATE.start_L11_5_Int Int) (hbv_ULTIMATE.start_L11_6_Bool Bool)) (=> (and (or hhv_ULTIMATE.start_ULTIMATE.startFINAL_6_Bool (= hhv_ULTIMATE.start_ULTIMATE.startFINAL_1_Int hhv_ULTIMATE.start_ULTIMATE.startFINAL_3_Int)) (ULTIMATE.start_L11 hhv_ULTIMATE.start_ULTIMATE.startFINAL_0_Int hbv_ULTIMATE.start_L11_1_Int hhv_ULTIMATE.start_ULTIMATE.startFINAL_2_Int hhv_ULTIMATE.start_ULTIMATE.startFINAL_3_Int hhv_ULTIMATE.start_ULTIMATE.startFINAL_4_Int hhv_ULTIMATE.start_ULTIMATE.startFINAL_5_Int hhv_ULTIMATE.start_ULTIMATE.startFINAL_6_Bool)) (ULTIMATE.start_ULTIMATE.startFINAL hhv_ULTIMATE.start_ULTIMATE.startFINAL_0_Int hhv_ULTIMATE.start_ULTIMATE.startFINAL_1_Int hhv_ULTIMATE.start_ULTIMATE.startFINAL_2_Int hhv_ULTIMATE.start_ULTIMATE.startFINAL_3_Int hhv_ULTIMATE.start_ULTIMATE.startFINAL_4_Int hhv_ULTIMATE.start_ULTIMATE.startFINAL_5_Int hhv_ULTIMATE.start_ULTIMATE.startFINAL_6_Bool))))
(assert (forall ((hhv_sum_sumEXIT_0_Int Int) (hhv_sum_sumEXIT_1_Int Int) (hhv_sum_sumEXIT_2_Int Int) (hhv_sum_sumEXIT_3_Int Int) (hhv_sum_sumEXIT_4_Int Int) (hhv_sum_sumEXIT_5_Int Int) (hhv_sum_sumEXIT_6_Bool Bool) (hbv_sum_sumFINAL_0_Int Int) (hbv_sum_sumFINAL_1_Int Int) (hbv_sum_sumFINAL_2_Int Int) (hbv_sum_sumFINAL_3_Int Int) (hbv_sum_sumFINAL_4_Int Int) (hbv_sum_sumFINAL_5_Int Int) (hbv_sum_sumFINAL_6_Bool Bool)) (=> (sum_sumFINAL hhv_sum_sumEXIT_0_Int hhv_sum_sumEXIT_1_Int hhv_sum_sumEXIT_2_Int hhv_sum_sumEXIT_3_Int hhv_sum_sumEXIT_4_Int hhv_sum_sumEXIT_5_Int hhv_sum_sumEXIT_6_Bool) (sum_sumEXIT hhv_sum_sumEXIT_0_Int hhv_sum_sumEXIT_1_Int hhv_sum_sumEXIT_2_Int hhv_sum_sumEXIT_3_Int hhv_sum_sumEXIT_4_Int hhv_sum_sumEXIT_5_Int hhv_sum_sumEXIT_6_Bool))))
(assert (forall ((hhv_ULTIMATE.start_ULTIMATE.startEXIT_0_Int Int) (hhv_ULTIMATE.start_ULTIMATE.startEXIT_1_Int Int) (hhv_ULTIMATE.start_ULTIMATE.startEXIT_2_Int Int) (hhv_ULTIMATE.start_ULTIMATE.startEXIT_3_Int Int) (hhv_ULTIMATE.start_ULTIMATE.startEXIT_4_Int Int) (hhv_ULTIMATE.start_ULTIMATE.startEXIT_5_Int Int) (hhv_ULTIMATE.start_ULTIMATE.startEXIT_6_Bool Bool) (hbv_ULTIMATE.start_ULTIMATE.startFINAL_0_Int Int) (hbv_ULTIMATE.start_ULTIMATE.startFINAL_1_Int Int) (hbv_ULTIMATE.start_ULTIMATE.startFINAL_2_Int Int) (hbv_ULTIMATE.start_ULTIMATE.startFINAL_3_Int Int) (hbv_ULTIMATE.start_ULTIMATE.startFINAL_4_Int Int) (hbv_ULTIMATE.start_ULTIMATE.startFINAL_5_Int Int) (hbv_ULTIMATE.start_ULTIMATE.startFINAL_6_Bool Bool)) (=> (ULTIMATE.start_ULTIMATE.startFINAL hhv_ULTIMATE.start_ULTIMATE.startEXIT_0_Int hhv_ULTIMATE.start_ULTIMATE.startEXIT_1_Int hhv_ULTIMATE.start_ULTIMATE.startEXIT_2_Int hhv_ULTIMATE.start_ULTIMATE.startEXIT_3_Int hhv_ULTIMATE.start_ULTIMATE.startEXIT_4_Int hhv_ULTIMATE.start_ULTIMATE.startEXIT_5_Int hhv_ULTIMATE.start_ULTIMATE.startEXIT_6_Bool) (ULTIMATE.start_ULTIMATE.startEXIT hhv_ULTIMATE.start_ULTIMATE.startEXIT_0_Int hhv_ULTIMATE.start_ULTIMATE.startEXIT_1_Int hhv_ULTIMATE.start_ULTIMATE.startEXIT_2_Int hhv_ULTIMATE.start_ULTIMATE.startEXIT_3_Int hhv_ULTIMATE.start_ULTIMATE.startEXIT_4_Int hhv_ULTIMATE.start_ULTIMATE.startEXIT_5_Int hhv_ULTIMATE.start_ULTIMATE.startEXIT_6_Bool))))
(assert (forall ((hhv_ULTIMATE.start_L14-1_0_Int Int) (hhv_ULTIMATE.start_L14-1_1_Int Int) (hhv_ULTIMATE.start_L14-1_2_Int Int) (hhv_ULTIMATE.start_L14-1_3_Int Int) (hhv_ULTIMATE.start_L14-1_4_Int Int) (hhv_ULTIMATE.start_L14-1_5_Int Int) (hhv_ULTIMATE.start_L14-1_6_Bool Bool) (hbv_ULTIMATE.start_L14_0_Int Int) (hbv_ULTIMATE.start_L14_1_Int Int) (hbv_ULTIMATE.start_L14_2_Int Int) (hbv_ULTIMATE.start_L14_3_Int Int) (hbv_ULTIMATE.start_L14_4_Int Int) (hbv_ULTIMATE.start_L14_5_Int Int) (hbv_ULTIMATE.start_L14_6_Bool Bool) (hbv_sum_sumEXIT_0_Int Int) (hbv_sum_sumEXIT_1_Int Int) (hbv_sum_sumEXIT_2_Int Int) (hbv_sum_sumEXIT_3_Int Int) (hbv_sum_sumEXIT_4_Int Int) (hbv_sum_sumEXIT_5_Int Int) (hbv_sum_sumEXIT_6_Bool Bool)) (=> (and (sum_sumEXIT hbv_sum_sumEXIT_0_Int hbv_sum_sumEXIT_1_Int hbv_sum_sumEXIT_2_Int hbv_sum_sumEXIT_3_Int hbv_sum_sumEXIT_4_Int hbv_sum_sumEXIT_5_Int hbv_sum_sumEXIT_6_Bool) (= hhv_ULTIMATE.start_L14-1_0_Int hbv_sum_sumEXIT_0_Int) (ULTIMATE.start_L14 hbv_ULTIMATE.start_L14_0_Int hhv_ULTIMATE.start_L14-1_1_Int hhv_ULTIMATE.start_L14-1_2_Int hhv_ULTIMATE.start_L14-1_3_Int hhv_ULTIMATE.start_L14-1_4_Int hhv_ULTIMATE.start_L14-1_5_Int hbv_ULTIMATE.start_L14_6_Bool) (let ((.cse0 (or hbv_ULTIMATE.start_L14_6_Bool hbv_sum_sumEXIT_6_Bool))) (or (and (not hhv_ULTIMATE.start_L14-1_6_Bool) (not .cse0)) (and .cse0 hhv_ULTIMATE.start_L14-1_6_Bool))) (= hbv_sum_sumEXIT_5_Int hhv_ULTIMATE.start_L14-1_2_Int) (= hbv_sum_sumEXIT_4_Int hhv_ULTIMATE.start_L14-1_4_Int)) (ULTIMATE.start_L14-1 hhv_ULTIMATE.start_L14-1_0_Int hhv_ULTIMATE.start_L14-1_1_Int hhv_ULTIMATE.start_L14-1_2_Int hhv_ULTIMATE.start_L14-1_3_Int hhv_ULTIMATE.start_L14-1_4_Int hhv_ULTIMATE.start_L14-1_5_Int hhv_ULTIMATE.start_L14-1_6_Bool))))
(assert (forall ((hhv_sum_L7-1_0_Int Int) (hhv_sum_L7-1_1_Int Int) (hhv_sum_L7-1_2_Int Int) (hhv_sum_L7-1_3_Int Int) (hhv_sum_L7-1_4_Int Int) (hhv_sum_L7-1_5_Int Int) (hhv_sum_L7-1_6_Bool Bool) (hbv_sum_L7_0_Int Int) (hbv_sum_L7_1_Int Int) (hbv_sum_L7_2_Int Int) (hbv_sum_L7_3_Int Int) (hbv_sum_L7_4_Int Int) (hbv_sum_L7_5_Int Int) (hbv_sum_L7_6_Bool Bool) (hbv_sum_sumEXIT_0_Int Int) (hbv_sum_sumEXIT_1_Int Int) (hbv_sum_sumEXIT_2_Int Int) (hbv_sum_sumEXIT_3_Int Int) (hbv_sum_sumEXIT_4_Int Int) (hbv_sum_sumEXIT_5_Int Int) (hbv_sum_sumEXIT_6_Bool Bool)) (=> (and (sum_sumEXIT hbv_sum_sumEXIT_0_Int hbv_sum_sumEXIT_1_Int hbv_sum_sumEXIT_2_Int hbv_sum_sumEXIT_3_Int hbv_sum_sumEXIT_4_Int hbv_sum_sumEXIT_5_Int hbv_sum_sumEXIT_6_Bool) (sum_L7 hhv_sum_L7-1_0_Int hbv_sum_L7_1_Int hhv_sum_L7-1_2_Int hhv_sum_L7-1_3_Int hhv_sum_L7-1_4_Int hhv_sum_L7-1_5_Int hbv_sum_L7_6_Bool) (let ((.cse0 (or hbv_sum_L7_6_Bool hbv_sum_sumEXIT_6_Bool))) (or (and hhv_sum_L7-1_6_Bool .cse0) (and (not .cse0) (not hhv_sum_L7-1_6_Bool)))) (= hbv_sum_sumEXIT_5_Int (+ hhv_sum_L7-1_2_Int (- 1))) (= hbv_sum_sumEXIT_4_Int (+ hhv_sum_L7-1_3_Int 1)) (= hhv_sum_L7-1_1_Int hbv_sum_sumEXIT_0_Int)) (sum_L7-1 hhv_sum_L7-1_0_Int hhv_sum_L7-1_1_Int hhv_sum_L7-1_2_Int hhv_sum_L7-1_3_Int hhv_sum_L7-1_4_Int hhv_sum_L7-1_5_Int hhv_sum_L7-1_6_Bool))))
(assert (forall ((hhv_sum_sumFINAL_0_Int Int) (hhv_sum_sumFINAL_1_Int Int) (hhv_sum_sumFINAL_2_Int Int) (hhv_sum_sumFINAL_3_Int Int) (hhv_sum_sumFINAL_4_Int Int) (hhv_sum_sumFINAL_5_Int Int) (hhv_sum_sumFINAL_6_Bool Bool) (hbv_sum_L7-1_0_Int Int) (hbv_sum_L7-1_1_Int Int) (hbv_sum_L7-1_2_Int Int) (hbv_sum_L7-1_3_Int Int) (hbv_sum_L7-1_4_Int Int) (hbv_sum_L7-1_5_Int Int) (hbv_sum_L7-1_6_Bool Bool)) (=> (and (or (and (<= hbv_sum_L7-1_1_Int 2147483647) (<= 0 (+ hbv_sum_L7-1_1_Int 2147483648)) (= hhv_sum_sumFINAL_0_Int hbv_sum_L7-1_1_Int)) hhv_sum_sumFINAL_6_Bool) (sum_L7-1 hbv_sum_L7-1_0_Int hbv_sum_L7-1_1_Int hhv_sum_sumFINAL_2_Int hhv_sum_sumFINAL_3_Int hhv_sum_sumFINAL_4_Int hhv_sum_sumFINAL_5_Int hhv_sum_sumFINAL_6_Bool)) (sum_sumFINAL hhv_sum_sumFINAL_0_Int hhv_sum_sumFINAL_1_Int hhv_sum_sumFINAL_2_Int hhv_sum_sumFINAL_3_Int hhv_sum_sumFINAL_4_Int hhv_sum_sumFINAL_5_Int hhv_sum_sumFINAL_6_Bool))))
(assert (forall ((hhv_ULTIMATE.start_ULTIMATE.startENTRY_0_Int Int) (hhv_ULTIMATE.start_ULTIMATE.startENTRY_1_Int Int) (hhv_ULTIMATE.start_ULTIMATE.startENTRY_2_Int Int) (hhv_ULTIMATE.start_ULTIMATE.startENTRY_3_Int Int) (hhv_ULTIMATE.start_ULTIMATE.startENTRY_4_Int Int) (hhv_ULTIMATE.start_ULTIMATE.startENTRY_5_Int Int) (hhv_ULTIMATE.start_ULTIMATE.startENTRY_6_Bool Bool)) (=> (not hhv_ULTIMATE.start_ULTIMATE.startENTRY_6_Bool) (ULTIMATE.start_ULTIMATE.startENTRY hhv_ULTIMATE.start_ULTIMATE.startENTRY_0_Int hhv_ULTIMATE.start_ULTIMATE.startENTRY_1_Int hhv_ULTIMATE.start_ULTIMATE.startENTRY_2_Int hhv_ULTIMATE.start_ULTIMATE.startENTRY_3_Int hhv_ULTIMATE.start_ULTIMATE.startENTRY_4_Int hhv_ULTIMATE.start_ULTIMATE.startENTRY_5_Int hhv_ULTIMATE.start_ULTIMATE.startENTRY_6_Bool))))
(assert (forall ((hhv_sum_sumENTRY_0_Int Int) (hhv_sum_sumENTRY_1_Int Int) (hhv_sum_sumENTRY_2_Int Int) (hhv_sum_sumENTRY_3_Int Int) (hhv_sum_sumENTRY_4_Int Int) (hhv_sum_sumENTRY_5_Int Int) (hhv_sum_sumENTRY_6_Bool Bool)) (=> (not hhv_sum_sumENTRY_6_Bool) (sum_sumENTRY hhv_sum_sumENTRY_0_Int hhv_sum_sumENTRY_1_Int hhv_sum_sumENTRY_2_Int hhv_sum_sumENTRY_3_Int hhv_sum_sumENTRY_4_Int hhv_sum_sumENTRY_5_Int hhv_sum_sumENTRY_6_Bool))))
(assert (forall ((hbv_ULTIMATE.start_ULTIMATE.startEXIT_0_Int Int) (hbv_ULTIMATE.start_ULTIMATE.startEXIT_1_Int Int) (hbv_ULTIMATE.start_ULTIMATE.startEXIT_2_Int Int) (hbv_ULTIMATE.start_ULTIMATE.startEXIT_3_Int Int) (hbv_ULTIMATE.start_ULTIMATE.startEXIT_4_Int Int) (hbv_ULTIMATE.start_ULTIMATE.startEXIT_5_Int Int) (hbv_ULTIMATE.start_ULTIMATE.startEXIT_6_Bool Bool)) (=> (and (ULTIMATE.start_ULTIMATE.startEXIT hbv_ULTIMATE.start_ULTIMATE.startEXIT_0_Int hbv_ULTIMATE.start_ULTIMATE.startEXIT_1_Int hbv_ULTIMATE.start_ULTIMATE.startEXIT_2_Int hbv_ULTIMATE.start_ULTIMATE.startEXIT_3_Int hbv_ULTIMATE.start_ULTIMATE.startEXIT_4_Int hbv_ULTIMATE.start_ULTIMATE.startEXIT_5_Int hbv_ULTIMATE.start_ULTIMATE.startEXIT_6_Bool) hbv_ULTIMATE.start_ULTIMATE.startEXIT_6_Bool) false)))
(check-sat)
