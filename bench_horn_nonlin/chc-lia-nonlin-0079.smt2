;; Original file: adr_75.smt2
(set-logic HORN)
(declare-fun |zip$unknown:2| (Int Int) Bool)
(declare-fun |zip$unknown:3| (Int Int Int) Bool)


(assert (forall ((|$alpha-3:n| Int))
  (=> true (|zip$unknown:2| |$alpha-3:n| |$alpha-3:n|))))
(assert (forall ((|$knormal:5| Int)
         (|$alpha-2:y| Int)
         (|$knormal:3| Int)
         (|$alpha-1:x| Int)
         (|$knormal:2| Int)
         (|$knormal:1| Int)
         (|$V-reftype:17| Int)
         (|$knormal:7| Int))
  (let ((a!1 (and (= |$knormal:5| (- |$alpha-2:y| 1))
                  (= |$knormal:3| (- |$alpha-1:x| 1))
                  (= (not (= 0 |$knormal:2|)) (= |$alpha-2:y| 0))
                  (= (not (= 0 |$knormal:1|)) (= |$alpha-1:x| 0))
                  (= |$V-reftype:17| (+ 1 |$knormal:7|))
                  (not (not (= 0 |$knormal:2|)))
                  (not (not (= 0 |$knormal:1|)))
                  (|zip$unknown:3| |$knormal:7|
                                   |$knormal:5|
                                   |$knormal:3|)
                  (|zip$unknown:2| |$alpha-2:y| |$alpha-1:x|)
                  true)))
    (=> a!1
        (|zip$unknown:3| |$V-reftype:17| |$alpha-2:y| |$alpha-1:x|)))))
(assert (forall ((|$knormal:9| Int)
         (|$alpha-2:y| Int)
         (|$knormal:1| Int)
         (|$alpha-1:x| Int)
         (|$V-reftype:11| Int))
  (let ((a!1 (and (= (not (= 0 |$knormal:9|)) (= |$alpha-2:y| 0))
                  (= (not (= 0 |$knormal:1|)) (= |$alpha-1:x| 0))
                  (= |$V-reftype:11| 0)
                  (not (= 0 |$knormal:9|))
                  (not (= 0 |$knormal:1|))
                  (|zip$unknown:2| |$alpha-2:y| |$alpha-1:x|)
                  true)))
    (=> a!1
        (|zip$unknown:3| |$V-reftype:11| |$alpha-2:y| |$alpha-1:x|)))))
(assert (forall ((|$knormal:9| Int)
         (|$alpha-2:y| Int)
         (|$knormal:1| Int)
         (|$alpha-1:x| Int))
  (let ((a!1 (and (= (not (= 0 |$knormal:9|)) (= |$alpha-2:y| 0))
                  (= (not (= 0 |$knormal:1|)) (= |$alpha-1:x| 0))
                  (not (not (= 0 |$knormal:9|)))
                  (not (= 0 |$knormal:1|))
                  (|zip$unknown:2| |$alpha-2:y| |$alpha-1:x|)
                  true)))
    (=> a!1 false))))
(assert (forall ((|$knormal:2| Int)
         (|$alpha-2:y| Int)
         (|$knormal:1| Int)
         (|$alpha-1:x| Int))
  (let ((a!1 (and (= (not (= 0 |$knormal:2|)) (= |$alpha-2:y| 0))
                  (= (not (= 0 |$knormal:1|)) (= |$alpha-1:x| 0))
                  (not (not (= 0 |$knormal:1|)))
                  (not (= 0 |$knormal:2|))
                  (|zip$unknown:2| |$alpha-2:y| |$alpha-1:x|)
                  true)))
    (=> a!1 false))))
(assert (forall ((|$knormal:5| Int)
         (|$alpha-2:y| Int)
         (|$knormal:3| Int)
         (|$alpha-1:x| Int)
         (|$knormal:2| Int)
         (|$knormal:1| Int))
  (let ((a!1 (and (= |$knormal:5| (- |$alpha-2:y| 1))
                  (= |$knormal:3| (- |$alpha-1:x| 1))
                  (= (not (= 0 |$knormal:2|)) (= |$alpha-2:y| 0))
                  (= (not (= 0 |$knormal:1|)) (= |$alpha-1:x| 0))
                  (not (not (= 0 |$knormal:2|)))
                  (not (not (= 0 |$knormal:1|)))
                  (|zip$unknown:2| |$alpha-2:y| |$alpha-1:x|)
                  true
                  (not true))))
    (=> a!1 true))))
(assert (forall ((|$knormal:5| Int)
         (|$alpha-2:y| Int)
         (|$knormal:3| Int)
         (|$alpha-1:x| Int)
         (|$knormal:2| Int)
         (|$knormal:1| Int))
  (let ((a!1 (and (= |$knormal:5| (- |$alpha-2:y| 1))
                  (= |$knormal:3| (- |$alpha-1:x| 1))
                  (= (not (= 0 |$knormal:2|)) (= |$alpha-2:y| 0))
                  (= (not (= 0 |$knormal:1|)) (= |$alpha-1:x| 0))
                  (not (not (= 0 |$knormal:2|)))
                  (not (not (= 0 |$knormal:1|)))
                  (|zip$unknown:2| |$alpha-2:y| |$alpha-1:x|)
                  true)))
    (=> a!1 (|zip$unknown:2| |$knormal:5| |$knormal:3|)))))
(assert (forall ((|$knormal:14| Int) (|$knormal:12| Int) (|$alpha-3:n| Int))
  (let ((a!1 (and (= (not (= 0 |$knormal:14|))
                     (= |$knormal:12| |$alpha-3:n|))
                  (not (not (= 0 |$knormal:14|)))
                  (|zip$unknown:3| |$knormal:12|
                                   |$alpha-3:n|
                                   |$alpha-3:n|))))
    (=> a!1 false))))
(check-sat)