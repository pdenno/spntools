(ns gov.nist.spntools-test
  (:require [clojure.test :refer :all]
            [gov.nist.spntools.core :refer :all]
            [gov.nist.spntools.util.pnml :refer :all]
            [gov.nist.spntools.util.utils :refer :all]
            [gov.nist.spntools.util.reach :refer :all]))

;;;==========================================================================
;;; Reachability
;;;==========================================================================
(deftest reachability-test
  (testing "Reachability graph size"
    (is (= 10 (-> "data/qo10.xml" read-pnml reachability :M2Mp count)))))

(deftest distinct-markings
  (testing "markings created by reachability"
    (= (set [[1 0 0 1 1 0 0]
             [0 1 0 1 1 0 0]
             [0 0 1 0 1 0 0]
             [0 0 1 0 0 1 0]
             [0 1 0 1 0 1 0]
             [1 0 0 1 0 1 0]
             [1 0 0 0 0 0 1]
             [0 1 0 0 0 0 1]])
       (set
        (as-> (read-pnml "data/m6.xml") ?pn
          (reachability ?pn)
          (distinct (map :M (:M2Mp ?pn))))))))
        
;;;========================================================
;;; Infinitesimal Generator
;;;========================================================
(deftest infinitesimal-generator-matrix
  (testing "Marsan section 6.1 example, infinitesimal generator"
    (is (= (:Q (-> (read-pnml "data/m6.xml")
                   (reorder-places [:Pact1 :Preq1 :Pacc1 :Pidle :Pact2 :Preq2 :Pacc2])
                   (reachability)
                   (Q-matrix :force-ordering
                             [[1 0 0 1 1 0 0]
                              [0 1 0 1 1 0 0]
                              [0 0 1 0 1 0 0]
                              [0 0 1 0 0 1 0]
                              [0 1 0 1 0 1 0]
                              [1 0 0 1 0 1 0]
                              [1 0 0 0 0 0 1]
                              [0 1 0 0 0 0 1]])))
           [[-3.0 1.0 0.0 0.0 0.0 2.0 0.0 0.0]
            [0.0 -102.0 100.0 0.0 2.0 0.0 0.0 0.0]
            [10.0 0.0 -12.0 2.0 0.0 0.0 0.0 0.0]
            [0.0 0.0 0.0 -10.0 0.0 10.0 0.0 0.0]
            [0.0 0.0 0.0 100.0 -200.0 0.0 0.0 100.0]
            [0.0 0.0 0.0 0.0 1.0 -101.0 100.0 0.0]
            [5.0 0.0 0.0 0.0 0.0 0.0 -6.0 1.0]
            [0.0 5.0 0.0 0.0 0.0 0.0 0.0 -5.0]]))))

#_(deftest gauss-jordan-elimination
  (testing "Gauss-Jordan elimination solution, inverse and determinant"
    (let [result (gj-explicit [[1.0 2.0 3.0] [3.0 2.0 1.0] [2.0 1.0 3.0]] [12.0 24.0 36.0])
          x (:x result)
          ainv (:inv result)
          det (:det result)]
      ;(is (< -11.999 det -12.001)) ; POD needs investigation.
      (is (vec=* x [13.0 -11.0 7.0] 0.0000001))
      (is (vec=* (nth ainv 0) [-5/12  1/4  1/3] 0.0000001))
      (is (vec=* (nth ainv 1) [ 7/12  1/4 -2/3] 0.0000001))
      (is (vec=* (nth ainv 2) [ 1/12 -1/4  1/3] 0.0000001)))))

;;;========================================================
;;; Steady-state properties
;;;========================================================
(deftest steady-state-qo10
  (testing "Steady-state properties qo10.xml"
    (let [result (:avg-tokens-on-place (pn-steady-state (read-pnml "data/qo10.xml")))
          correct  {:P1 0.111111, :P2 0.0, :P3 0.0, :P4 0.0, :P5 0.41667, 
                    :P6 0.333333, :P7 0.083333,  :P8 0.05556}]
      (is (every? (fn [[key val]]
                    (=* val (get correct key) 0.0001)) result)))))

(deftest steady-state-qorchard
  (testing "Steady-state properties qorchard.xml (has a loop)"
    (let [result (:avg-tokens-on-place (pn-steady-state (read-pnml "data/qorchard.xml")))
          correct  {:P1 0.11111, :P2 0.0, :P3 0.0, :P4 0.0, :P5 0.0, :P6 0.2, 
                    :P7 0.258333,:P8 0.4305555}]
      (is (every? (fn [[key val]]
                    (=* val (get correct key) 0.0001)) result)))))

(deftest steady-state-properties-simple
  (testing "Steady-state properties are consistent with findings from other tools"
    (let [result (:avg-tokens-on-place (pn-steady-state (read-pnml "data/simple.xml")))
          correct {:A 0.33333333333333326, :B 0.6666666666666669}]
      (is (every? (fn [[key val]]
                    (=* val (get correct key) 0.0001)) result)))))

(deftest steady-state-properties-m6
  (testing "Steady-state properties are consistent/m6"
    (let [result (:avg-tokens-on-place (pn-steady-state (read-pnml "data/m6.xml")))
          correct {:Pacc1 0.08569697319444844, :Pacc2 0.27730828048945594, :Pact1 0.8569697319444844,
                   :Pact2 0.6932707012236401,  :Pidle 0.6369947463160957,  :Preq1 0.0573332948610671,
                   :Preq2 0.029421018286903994}]
      (is (every? (fn [[key val]]
                    (=* val (get correct key) 0.0001)) result)))))

(deftest steady-state-properties-join2
  (testing "Steady-state properties are consistent/join2"
    (let [result (:avg-tokens-on-place (pn-steady-state (read-pnml "data/join2.xml")))
          correct {:P1 0.2, :P2 0.2, :Pjoin 0.4, :Pstart 0.8}]
      (is (every? (fn [[key val]]
                    (=* val (get correct key) 0.0001)) result)))))

(deftest steady-state-properties-join2-reduced
  (testing "Steady-state properties are consistent/join2-reduce"
    (let [result (:avg-tokens-on-place (pn-steady-state (read-pnml "data/join2-reduce.xml")))
          correct {:P1 0.2, :P2 0.2, :Pjoin 0.4, :Pstart 0.8}]
      (is (every? (fn [[key val]]
                    (=* val (get correct key) 0.0001)) result)))))

(deftest steady-state-properties-join3
  (testing "Steady-state properties are consistent/join3"
    (let [result (:avg-tokens-on-place (pn-steady-state (read-pnml "data/join3.xml")))
          correct {:P1 0.29412 :P2 0.29412 :P3 0.29412 :Pjoin 0.35294 :Pstart 1.05882}]
      (is (every? (fn [[key val]]
                    (=* val (get correct key) 0.0001)) result)))))

(deftest steady-state-properties-join3-reduced
  (testing "Steady-state properties are consistent/join3-reduce"
    (let [result (:avg-tokens-on-place (pn-steady-state (read-pnml "data/join3-reduce-v2.xml")))
          correct {:P1 0.29412 :P2 0.29412 :P3 0.29412 :Pjoin 0.35294 :Pstart 1.05882}]
      (is (every? (fn [[key val]]
                    (=* val (get correct key) 0.0001)) result)))))

(deftest steady-state-properties-marsan
  (testing "Steady-state properties are consistent/marsan69"
    (let [result (:avg-tokens-on-place (pn-steady-state (read-pnml "data/marsan69.xml")))
          correct {:P1 0.31305 :P3 0.72487 :P4 0.72487 :P5 0.33774 :P6 0.33774 :P8 0.31217 :P9 0.31217}]
      (is (every? (fn [[key val]]
                    (=* val (get correct key) 0.0001)) result)))))

(deftest steady-state-properties-m612
  (testing "Steady-state properties m612.xml"
    (let [result (:avg-tokens-on-place (pn-steady-state (read-pnml "data/m612.xml")))
          correct {:P1 0.16667 :P2 0.16667 :P3 0.16667 :Pa 0.5 :Pb 0.0}]
      (is (every? (fn [[key val]]
                    (=* val (get correct key) 0.001)) result)))))

(deftest steady-state-properties-simple-vanish
  (testing "Steady-state properties on a PN that reduces to a self-loop"
    (let [result (:avg-tokens-on-place (pn-steady-state (read-pnml "data/simple-vanish.xml")))
          correct {:P1 1.0}]
      (is (every? (fn [[key val]]
                    (=* val (get correct key) 0.001)) result)))))

;;; On-the-fly reduction -- Don't need all these tests, just documentation for pnr/Q-prime calculation
#_(def tQt [0.0 0.0 0.0])  ; 1->6 1->7 1->8 (need root, need other tangible states)
#_(def tQtv [5.0 3.0 0.0 0.0]) ; 1->2 1->3 1->4 1->5
;;; Pv has i->i. Does that make sense?
#_(def tPv [[0.0,0.0,0.0,1.0],  ; 2->2 2->3 2->4 2->5
          [0.0,0.0,0.0,0.4],  ; 3->2 3->3 3->4 3->5
          [0.4,0.0,0.0,0.0],  ; 4->2 4->3 4->4 4->5
          [0.0,0.0,0.5,0.0]]) ; 5->2 5->3 5->4 5->5

#_(def tPvt [[0.0 0.0 0.0]   ; 2->6 2->7 2->8  (Use name ordering as Qt/Qtv, )
           [0.6 0.0 0.0]   ; 3->6 3->7 3->8
           [0.0 0.6 0.0]   ; 4->6 4->7 4->8
           [0.0 0.0 0.5]]) ; 5->6 5->7 5->8
#_(def tenQt [0.0 0.0 0.0 0.0])
#_(def tenQtv [5.0 3.0 0.0])
#_(def tenPvt [[0.75 0.0 0.0 0.0]   ; 2->5 2->6 2->7 2->8
             [0.0  1.0 0.0 0.0]   ; 3->5 3->6 3->7 3->8
             [0.0 0.0 0.6 0.4]])  ; 4->5 4->6 4->7 4->8
#_(def tenPv [[0.0 0.0 0.25]    ; 2->2 2->3 2->4
            [0.0 0.0 0.0]     ; 3->2 2->3 3->4
            [0.0 0.0 0.0]])   ; 4->2 4->3 4->4

#_(def t13Qt [0.0 0.0])
#_(def t13Qtv [5.0 3.0 0.0 0.0])
;;; Pvt has 'downsteam' transitions from every vanishing. Here just one downstream state.
#_(def t13Pvt [[0.0]      ; 2->6
             [0.6]      ; 3->6
             [0.0]      ; 4->6
             [0.0]])    ; 5->6
#_(def t13Pv [[0.0 0.0 0.0 1.0]
            [0.0 0.0 0.0 0.4]
            [1.0 0.0 0.0 0.0]
            [0.0 0.0 1.0 0.0]])










      
