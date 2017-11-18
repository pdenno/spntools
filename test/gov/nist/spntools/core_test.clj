(ns gov.nist.spntools.core-test
  (:require [clojure.test :refer :all]
            [clojure.core.matrix :as m :refer :all]
            [gov.nist.spntools.core :refer :all]
            [gov.nist.spntools.util.pnml :as pnml :refer :all]
            [gov.nist.spntools.util.utils :as pnu :refer :all]
            [gov.nist.spntools.util.reach :as pnr :refer :all]))

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
(defn steady-state-ok?
  [fname correct]
  (let [result (:avg-tokens-on-place (pn-steady-state (read-pnml fname)))]
    (when (contains? result :failure)
      (println ":failure " (:failure result)))
    (if (and (not-empty result)
             (every? (fn [[key val]] (=* val (get correct key) 0.0001))
                     result))
      {:fname fname :ok? true}
      {:fname fname :ok? false})))

(deftest steady-state
  (is (= (steady-state-ok?
          "data/qo10.xml" ; no loop
          {:P1 0.111111, :P2 0.0, :P3 0.0, :P4 0.0, :P5 0.41667, 
           :P6 0.333333, :P7 0.083333,  :P8 0.05556})
         {:fname "data/qo10.xml" :ok? true}))
  (is (= (steady-state-ok?
          "data/qorchard.xml" ; has a loop
          {:P0 0.11111 :P1 0 :P2 0 :P3 0 :P4 0.2 :P5 0
           :P6 0.43056 :P7 0.25833})
         {:fname "data/qorchard.xml" :ok? true}))
  (is (= (steady-state-ok?
          "data/simple.xml"
          {:A 0.33333333333333326, :B 0.6666666666666669})
         {:fname "data/simple.xml" :ok? true}))
  (is (= (steady-state-ok?
          "data/m6.xml"
          {:Pacc1 0.08569697319444844, :Pacc2 0.27730828048945594, :Pact1 0.8569697319444844,
           :Pact2 0.6932707012236401,  :Pidle 0.6369947463160957,  :Preq1 0.0573332948610671,
           :Preq2 0.029421018286903994})
         {:fname "data/m6.xml" :ok? true}))
  (is (= (steady-state-ok?
          "data/join2.xml"
          {:P1 0.2, :P2 0.2, :Pjoin 0.4, :Pstart 0.8})
         {:fname "data/join2.xml" :ok? true}))
  (is (= (steady-state-ok?
          "data/join2-reduce.xml"
          {:P1 0.2, :P2 0.2, :Pjoin 0.4, :Pstart 0.8})
         {:fname "data/join2-reduce.xml" :ok? true}))
  (is (= (steady-state-ok?
          "data/join3.xml"
          {:P1 0.29412 :P2 0.29412 :P3 0.29412 :Pjoin 0.35294 :Pstart 1.05882})
         {:fname "data/join3.xml" :ok? true}))
  (is (= (steady-state-ok?
          "data/join3-reduce-v2.xml"
          {:P1 0.29412 :P2 0.29412 :P3 0.29412 :Pjoin 0.35294 :Pstart 1.05882})
         {:fname "data/join3-reduce-v2.xml" :ok? true}))
  (is (= (steady-state-ok?
          "data/marsan69.xml"
          {:P1 0.16667 :P2 0 :P3 0.33333 :P4 0.33333 :P5 0.16667
           :P6 0.16667 :P7 0 :P8 0.16667 :P9 0.16667})
         {:fname "data/marsan69.xml" :ok? true}))
  (is (= (steady-state-ok?
          "data/marsan69-2.xml"
          {:P1 0.31305114, :P2 0.0, :P3 0.724867, :P4 0.724867, :P5 0.3377425, :P6 0.3377425,
           :P7 0.0, :P8 0.312169, :P9 0.3121693})
         {:fname "data/marsan69-2.xml" :ok? true}))
  (is (= (steady-state-ok?
          "data/m612.xml"
          {:P1 0.16667 :P2 0.16667 :P3 0.16667 :Pa 0.5 :Pb 0.0})
         {:fname "data/m612.xml" :ok? true}))
  #_(is (= (steady-state-ok? ; one tangible, one immediate in series. 
          "data/simple-vanish.xml"
          {:P1 1.0})
         {:fname "data/simple-vanish.xml" :ok? true}))
  (is (= (steady-state-ok? ; test normalizing weights and sojourn in front of immediate.
          "data/weights-P0-2.xml"
          {:P0 0.27118, :P1 0.0, :P2 0.305085, :P3 0.288906, :P4 0.4229584, :P5 0.7118644})
         {:fname "data/weights-P0-2.xml" :ok? true}))
  (is (= (steady-state-ok?
          "data/m2-inhib-bas.xml"
          {:buffer 0.44752 :m1-blocked 0.21198 :m1-busy 0.78802
           :m2-busy 0.70922 :m2-starved 0.29078})
         {:fname "data/m2-inhib-bas.xml" :ok? true}))
  (is (= (steady-state-ok? 
          "data/m3-feeder.xml"
           {:m2-feed-buffer        0.88623
            :m2-blocked            0.00734
            :m2-starved            0.01424
            :subassembly-arrival   1.0,
            :buffer-2              0.02986
            :m3-busy               0.10915
            :m1-busy               0.11605
            :m1-blocked            0.88394
            :m2-busy               0.98575
            :buffer-1              0.97186
            :m3-starved            0.89084})
         {:fname "data/m3-feeder.xml" :ok? true})))
  
  
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

(deftest timeless-trap
  (testing "that timeless traps are identified."
    (is (= :timeless-trap
           (-> "data/2017-05-06-five.xml"
               run-all
               :failure
               :reason)))))

(deftest parametric-Q-matrix
  (testing "that the parametric code works, at least on a PN with no immediate transitions."
    (let [pn (-> (pnml/read-pnml "data/m6.xml")
                 (pnml/reorder-places [:Pact1 :Preq1 :Pacc1 :Pidle :Pact2 :Preq2 :Pacc2])
                 (pnr/reachability)) 
          rate-table (reduce (fn [t e] (assoc t (:name e) (:rate e))) {} (:transitions pn))
          ordering [[1 0 0 1 1 0 0] [0 1 0 1 1 0 0] [0 0 1 0 1 0 0] [0 0 1 0 0 1 0]
                    [0 1 0 1 0 1 0] [1 0 0 1 0 1 0] [1 0 0 0 0 0 1] [0 1 0 0 0 0 1]]]
      (is (= (-> (Q-matrix pn :force-ordering ordering :rates rate-table)
                 :Q
                 m/to-nested-vectors)
             [[-3.0 1.0 0.0 0.0 0.0 2.0 0.0 0.0]
              [0.0 -102.0 100.0 0.0 2.0 0.0 0.0 0.0]
              [10.0 0.0 -12.0 2.0 0.0 0.0 0.0 0.0]
              [0.0 0.0 0.0 -10.0 0.0 10.0 0.0 0.0]
              [0.0 0.0 0.0 100.0 -200.0 0.0 0.0 100.0]
              [0.0 0.0 0.0 0.0 1.0 -101.0 100.0 0.0]
              [5.0 0.0 0.0 0.0 0.0 0.0 -6.0 1.0]
              [0.0 5.0 0.0 0.0 0.0 0.0 0.0 -5.0]]))))
  (testing "that the parametric code works for PNs with vanishing states."
    (let [pn (-> (pnml/read-pnml "data/marsan69.xml")
                 (pnr/reachability))
          rate-table (reduce (fn [t e] (assoc t (:name e) (:rate e))) {} (:transitions pn))]
      (is (= (Q-matrix pn) (Q-matrix pn :rates rate-table))))))

  

    
