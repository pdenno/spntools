(ns gov.nist.spntools-test
  (:require [clojure.test :refer :all]
            [gov.nist.spntools :refer :all]
            [gov.nist.spntools.util.pnml :refer :all]
            [gov.nist.spntools.util.utils :refer :all]))

(deftest join-2-test
  (testing "small join reduction"
    (let [j2 (gspn2spn (read-pnml "data/join2.xml"))]
      (is (= (count (:arcs j2)) 18))
      (is (= (count (:transitions j2)) 5))
      (is (= (count (:places j2)) 4)))))

(deftest join-3-test
  (testing "medium join reduction"
    (let [j3 (gspn2spn (read-pnml "data/join3.xml"))]
      (is (= (count (:arcs j3)) 68))
      (is (= (count (:transitions j3)) 13))
      (is (= (count (:places j3)) 5)))))

(deftest join2-graph-test
  (testing "join graph equality"
    (let [result (as-> (gspn2spn (read-pnml "data/join2.xml")) ?pn
                   (assoc ?pn :places (set (:places ?pn)))
                   (assoc ?pn :transitions (set (:transitions ?pn)))
                   (assoc ?pn :arcs (set (:arcs ?pn))))]
      (is (= result
             {:places
              #{{:name :P1, :pid 1, :initial-marking 0}
                {:name :P2, :pid 2, :initial-marking 0}
                {:name :Pjoin, :pid 3, :initial-marking 0}
                {:name :Pstart, :pid 4, :initial-marking 2}},
              :transitions
              #{{:name :Treturn, :tid 4, :type :exponential, :rate 1.0}
                {:name :P1-first, :tid 5, :type :exponential, :rate 1.0}
                {:name :P1-last, :tid 6, :type :exponential, :rate 1.0}
                {:name :P2-first, :tid 7, :type :exponential, :rate 1.0}
                {:name :P2-last, :tid 8, :type :exponential, :rate 1.0}},
              :arcs
              #{{:aid 6, :source :Pjoin, :target :Treturn, :type :normal, :multiplicity 1}
                {:aid 11, :source :Treturn, :target :Pstart, :type :normal, :multiplicity 2}
                {:aid 12, :source :Pstart, :target :P1-first, :type :normal, :multiplicity 1}
                {:aid 13, :source :P1, :target :P1-first, :type :inhibitor, :multiplicity 1}
                {:aid 14, :source :P1-first, :target :P1, :type :normal, :multiplicity 1}
                {:aid 15, :source :P2, :target :P1-first, :type :inhibitor, :multiplicity 1}
                {:aid 16, :source :Pstart, :target :P1-last, :type :normal, :multiplicity 1}
                {:aid 17, :source :P1, :target :P1-last, :type :inhibitor, :multiplicity 1}
                {:aid 18, :source :P1-last, :target :Pjoin, :type :normal, :multiplicity 1}
                {:aid 19, :source :P2, :target :P1-last, :type :normal, :multiplicity 1}
                {:aid 20, :source :Pstart, :target :P2-first, :type :normal, :multiplicity 1}
                {:aid 21, :source :P2, :target :P2-first, :type :inhibitor, :multiplicity 1}
                {:aid 22, :source :P2-first, :target :P2, :type :normal, :multiplicity 1}
                {:aid 23, :source :P1, :target :P2-first, :type :inhibitor, :multiplicity 1}
                {:aid 24, :source :Pstart, :target :P2-last, :type :normal, :multiplicity 1}
                {:aid 25, :source :P2, :target :P2-last, :type :inhibitor, :multiplicity 1}
                {:aid 26, :source :P2-last, :target :Pjoin, :type :normal, :multiplicity 1}
                {:aid 27, :source :P1, :target :P2-last, :type :normal, :multiplicity 1}}})))))

(defn find-arc-test
  [pn source target]
  (filter #(and (= (:source %) source)
                (= (:target %) target))
          (:arcs pn)))

(defn check-every [pn data]
  (every? (fn [r] r)
          (reduce (fn [result [source target num]]
                    (if (= (count (find-arc-test pn source target)) 1) ; just worked out that way.
                      (conj result true)
                      (do (println "--- Failing:" num  "[" source target "]")
                          (conj result false))))
                  []
                  data)))


;;; Ones with commas are inhibitors
(defn j2-has-arcs-test []    
  (let [j2 (gspn2spn (read-pnml "data/join2.xml"))
        data  [[:Pstart :P1-last 1] [:Pstart :P1-first 2] [:Pstart :P2-first 3] [:Pstart :P2-last 4]
               [:P1-first :P1 5]  [:P1 :P1-first, 6] [:P2 :P1-first 7]  [:P1 :P2-first, 8]  [:P2-first :P2 9]
               [:P2 :P2-first, 10] [:P2 :P1-last 11] [:P1 :P2-last 12] [:P1 :P1-last, 13] [:P2 :P2-last, 14]
               [:P1-last :Pjoin 15]  [:P2-last :Pjoin 16] [:Pjoin :Treturn 17]  [:Treturn :Pstart 18]]]
    (println "Testing" (count data) "arcs")
    (check-every j2 data)))

(defn marsan-one-step-arcs-test []    
  (let [j2 (one-step "data/marsan69.xml")
        data [[:P1 :Tndata 1] [:P3 :Tpar1 6] [:P4 :Tpar2 7] [:P5 :t_syn 10] [:P6 :t_syn 11]
              [:P7 :t_ko 13] [:P7 :t_ok 16] [:P8 :Tcheck 15] [:P9 :Tio 18] [:t_ko :P8 14]
              [:t_ok :P9 17] [:t_syn :P7 12] [:Tio :P1 19] [:Tpar1 :P5 8] [:Tpar2 :P6 9]
              [:Tcheck :P3 4] [:Tcheck :P4 5] [:Tndata :P3 2] [:Tndata :P4 3]]]
    (println "Testing" (count data) "arcs")
    (check-every j2 data)))
    
(defn marsan-two-step-arcs-test []    
  (let [j2 (two-step "data/marsan69.xml")
        data [[:Tio :P1 1] [:P9 :Tio 2]
              [:t_ok :P9 3] [:P7 :t_ok 4] [:P7 :t_ko 5] [:t_ko :P8 6] [:P8 :Tcheck 7] [:Tcheck :P3 8]
              [:Tcheck :P4 9] [:P6-last :P7 10] [:P6-first :P6 11] [:P5 :P6-last 12] [:P5 :P6-first 13]
              [:P6 :P5-first 14] [:P6 :P5-last 15] [:P3 :P5-last 16] [:P3 :P5-first 17]
              [:P4 :P6-first 18] [:P4 :P6-last 19] [:Tndata :P4 20] [:Tndata :P3 21]
              [:P1 :Tndata 22] [:P5-first :P5 23] [:P5-last :P7 24]]]
    (println "Testing" (count data) "arcs")
    (every? (fn [r] r)
            (reduce (fn [result [source target num]]
                      (if (= (count (find-arc-test j2 source target)) 1) ; just worked out that way.
                        (conj result true)
                        (do (println "--- Failing:" num  "[" source target "]")
                            (conj result false))))
                    []
                    data))))

;;; Numbering (third element in the data vector) is on a printout of the diagram somewhere.
(defn j2-weird-arcs-test []
  (let [j2 (gspn2spn (read-pnml "data/join2.xml"))
        data  [[:Pstart :P1-last 1] [:Pstart :P1-first 2] [:Pstart :P2-first 3] [:Pstart :P2-last 4]
               [:P1-first :P1 5]  [:P1 :P1-first, 6] [:P2 :P1-first 7]  [:P1 :P2-first, 8]  [:P2-first :P2 9]
               [:P2 :P2-first, 10] [:P2 :P1-last 11] [:P1 :P2-last 12] [:P1 :P1-last, 13] [:P2 :P2-last, 14]
               [:P1-last :Pjoin 15]  [:P2-last :Pjoin 16] [:Pjoin :Treturn 17]  [:Treturn :Pstart 18]]
        cdata (map (fn [[s t _]] [s t]) data)]
    (remove (fn [a] (some #(= [(:source a) (:target a)] %) cdata)) (:arcs j2))))

(defn marsan-one-step-weird-arcs-test []
  (let [j2 (one-step "data/marsan69.xml")
        data  [[:P1 :Tndata 1] [:P3 :Tpar1 6] [:P4 :Tpar2 7] [:P5 :t_syn 10] [:P6 :t_syn 11]
               [:P7 :t_ko 13] [:P7 :t_ok 16] [:P8 :Tcheck 15] [:P9 :Tio 18] [:t_ko :P8 14]
               [:t_ok :P9 17] [:t_syn :P7 12] [:Tio :P1 19] [:Tpar1 :P5 8] [:Tpar2 :P6 9]
               [:Tcheck :P3 4] [:Tcheck :P4 5] [:Tndata :P3 2] [:Tndata :P4 3]]
        cdata (map (fn [[s t _]] [s t]) data)]
    (remove (fn [a] (some #(= [(:source a) (:target a)] %) cdata)) (:arcs j2))))

(defn marsan-two-step-weird-arcs-test []
  (let [j2 (two-step "data/marsan69.xml")
        data  [[:Tio :P1 1] [:P9 :Tio 2] [:t_ok :P9 3] [:P7 :t_ok 4] [:P7 :t_ko 5]
               [:t_ko :P8 6] [:P8 :Tcheck 7] [:Tcheck :P3 8] [:Tcheck :P4 9] [:P6-last :P7 10]
               [:P6-first :P6 11] [:P5 :P6-last 12] [:P5 :P6-first 13]
               [:P6 :P5-first 14] [:P6 :P5-last 15] [:P3 :P5-last 16] [:P3 :P5-first 17]
               [:P4 :P6-first 18] [:P4 :P6-last 19] [:Tndata :P4 20] [:Tndata :P3 21]
               [:P1 :Tndata 22] [:P5-first :P5 23] [:P5-last :P7 24]]
        cdata (map (fn [[s t _]] [s t]) data)]
    (remove (fn [a] (some #(= [(:source a) (:target a)] %) cdata)) (:arcs j2))))

(deftest find-missing-arcs
  (testing "PNs have all correct arcs"
    (is (j2-has-arcs-test))
    (is (marsan-one-step-arcs-test))))

(deftest find-unwanted-arcs
  (testing "PNs do not have unexpected arcs"
    (is (empty? (j2-weird-arcs-test)))
    (is (empty? (marsan-one-step-weird-arcs-test)))
    (is (empty? (marsan-two-step-weird-arcs-test)))))

(deftest infinitesimal-generator-matrix
  (testing "Marsan section 6.1 example, infinitesimal generator"
    (is (= (pn-Q-matrix (read-pnml "data/m6.xml")
                        :force-places [:Pact1 :Preq1 :Pacc1 :Pidle :Pact2 :Preq2 :Pacc2]
                        :force-markings [[1 0 0 1 1 0 0]
                                         [0 1 0 1 1 0 0]
                                         [0 0 1 0 1 0 0]
                                         [0 0 1 0 0 1 0]
                                         [0 1 0 1 0 1 0]
                                         [1 0 0 1 0 1 0]
                                         [1 0 0 0 0 0 1]
                                         [0 1 0 0 0 0 1]])
           [-3.0    0.0   10.0   0.0    0.0    0.0   5.0   0.0
             1.0 -102.0    0.0   0.0    0.0    0.0   0.0   5.0
             0.0  100.0  -12.0   0.0    0.0    0.0   0.0   0.0
             0.0    0.0    2.0 -10.0  100.0    0.0   0.0   0.0
             0.0    2.0    0.0   0.0 -200.0    1.0   0.0   0.0
             2.0    0.0    0.0  10.0    0.0 -101.0   0.0   0.0
             0.0    0.0    0.0   0.0    0.0  100.0  -6.0   0.0
             0.0    0.0    0.0   0.0  100.0    0.0   1.0  -5.0]))))


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
      
