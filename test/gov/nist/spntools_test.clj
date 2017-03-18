(ns gov.nist.spntools-test
  (:require [clojure.test :refer :all]
            [gov.nist.spntools.core :refer :all]
            [gov.nist.spntools.util.pnml :refer :all]
            [gov.nist.spntools.util.utils :refer :all]
            [gov.nist.spntools.util.reach :refer :all]))

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
    (let [result (gspn2spn (read-pnml "data/join2.xml"))]
      (is (= (set (:places result))
             #{{:name :P1, :pid 1, :initial-marking 0}
               {:name :P2, :pid 2, :initial-marking 0}
               {:name :Pjoin, :pid 3, :initial-marking 0}
               {:name :Pstart, :pid 4, :initial-marking 2}}))
      (is (= (set (:transitions result))
             #{{:name :Treturn, :tid 8, :type :exponential, :rate 1.0}
               {:name :IMM-P1-first, :tid 9, :type :exponential, :rate 1.0}
               {:name :IMM-P1-last, :tid 10, :type :exponential, :rate 1.0}
               {:name :IMM-P2-first, :tid 11, :type :exponential, :rate 1.0}
               {:name :IMM-P2-last, :tid 12, :type :exponential, :rate 1.0}}))
      (is (= (set (:arcs result))
             #{{:aid 14, :source :Pjoin, :target :Treturn, :name :aa-14, :type :normal, :multiplicity 1}
               {:aid 19, :source :Treturn, :target :Pstart, :name :aa-19, :type :normal, :multiplicity 2}
               {:aid 20, :source :Pstart, :target :IMM-P1-first, :name :aa-20, :type :normal, :multiplicity 1, :debug :receive-tops}
               {:aid 21, :source :IMM-P1-first, :target :P1, :name :aa-21, :type :normal, :multiplicity 1, :debug :psv-trans&places}
               {:aid 22, :source :P1, :target :IMM-P1-first, :name :aa-22, :type :inhibitor, :multiplicity 1, :debug :psv-trans&places}
               {:aid 23, :source :P2, :target :IMM-P1-first, :name :aa-23, :type :inhibitor, :multiplicity 1, :debug :receive-inhibitors}
               {:aid 24, :source :Pstart, :target :IMM-P1-last, :name :aa-24, :type :normal, :multiplicity 1, :debug :receive-tops}
               {:aid 25, :source :IMM-P1-last, :target :Pjoin, :name :aa-25, :type :normal, :multiplicity 1, :debug :send-activators}
               {:aid 26, :source :P1, :target :IMM-P1-last, :name :aa-26, :type :inhibitor, :multiplicity 1, :debug :receive-inhibitors}
               {:aid 27, :source :P2, :target :IMM-P1-last, :name :aa-27, :type :normal, :multiplicity 1, :debug :receive-activators}
               {:aid 28, :source :Pstart, :target :IMM-P2-first, :name :aa-28, :type :normal, :multiplicity 1, :debug :receive-tops}
               {:aid 29, :source :IMM-P2-first, :target :P2, :name :aa-29, :type :normal, :multiplicity 1, :debug :psv-trans&places}
               {:aid 30, :source :P2, :target :IMM-P2-first, :name :aa-30, :type :inhibitor, :multiplicity 1, :debug :psv-trans&places}
               {:aid 31, :source :P1, :target :IMM-P2-first, :name :aa-31, :type :inhibitor, :multiplicity 1, :debug :receive-inhibitors}
               {:aid 32, :source :Pstart, :target :IMM-P2-last, :name :aa-32, :type :normal, :multiplicity 1, :debug :receive-tops}
               {:aid 33, :source :IMM-P2-last, :target :Pjoin, :name :aa-33, :type :normal, :multiplicity 1, :debug :send-activators}
               {:aid 34, :source :P2, :target :IMM-P2-last, :name :aa-34, :type :inhibitor, :multiplicity 1, :debug :receive-inhibitors}
               {:aid 35, :source :P1, :target :IMM-P2-last, :name :aa-35, :type :normal, :multiplicity 1, :debug :receive-activators}})))))



(deftest join3-graph-test
  (testing "join graph equality (join3)"
    (let [result (gspn2spn (read-pnml "data/join3.xml"))]
      (is (= (set (:places result))
             #{{:name :P1, :pid 1, :initial-marking 0}
               {:name :P2, :pid 2, :initial-marking 0}
               {:name :P3, :pid 3, :initial-marking 0}
               {:name :Pjoin, :pid 4, :initial-marking 0}
               {:name :Pstart, :pid 5, :initial-marking 3}}))
      (is (= (set (:transitions result))
             #{{:name :Tassemble, :tid 10, :type :exponential, :rate 1.0}
               {:name :IMM-P1-first, :tid 11, :type :exponential, :rate 1.0}
               {:name :IMM-P1--P3-before, :tid 12, :type :exponential, :rate 1.0}
               {:name :IMM-P1--P2-before, :tid 13, :type :exponential, :rate 1.0}
               {:name :IMM-P1-last, :tid 14, :type :exponential, :rate 1.0}
               {:name :IMM-P3-first, :tid 15, :type :exponential, :rate 1.0}
               {:name :IMM-P3--P1-before, :tid 16, :type :exponential, :rate 1.0}
               {:name :IMM-P3--P2-before, :tid 17, :type :exponential, :rate 1.0}
               {:name :IMM-P3-last, :tid 18, :type :exponential, :rate 1.0}
               {:name :IMM-P2-first, :tid 19, :type :exponential, :rate 1.0}
               {:name :IMM-P2--P1-before, :tid 20, :type :exponential, :rate 1.0}
               {:name :IMM-P2--P3-before, :tid 21, :type :exponential, :rate 1.0}
               {:name :IMM-P2-last, :tid 22, :type :exponential, :rate 1.0}}))
      (is (= (set (:arcs result))
             #{{:aid 18, :source :Pjoin, :target :Tassemble, :name :aa-18, :type :normal, :multiplicity 1}
               {:aid 25, :source :Tassemble, :target :Pstart, :name :aa-25, :type :normal, :multiplicity 3}
               {:aid 26, :source :Pstart, :target :IMM-P1-first, :name :aa-26, :type :normal, :multiplicity 1, :debug :receive-tops}
               {:aid 27, :source :IMM-P1-first, :target :P1, :name :aa-27, :type :normal, :multiplicity 1, :debug :psv-trans&places}
               {:aid 28, :source :P1, :target :IMM-P1-first, :name :aa-28, :type :inhibitor, :multiplicity 1, :debug :psv-trans&places}
               {:aid 29, :source :P3, :target :IMM-P1-first, :name :aa-29, :type :inhibitor, :multiplicity 1, :debug :receive-inhibitors}
               {:aid 30, :source :P2, :target :IMM-P1-first, :name :aa-30, :type :inhibitor, :multiplicity 1, :debug :receive-inhibitors}
               {:aid 31, :source :Pstart, :target :IMM-P1--P3-before, :name :aa-31, :type :normal, :multiplicity 1, :debug :receive-tops}
               {:aid 32, :source :P1, :target :IMM-P1--P3-before, :name :aa-32, :type :inhibitor, :multiplicity 1, :debug :psv-trans&places}
               {:aid 33, :source :IMM-P1--P3-before, :target :P1, :name :aa-33, :type :normal, :multiplicity 1, :debug :send-activators}
               {:aid 34, :source :P2, :target :IMM-P1--P3-before, :name :aa-34, :type :inhibitor, :multiplicity 1, :debug :receive-inhibitors}
               {:aid 35, :source :IMM-P1--P3-before, :target :P3, :name :aa-35, :type :normal, :multiplicity 1, :debug :s&r}
               {:aid 36, :source :P3, :target :IMM-P1--P3-before, :name :aa-36, :type :normal, :multiplicity 1, :debug :s&r}
               {:aid 37, :source :Pstart, :target :IMM-P1--P2-before, :name :aa-37, :type :normal, :multiplicity 1, :debug :receive-tops}
               {:aid 38, :source :P1, :target :IMM-P1--P2-before, :name :aa-38, :type :inhibitor, :multiplicity 1, :debug :psv-trans&places}
               {:aid 39, :source :IMM-P1--P2-before, :target :P1, :name :aa-39, :type :normal, :multiplicity 1, :debug :send-activators}
               {:aid 40, :source :P3, :target :IMM-P1--P2-before, :name :aa-40, :type :inhibitor, :multiplicity 1, :debug :receive-inhibitors}
               {:aid 41, :source :IMM-P1--P2-before, :target :P2, :name :aa-41, :type :normal, :multiplicity 1, :debug :s&r}
               {:aid 42, :source :P2, :target :IMM-P1--P2-before, :name :aa-42, :type :normal, :multiplicity 1, :debug :s&r}
               {:aid 43, :source :Pstart, :target :IMM-P1-last, :name :aa-43, :type :normal, :multiplicity 1, :debug :receive-tops}
               {:aid 44, :source :IMM-P1-last, :target :Pjoin, :name :aa-44, :type :normal, :multiplicity 1, :debug :send-activators}
               {:aid 45, :source :P1, :target :IMM-P1-last, :name :aa-45, :type :inhibitor, :multiplicity 1, :debug :receive-inhibitors}
               {:aid 46, :source :P3, :target :IMM-P1-last, :name :aa-46, :type :normal, :multiplicity 1, :debug :receive-activators}
               {:aid 47, :source :P2, :target :IMM-P1-last, :name :aa-47, :type :normal, :multiplicity 1, :debug :receive-activators}
               {:aid 48, :source :Pstart, :target :IMM-P3-first, :name :aa-48, :type :normal, :multiplicity 1, :debug :receive-tops}
               {:aid 49, :source :IMM-P3-first, :target :P3, :name :aa-49, :type :normal, :multiplicity 1, :debug :psv-trans&places}
               {:aid 50, :source :P3, :target :IMM-P3-first, :name :aa-50, :type :inhibitor, :multiplicity 1, :debug :psv-trans&places}
               {:aid 51, :source :P1, :target :IMM-P3-first, :name :aa-51, :type :inhibitor, :multiplicity 1, :debug :receive-inhibitors}
               {:aid 52, :source :P2, :target :IMM-P3-first, :name :aa-52, :type :inhibitor, :multiplicity 1, :debug :receive-inhibitors}
               {:aid 53, :source :Pstart, :target :IMM-P3--P1-before, :name :aa-53, :type :normal, :multiplicity 1, :debug :receive-tops}
               {:aid 54, :source :P3, :target :IMM-P3--P1-before, :name :aa-54, :type :inhibitor, :multiplicity 1, :debug :psv-trans&places}
               {:aid 55, :source :IMM-P3--P1-before, :target :P3, :name :aa-55, :type :normal, :multiplicity 1, :debug :send-activators}
               {:aid 56, :source :P2, :target :IMM-P3--P1-before, :name :aa-56, :type :inhibitor, :multiplicity 1, :debug :receive-inhibitors}
               {:aid 57, :source :IMM-P3--P1-before, :target :P1, :name :aa-57, :type :normal, :multiplicity 1, :debug :s&r}
               {:aid 58, :source :P1, :target :IMM-P3--P1-before, :name :aa-58, :type :normal, :multiplicity 1, :debug :s&r}
               {:aid 59, :source :Pstart, :target :IMM-P3--P2-before, :name :aa-59, :type :normal, :multiplicity 1, :debug :receive-tops}
               {:aid 60, :source :P3, :target :IMM-P3--P2-before, :name :aa-60, :type :inhibitor, :multiplicity 1, :debug :psv-trans&places}
               {:aid 61, :source :IMM-P3--P2-before, :target :P3, :name :aa-61, :type :normal, :multiplicity 1, :debug :send-activators}
               {:aid 62, :source :P1, :target :IMM-P3--P2-before, :name :aa-62, :type :inhibitor, :multiplicity 1, :debug :receive-inhibitors}
               {:aid 63, :source :IMM-P3--P2-before, :target :P2, :name :aa-63, :type :normal, :multiplicity 1, :debug :s&r}
               {:aid 64, :source :P2, :target :IMM-P3--P2-before, :name :aa-64, :type :normal, :multiplicity 1, :debug :s&r}
               {:aid 65, :source :Pstart, :target :IMM-P3-last, :name :aa-65, :type :normal, :multiplicity 1, :debug :receive-tops}
               {:aid 66, :source :IMM-P3-last, :target :Pjoin, :name :aa-66, :type :normal, :multiplicity 1, :debug :send-activators}
               {:aid 67, :source :P3, :target :IMM-P3-last, :name :aa-67, :type :inhibitor, :multiplicity 1, :debug :receive-inhibitors}
               {:aid 68, :source :P1, :target :IMM-P3-last, :name :aa-68, :type :normal, :multiplicity 1, :debug :receive-activators}
               {:aid 69, :source :P2, :target :IMM-P3-last, :name :aa-69, :type :normal, :multiplicity 1, :debug :receive-activators}
               {:aid 70, :source :Pstart, :target :IMM-P2-first, :name :aa-70, :type :normal, :multiplicity 1, :debug :receive-tops}
               {:aid 71, :source :IMM-P2-first, :target :P2, :name :aa-71, :type :normal, :multiplicity 1, :debug :psv-trans&places}
               {:aid 72, :source :P2, :target :IMM-P2-first, :name :aa-72, :type :inhibitor, :multiplicity 1, :debug :psv-trans&places}
               {:aid 73, :source :P1, :target :IMM-P2-first, :name :aa-73, :type :inhibitor, :multiplicity 1, :debug :receive-inhibitors}
               {:aid 74, :source :P3, :target :IMM-P2-first, :name :aa-74, :type :inhibitor, :multiplicity 1, :debug :receive-inhibitors}
               {:aid 75, :source :Pstart, :target :IMM-P2--P1-before, :name :aa-75, :type :normal, :multiplicity 1, :debug :receive-tops}
               {:aid 76, :source :P2, :target :IMM-P2--P1-before, :name :aa-76, :type :inhibitor, :multiplicity 1, :debug :psv-trans&places}
               {:aid 77, :source :IMM-P2--P1-before, :target :P2, :name :aa-77, :type :normal, :multiplicity 1, :debug :send-activators}
               {:aid 78, :source :P3, :target :IMM-P2--P1-before, :name :aa-78, :type :inhibitor, :multiplicity 1, :debug :receive-inhibitors}
               {:aid 79, :source :IMM-P2--P1-before, :target :P1, :name :aa-79, :type :normal, :multiplicity 1, :debug :s&r}
               {:aid 80, :source :P1, :target :IMM-P2--P1-before, :name :aa-80, :type :normal, :multiplicity 1, :debug :s&r}
               {:aid 81, :source :Pstart, :target :IMM-P2--P3-before, :name :aa-81, :type :normal, :multiplicity 1, :debug :receive-tops}
               {:aid 82, :source :P2, :target :IMM-P2--P3-before, :name :aa-82, :type :inhibitor, :multiplicity 1, :debug :psv-trans&places}
               {:aid 83, :source :IMM-P2--P3-before, :target :P2, :name :aa-83, :type :normal, :multiplicity 1, :debug :send-activators}
               {:aid 84, :source :P1, :target :IMM-P2--P3-before, :name :aa-84, :type :inhibitor, :multiplicity 1, :debug :receive-inhibitors}
               {:aid 85, :source :IMM-P2--P3-before, :target :P3, :name :aa-85, :type :normal, :multiplicity 1, :debug :s&r}
               {:aid 86, :source :P3, :target :IMM-P2--P3-before, :name :aa-86, :type :normal, :multiplicity 1, :debug :s&r}
               {:aid 87, :source :Pstart, :target :IMM-P2-last, :name :aa-87, :type :normal, :multiplicity 1, :debug :receive-tops}
               {:aid 88, :source :IMM-P2-last, :target :Pjoin, :name :aa-88, :type :normal, :multiplicity 1, :debug :send-activators}
               {:aid 89, :source :P2, :target :IMM-P2-last, :name :aa-89, :type :inhibitor, :multiplicity 1, :debug :receive-inhibitors}
               {:aid 90, :source :P1, :target :IMM-P2-last, :name :aa-90, :type :normal, :multiplicity 1, :debug :receive-activators}
               {:aid 91, :source :P3, :target :IMM-P2-last, :name :aa-91, :type :normal, :multiplicity 1, :debug :receive-activators}})))))


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

;;;==========================================================================
;;; Reachability
;;;==========================================================================
(defn get-misc-arc-count
  [file]
  [(count (:M2Mp (reachability (zero-step file))))
   (count (:M2Mp (reachability (one-step file))))
   (count (:M2Mp (reachability (two-step file))))
   (count (:M2Mp (reachability (full-step file))))])

(deftest reachability-test
  (testing "Reachability graph size"
    (is (= [4 4 4 4]     (get-misc-arc-count "data/simple.xml")))
    (is (= [6 6 5 5]     (get-misc-arc-count "data/join2.xml")))
    (is (= [5 5 5 5]     (get-misc-arc-count "data/join2-reduce.xml")))
    (is (= [14 14 13 13] (get-misc-arc-count "data/join3.xml")))
    (is (= [13 13 13 13] (get-misc-arc-count "data/join3-reduce-v2.xml")))
    (is (= [95 76 59 48] (get-misc-arc-count "data/marsan69.xml")))
    (is (= [14 14 14 14] (get-misc-arc-count "data/m6.xml")))))

;;;==========================================================================
;;; Reduction GSPN to SPN, one-step, two-step and full
;;;==========================================================================

#_(defn marsan-one-step-arcs-test []    
  (let [j2 (one-step "data/marsan69.xml")
        data [[:P1 :Tndata 1] [:P3 :Tpar1 6] [:P4 :Tpar2 7] [:P5 :t_syn 10] [:P6 :t_syn 11]
              [:P7 :t_ko 13] [:P7 :t_ok 16] [:P8 :Tcheck 15] [:P9 :Tio 18] [:t_ko :P8 14]
              [:t_ok :P9 17] [:t_syn :P7 12] [:Tio :P1 19] [:Tpar1 :P5 8] [:Tpar2 :P6 9]
              [:Tcheck :P3 4] [:Tcheck :P4 5] [:Tndata :P3 2] [:Tndata :P4 3]]]
    (println "Testing" (count data) "arcs")
    (check-every j2 data)))
    
#_(defn marsan-two-step-arcs-test []    
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
#_(defn j2-weird-arcs-test []
  (let [j2 (gspn2spn (read-pnml "data/join2.xml"))
        data  [[:Pstart :P1-last 1] [:Pstart :P1-first 2] [:Pstart :P2-first 3] [:Pstart :P2-last 4]
               [:P1-first :P1 5]  [:P1 :P1-first, 6] [:P2 :P1-first 7]  [:P1 :P2-first, 8]  [:P2-first :P2 9]
               [:P2 :P2-first, 10] [:P2 :P1-last 11] [:P1 :P2-last 12] [:P1 :P1-last, 13] [:P2 :P2-last, 14]
               [:P1-last :Pjoin 15]  [:P2-last :Pjoin 16] [:Pjoin :Treturn 17]  [:Treturn :Pstart 18]]
        cdata (map (fn [[s t _]] [s t]) data)]
    (remove (fn [a] (some #(= [(:source a) (:target a)] %) cdata)) (:arcs j2))))

#_(defn marsan-one-step-weird-arcs-test []
  (let [j2 (one-step "data/marsan69.xml")
        data  [[:P1 :Tndata 1] [:P3 :Tpar1 6] [:P4 :Tpar2 7] [:P5 :t_syn 10] [:P6 :t_syn 11]
               [:P7 :t_ko 13] [:P7 :t_ok 16] [:P8 :Tcheck 15] [:P9 :Tio 18] [:t_ko :P8 14]
               [:t_ok :P9 17] [:t_syn :P7 12] [:Tio :P1 19] [:Tpar1 :P5 8] [:Tpar2 :P6 9]
               [:Tcheck :P3 4] [:Tcheck :P4 5] [:Tndata :P3 2] [:Tndata :P4 3]]
        cdata (map (fn [[s t _]] [s t]) data)]
    (remove (fn [a] (some #(= [(:source a) (:target a)] %) cdata)) (:arcs j2))))

#_(defn marsan-two-step-weird-arcs-test []
  (let [j2 (two-step "data/marsan69.xml")
        data  [[:Tio :P1 1] [:P9 :Tio 2] [:t_ok :P9 3] [:P7 :t_ok 4] [:P7 :t_ko 5]
               [:t_ko :P8 6] [:P8 :Tcheck 7] [:Tcheck :P3 8] [:Tcheck :P4 9] [:P6-last :P7 10]
               [:P6-first :P6 11] [:P5 :P6-last 12] [:P5 :P6-first 13]
               [:P6 :P5-first 14] [:P6 :P5-last 15] [:P3 :P5-last 16] [:P3 :P5-first 17]
               [:P4 :P6-first 18] [:P4 :P6-last 19] [:Tndata :P4 20] [:Tndata :P3 21]
               [:P1 :Tndata 22] [:P5-first :P5 23] [:P5-last :P7 24]]
        cdata (map (fn [[s t _]] [s t]) data)]
    (remove (fn [a] (some #(= [(:source a) (:target a)] %) cdata)) (:arcs j2))))

#_(deftest find-missing-arcs
  (testing "PNs have all correct arcs"
    (is (marsan-one-step-arcs-test))))

#_(deftest find-unwanted-arcs
  (testing "PNs do not have unexpected arcs"
    (is (empty? (j2-weird-arcs-test)))
    (is (empty? (marsan-one-step-weird-arcs-test)))
    (is (empty? (marsan-two-step-weird-arcs-test)))))

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
        (as-> (two-step "data/m6.xml") ?pn
          (reorder-places ?pn [:Pact1 :Preq1 :Pacc1 :Pidle :Pact2 :Preq2 :Pacc2])
          (reachability ?pn)
          (distinct (map :M (:M2Mp ?pn))))))))
        
;;;========================================================
;;; Infinitesimal Generator
;;;========================================================
(deftest infinitesimal-generator-matrix
  (testing "Marsan section 6.1 example, infinitesimal generator"
    (is (= (:Q (-> (two-step "data/m6.xml")
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
  (testing "Steady-state properties are consistent/marsan69 (which does 3 kinds of reduction)"
    (let [result (:avg-tokens-on-place (pn-steady-state (read-pnml "data/marsan69.xml")))
          correct {:P1 0.31305 :P3 0.72487 :P4 0.72487 :P5 0.33774 :P6 0.33774 :P8 0.31217 :P9 0.31217}]
      (is (every? (fn [[key val]]
                    (=* val (get correct key) 0.0001)) result)))))

(deftest steady-state-properties-3rd-step-vanishing-place
  (testing "Steady-state properties a case with '3rd-step vanishing place'"
    (let [result (:avg-tokens-on-place (pn-steady-state (read-pnml "data/m612.xml")))
          correct {:P1 0.16667 :P2 0.16667 :P3 0.16667 :Pa 0.5}]
      (is (every? (fn [[key val]]
                    (=* val (get correct key) 0.001)) result)))))

(deftest steady-state-properties-3rd-step-vanishing-place
  (testing "Steady-state properties on a PN that reduces to a self-loop"
    (let [result (:avg-tokens-on-place (pn-steady-state (read-pnml "data/simple-vanish.xml")))
          correct {:P1 1.0}]
      (is (every? (fn [[key val]]
                    (=* val (get correct key) 0.001)) result)))))


(deftest tight-join-first-bind
  (testing "Tight join binding")
  (let [m (read-pnml "data/tight-join.xml")]
        (is (= (as-> (join-binds m (first (find-joins m))) ?b
                 (update ?b :places-in&outs set)
                 (update ?b :places* set)
                 (update ?b :top-arcs set)
                 (update ?b :places-ins set)
                 (update ?b :places-top set)
                 (update ?b :imm-ins set)
                 (update ?b :trans set))
               {:places-in&outs
                #{{:aid 11, :source :m1-complete-job, :target :buffer, :name :aa-11, :type :normal, :multiplicity 1}
                  {:aid 8, :source :buffer, :target :m1-complete-job, :name :aa-8, :type :inhibitor, :multiplicity 1}
                  {:aid 13, :source :m2-busy, :target :m2-complete-job, :name :aa-13, :type :normal, :multiplicity 1}},
                :IMM :m2-start-job,
                :places* #{:m2-starved :buffer},
                :place-bottom-in {:aid 16, :source :m2-start-job, :target :m2-busy, :name :aa-16, :type :normal, :multiplicity 1},
                :top-arcs
                #{{:aid 15, :source :m2-complete-job, :target :m2-starved, :name :aa-15, :type :normal, :multiplicity 1}
                  {:aid 12, :source :m1-complete-job, :target :m1-busy, :name :aa-12, :type :normal, :multiplicity 1}
                  {:aid 10, :source :m1-busy, :target :m1-complete-job, :name :aa-10, :type :normal, :multiplicity 1}
                  {:aid 14, :source :m2-starved, :target :m2-start-job, :name :aa-14, :type :normal, :multiplicity 1}},
                :tight? :m2-busy,
                :places-ins
                #{{:aid 11, :source :m1-complete-job, :target :buffer, :name :aa-11, :type :normal, :multiplicity 1}
                  {:aid 15, :source :m2-complete-job, :target :m2-starved, :name :aa-15, :type :normal, :multiplicity 1}},
                :place-bottom :m2-busy,
                :places-top #{:m2-starved :m1-busy},
                :imm-ins
                #{{:aid 14, :source :m2-starved, :target :m2-start-job, :name :aa-14, :type :normal, :multiplicity 1}
                  {:aid 9, :source :buffer, :target :m2-start-job, :name :aa-9, :type :normal, :multiplicity 1}},
                :trans #{:m1-complete-job :m2-complete-job}}))))

(deftest steady-state-properties-3rd-step-vanishing-place
  (testing "Steady-state properties on a PN that reduces to a self-loop"
    (let [result (:avg-tokens-on-place (pn-steady-state (read-pnml "data/tight-join.xml")))
          correct {:buffer 0.16811 :m1-busy 1 :m2-busy 0.46735 :m2-starved 0.53265 }]
      (is (every? (fn [[key val]]
                    (=* val (get correct key) 0.001)) result)))))









      
