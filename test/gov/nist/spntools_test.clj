(ns gov.nist.spntools-test
  (:require [clojure.test :refer :all]
            [gov.nist.spntools :refer :all]
            [gov.nist.spntools.util.pnml :refer :all]
            [gov.nist.spntools.util.utils :refer :all]))

(deftest read-pnml-1
    (testing "pnml reading"
    (let [pnml (gspn2spn (read-pnml "data/marsan69.xml"))]
      (is (= (count (:arcs pnml)) 28))
      (is (= (count (:transitions pnml)) 9))
      (is (= (count (:places pnml)) 8)))))

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

;;; Needs investigation.
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
               {:aid 13, :source :P1, :target :P1-first, :type :inhibitor, :multiplicity nil}
               {:aid 14, :source :P1-first, :target :P1, :type :normal, :multiplicity 1}
               {:aid 15, :source :P1-first, :target :P2, :type :inhibitor, :multiplicity 1}
               {:aid 16, :source :Pstart, :target :P1-last, :type :normal, :multiplicity 1}
               {:aid 17, :source :P1, :target :P1-last, :type :inhibitor, :multiplicity nil}
               {:aid 18, :source :P1-last, :target :Pjoin, :type :normal, :multiplicity 1}
               {:aid 19, :source :P1-last, :target :P2, :type :normal, :multiplicity 1}
               {:aid 20, :source :Pstart, :target :P2-first, :type :normal, :multiplicity 1}
               {:aid 21, :source :P2, :target :P2-first, :type :inhibitor, :multiplicity nil}
               {:aid 22, :source :P2-first, :target :P2, :type :normal, :multiplicity 1}
               {:aid 23, :source :P2-first, :target :P1, :type :inhibitor, :multiplicity 1}
               {:aid 24, :source :Pstart, :target :P2-last, :type :normal, :multiplicity 1}
               {:aid 25, :source :P2, :target :P2-last, :type :inhibitor, :multiplicity nil}
               {:aid 26, :source :P2-last, :target :Pjoin, :type :normal, :multiplicity 1}
               {:aid 27, :source :P2-last, :target :P1, :type :normal, :multiplicity 1}}})))))


      
          
