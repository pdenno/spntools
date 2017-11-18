(ns gov.nist.spntools.util.reach-test
  (:require [clojure.test :refer :all]
            [clojure.core.matrix :as m :refer :all]
            [gov.nist.spntools.core :refer :all]
            [gov.nist.spntools.util.pnml :as pnml :refer (read-pnml)]
            [gov.nist.spntools.util.utils :refer :all]
            [gov.nist.spntools.util.reach :as pnr :refer :all]))

;;; ToDo move other reach tests, current in core-test into here. 

;;; POD This will give a false negative if the marking key changes!
;;;      Marking key should be forced. 
(deftest test-simple-reach
  (testing "whether simple reach calculates the right graph."
    (is (=
         #{{:M [0 0 1 1 0], :fire :m1-complete-job, :Mp [0 1 0 1 0], :rate 0.9}
           {:M [1 1 0 0 1], :fire :m2-start-job, :Mp [0 1 0 1 0], :rate 1.0}
           {:M [1 0 1 0 1], :fire :m1-complete-job, :Mp [1 1 0 0 1], :rate 0.9}
           {:M [0 1 0 1 0], :fire :m1-start-job, :Mp [1 0 1 1 0], :rate 1.0}
           {:M [0 0 1 0 1], :fire :m1-complete-job, :Mp [0 1 0 0 1], :rate 0.9}
           {:M [1 0 1 1 0], :fire :m1-complete-job, :Mp [1 1 0 1 0], :rate 0.9}
           {:M [1 0 1 0 1], :fire :m2-start-job, :Mp [0 0 1 1 0], :rate 1.0}
           {:M [1 0 1 1 0], :fire :m2-complete-job, :Mp [1 0 1 0 1], :rate 1.0}
           {:M [0 1 0 0 1], :fire :m1-start-job, :Mp [1 0 1 0 1], :rate 1.0}
           {:M [1 1 0 1 0], :fire :m2-complete-job, :Mp [1 1 0 0 1], :rate 1.0}
           {:M [0 1 0 1 0], :fire :m2-complete-job, :Mp [0 1 0 0 1], :rate 1.0}
           {:M [0 0 1 1 0], :fire :m2-complete-job, :Mp [0 0 1 0 1], :rate 1.0}}
         (-> "data/m2-inhib-bas.xml"
             pnml/read-pnml
             pnr/renumber-pids
             pnr/simple-reach
             :rgraph
             (->> (map #(dissoc % :rate-fn)))
             set)))))

(deftest reachability-test
  (testing "Reachability graph size"
    (is (= 8 (-> "data/qo10.xml" pnml/read-pnml pnr/reachability :M2Mp count)))))

;;; POD This is failing 2017-09-26. I guess I'm not suprised since it doesn't
;;;     force an ordering on the marking!
#_(deftest distinct-markings
  (testing "markings created by reachability"
    (is (= (set [[1 0 0 1 1 0 0]
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
              (distinct (map :M (:M2Mp ?pn)))))))))

#_(deftest vpaths
  (testing "vpath naviation"
    (let [m (run-ready "data/marsan69-2.xml")]
      (is (= (vanish-paths m [2 0 0 0 0 0 0 0 0] [1 1 0 0 0 0 0 0 0])
             {:new-vpath-rates [{:M [2 0 0 0 0 0 0 0 0],
                                 :fire [:Tndata :t_start],
                                 :Mp [1 0 1 1 0 0 0 0 0],
                                 :rate 1.0, :loop? false}],
              :explored [[2 0 0 0 0 0 0 0 0] [1 1 0 0 0 0 0 0 0] [1 0 1 1 0 0 0 0 0]],
              :paths nil,
              :new-St [[1 0 1 1 0 0 0 0 0]]})))
    (let [q (run-ready "data/qorchard.xml")
          paths [[[1 0 0 0 0 0 0 0] [0 1 0 0 0 0 0 0] [0 0 0 1 0 0 0 0] [0 0 0 0 0 1 0 0]]
                 [[1 0 0 0 0 0 0 0] [0 1 0 0 0 0 0 0] [0 0 0 1 0 0 0 0] [0 0 0 0 0 0 1 0]]]]
      (is (= (terminate-vpaths q paths)
             (list {:M [1 0 0 0 0 0 0 0], :fire [:T1 :t1-3 :t3-5], :Mp :NA, :rate :NA, :loop? true}
                   {:M [1 0 0 0 0 0 0 0], :fire [:T1 :t1-3 :t3-6], :Mp :NA, :rate :NA, :loop? true})))
      (is (= (terminating-tangibles q [1 0 0 0 0 0 0 0])
             {:root [1 0 0 0 0 0 0 0],
              :terms ([0 0 0 0 0 0 0 1] [0 0 0 0 0 0 1 0] [0 0 0 0 1 0 0 0]),
              :explored
              [{:M [1 0 0 0 0 0 0 0]}
               {:M [1 0 0 0 0 0 0 0], :fire :T1, :Mp [0 1 0 0 0 0 0 0], :rate 5.0}
               {:M [1 0 0 0 0 0 0 0], :fire :T2, :Mp [0 0 1 0 0 0 0 0], :rate 3.0}
               {:M [0 1 0 0 0 0 0 0], :fire :t1-3, :Mp [0 0 0 1 0 0 0 0], :rate 1.0}
               {:M [0 0 0 1 0 0 0 0], :fire :t3-5, :Mp [0 0 0 0 0 1 0 0], :rate 0.5}
               {:M [0 0 0 1 0 0 0 0], :fire :t3-6, :Mp [0 0 0 0 0 0 1 0], :rate 0.5}
               {:M [0 0 0 0 0 1 0 0], :fire :t5-2, :Mp [0 1 0 0 0 0 0 0], :rate 0.4}
               {:M [0 0 0 0 0 1 0 0], :fire :t5-7, :Mp [0 0 0 0 0 0 0 1], :rate 0.6}
               {:M [0 0 1 0 0 0 0 0], :fire :t2-3, :Mp [0 0 0 1 0 0 0 0], :rate 0.4}
               {:M [0 0 1 0 0 0 0 0], :fire :t2-4, :Mp [0 0 0 0 1 0 0 0], :rate 0.6}]}))
      (is (every? (fn [[correct mine]] (=* correct mine) 0.0001)
                  (map #(list %1 %2)
                       [2.325,3.875,1.8]
                       (:loop-rates (vanish-paths q [1 0 0 0 0 0 0 0] [0 1 0 0 0 0 0 0]))))))))
        
;;;========================================================
;;; Infinitesimal Generator
;;;========================================================
(deftest infinitesimal-generator-matrix
  (testing "Marsan section 6.1 example, infinitesimal generator"
    (is (= (-> (pnml/read-pnml "data/m6.xml")
               (pnml/reorder-places [:Pact1 :Preq1 :Pacc1 :Pidle :Pact2 :Preq2 :Pacc2])
               (pnr/reachability)
               (Q-matrix :force-ordering
                         [[1 0 0 1 1 0 0]
                          [0 1 0 1 1 0 0]
                          [0 0 1 0 1 0 0]
                          [0 0 1 0 0 1 0]
                          [0 1 0 1 0 1 0]
                          [1 0 0 1 0 1 0]
                          [1 0 0 0 0 0 1]
                          [0 1 0 0 0 0 1]])
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
