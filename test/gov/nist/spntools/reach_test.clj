(ns gov.nist.spntools.reach-test
  (:require [clojure.test :refer :all]
            [gov.nist.spntools.utils :refer :all]
            [gov.nist.spntools.reach :as pnr :refer :all]))

;;;  POD This will give a false negative if the marking key changes!
;;;  Marking key should be forced. Better yet, stop using .xml! Save the EDN. 
(deftest test-simple-reach
  (testing "whether simple reach calculates the right graph."
    (is (=
         #{{:M [0 0 1 1 0], :fire :m1-complete-job, :Mp [0 1 0 1 0], :rate 0.9}
           {:M [1 1 0 0 1], :fire :m2-start-job,    :Mp [0 1 0 1 0], :rate 1.0}
           {:M [1 0 1 0 1], :fire :m1-complete-job, :Mp [1 1 0 0 1], :rate 0.9}
           {:M [0 1 0 1 0], :fire :m1-start-job,    :Mp [1 0 1 1 0], :rate 1.0}
           {:M [0 0 1 0 1], :fire :m1-complete-job, :Mp [0 1 0 0 1], :rate 0.9}
           {:M [1 0 1 1 0], :fire :m1-complete-job, :Mp [1 1 0 1 0], :rate 0.9}
           {:M [1 0 1 0 1], :fire :m2-start-job,    :Mp [0 0 1 1 0], :rate 1.0}
           {:M [1 0 1 1 0], :fire :m2-complete-job, :Mp [1 0 1 0 1], :rate 1.0}
           {:M [0 1 0 0 1], :fire :m1-start-job,    :Mp [1 0 1 0 1], :rate 1.0}
           {:M [1 1 0 1 0], :fire :m2-complete-job, :Mp [1 1 0 0 1], :rate 1.0}
           {:M [0 1 0 1 0], :fire :m2-complete-job, :Mp [0 1 0 0 1], :rate 1.0}
           {:M [0 0 1 1 0], :fire :m2-complete-job, :Mp [0 0 1 0 1], :rate 1.0}}
         (-> "data/m2-inhib-bas.clj"
             load-file
             pnr/renumber-pids
             pnr/simple-reach
             :rgraph
             (->> (map #(dissoc % :rate-fn)))
             set)))))
