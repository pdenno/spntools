(ns gov.nist.spntools.reach-test
  (:require [clojure.test :refer :all]
            [gov.nist.spntools.utils :refer :all]
            [gov.nist.spntools.reach :as pnr :refer :all]))

(defn map-with-set-vals
  "Change the values of the map into sets."
  [m]
  (reduce-kv (fn [accum k v] (assoc accum k (set v)))
             {}
             m))

(def rgraph
   {[0 0 1 1 0] #{[:m2-complete-job [0 0 1 0 1]] [:m1-complete-job [0 1 0 1 0]]},
    [1 1 0 0 1] #{[:m2-start-job [0 1 0 1 0]]},
    [1 0 1 0 1] #{[:m2-start-job [0 0 1 1 0]] [:m1-complete-job [1 1 0 0 1]]},
    [0 1 0 1 0] #{[:m2-complete-job [0 1 0 0 1]] [:m1-start-job [1 0 1 1 0]]},
    [0 0 1 0 1] #{[:m1-complete-job [0 1 0 0 1]]},
    [1 0 1 1 0] #{[:m2-complete-job [1 0 1 0 1]] [:m1-complete-job [1 1 0 1 0]]},
    [0 1 0 0 1] #{[:m1-start-job [1 0 1 0 1]]},
    [1 1 0 1 0] #{[:m2-complete-job [1 1 0 0 1]]}})

;;;  POD This will give a false negative if the marking key changes!
;;;  Marking key should be forced. Better yet, stop using .xml! Save the EDN. 
(deftest test-simple-reach
  (testing "whether simple reach calculates the right graph."
    (is (= rgraph
         (-> "data/tests/m2-inhib-bas.clj"
             load-file
             pnr/renumber-pids
             pnr/simple-reach
             :rgraph
             map-with-set-vals)))))
