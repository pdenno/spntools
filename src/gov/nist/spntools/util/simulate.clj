(ns gov.nist.spntools.util.simulate
  (:require [clojure.pprint :refer (cl-format pprint pp)]
            [gov.nist.spntools.util.reach :as pnr :refer (reachability)]
            [gov.nist.spntools.util.utils :refer :all]
            [gov.nist.spntools.util.pnml :refer (read-pnml)]))

;;; Purpose: Run a PN, producing a log.

;;; ToDo: Think about how new jobs get defined. (Designate the :aj thing to do it?)

(def talking-m2-bas
  (pnr/renumber-pids 
   {:places
    [{:name :buffer, :pid 1, :initial-tokens 1      :fn (fn [chg] {:pl :buffer     :change chg})}
     {:name :m1-blocked, :pid 2, :initial-tokens 0  :fn (fn [chg] {:pl :m1-blocked :change chg})}
     {:name :m1-busy, :pid 3, :initial-tokens 1     :fn (fn [chg] {:pl :m1-busy    :change chg})}
     {:name :m2-busy, :pid 4, :initial-tokens 1     :fn (fn [chg] {:pl :m2-busy    :change chg})}
     {:name :m2-starved, :pid 5, :initial-tokens 0  :fn (fn [chg] {:pl :m2-starved :change chg})}],
    :transitions
    [{:name :m1-complete-job, :tid 6, :type :exponential, :rate 0.9 :fn (fn [id] {:act :bj :j id})}
     {:name :m1-start-job, :tid 7, :type :immediate, :rate 1.0      :fn (fn [id] {:act :sj :j id})}
     {:name :m2-complete-job, :tid 8, :type :exponential, :rate 1.0 :fn (fn [id] {:act :sj :j id})}
     {:name :m2-start-job, :tid 9, :type :immediate, :rate 1.0      :fn (fn [id] {:act :sm :j id})}],
    :arcs
    [{:aid 10, :source :buffer, :target :m1-start-job, :name :aa-10, :type :inhibitor, :multiplicity 1}
     {:aid 11, :source :buffer, :target :m2-start-job, :name :aa-11, :type :normal, :multiplicity 1}
     {:aid 12, :source :m1-blocked, :target :m1-start-job, :name :aa-12, :type :normal, :multiplicity 1}
     {:aid 13, :source :m1-busy, :target :m1-complete-job, :name :aa-13, :type :normal, :multiplicity 1}
     {:aid 14, :source :m1-complete-job, :target :m1-blocked, :name :aa-14, :type :normal, :multiplicity 1}
     {:aid 15, :source :m1-start-job, :target :buffer, :name :aa-15, :type :normal, :multiplicity 1}
     {:aid 16, :source :m1-start-job, :target :m1-busy, :name :aa-16, :type :normal, :multiplicity 1}
     {:aid 17, :source :m2-busy, :target :m2-complete-job, :name :aa-17, :type :normal, :multiplicity 1}
     {:aid 18, :source :m2-complete-job, :target :m2-starved, :name :aa-18, :type :normal, :multiplicity 1}
     {:aid 19, :source :m2-start-job, :target :m2-busy, :name :aa-19, :type :normal, :multiplicity 1}
     {:aid 20, :source :m2-starved, :target :m2-start-job, :name :aa-20, :type :normal, :multiplicity 1}]}
   ))

(declare sim-effects)
;;; Not yet a stochastic simulation, also need to implement free choice. 
(defn simulate
  "Run a PN for nsteps"
  [pn nsteps]
  (loop [mark (:initial-marking pn)
         step nsteps
         log []]
    (let [links (pnr/next-links pn mark)
          link (nth links (rand-int (count links))) ; POD NYI
          log (into log (sim-effects pn mark link))]
      (if (> step 0)
        (recur (:Mp link) (dec step) log)
        log))))

;(sim-effects talking-m2-bas [1 0 1 1 0] lll)
(defn sim-effects
  "Return a vector of log messages corresponding to the change in state from mark to (:Mp link)."
  [pn mark link]
  (let [mkey (:marking-key pn)
        t-fn (:fn (some #(when (= (:name %) (:fire link)) %) (:transitions pn)))
        log (vector (t-fn :bog))]
    log))
    
    
    

  
  
        
    
    
    

