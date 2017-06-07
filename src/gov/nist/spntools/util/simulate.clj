(ns gov.nist.spntools.util.simulate
  (:require [clojure.pprint :refer (cl-format pprint pp)]
            [gov.nist.spntools.util.reach :as pnr]
            [gov.nist.spntools.util.utils :as pnu]
            [gov.nist.spntools.util.pnml  :as pnml]))

;;; Purpose: Run a PN, producing a log.

;;; ToDo: Think about how new jobs get defined. (Designate the :aj thing to do it?)
(declare intro elim)

(def talking-m2-bas
  (pnr/renumber-pids 
   {:places                                         
    [{:name :buffer, :pid 1, :initial-tokens 1    }
     {:name :m1-blocked, :pid 2, :initial-tokens 0}
     {:name :m1-busy, :pid 3, :initial-tokens 1   }
     {:name :m2-busy, :pid 4, :initial-tokens 1   }
     {:name :m2-starved, :pid 5, :initial-tokens 0}],
    :transitions
    [{:name :m1-complete-job, :tid 6, :type :exponential, :rate 0.9 :fn (fn [tkn] {:act :bj :j tkn})}
     {:name :m1-start-job, :tid 7, :type :immediate, :rate 1.0      :fn (fn [tkn] {:act :sj :j tkn})}
     {:name :m2-complete-job, :tid 8, :type :exponential, :rate 1.0 :fn (fn [tkn] {:act :ej :j tkn})}
     {:name :m2-start-job, :tid 9, :type :immediate, :rate 1.0      :fn (fn [tkn] {:act :sm :j tkn})}],
    :arcs
    [{:aid 10, :source :buffer, :target :m1-start-job, :name :aa-10, :type :inhibitor, :multiplicity 1 :bind {:type :a}}
     {:aid 11, :source :buffer, :target :m2-start-job, :name :aa-11, :type :normal, :multiplicity 1 :bind {:type :a}}
     {:aid 12, :source :m1-blocked, :target :m1-start-job, :name :aa-12, :type :normal, :multiplicity 1 :bind {:type :a}}
     {:aid 13, :source :m1-busy, :target :m1-complete-job, :name :aa-13, :type :normal, :multiplicity 1 :bind {:type :a}}
     {:aid 14, :source :m1-complete-job, :target :m1-blocked, :name :aa-14, :type :normal, :multiplicity 1 :bind {:type :a}}
     {:aid 15, :source :m1-start-job, :target :buffer, :name :aa-15, :type :normal, :multiplicity 1 :bind {:type :a}}
     {:aid 16, :source :m1-start-job, :target :m1-busy, :name :aa-16, :type :normal, :multiplicity 1
      :bind {:type :a :act :intro}}
     {:aid 17, :source :m2-busy, :target :m2-complete-job, :name :aa-17, :type :normal, :multiplicity 1 :bind {:type :a}}
     {:aid 18, :source :m2-complete-job, :target :m2-starved, :name :aa-18, :type :normal, :multiplicity 1 :bind {:type :a}}
     {:aid 19, :source :m2-start-job, :target :m2-busy, :name :aa-19, :type :normal, :multiplicity 1 :bind {:type :a}}
     {:aid 20, :source :m2-starved, :target :m2-start-job, :name :aa-20, :type :normal, :multiplicity 1
      :bind {:type :a :act :elim}}]}))

;;; In ordinary GSPN code, a marking (:state) is just a vector of integers signifying the tokens on a place.
;;; In our implementation, we keep instead queues of tokens. Where we need the ordinary GSPN form of a marking,
;;; we can convert this marking to it with (map count (-> pn :sim :state)).
;;; The PN is initialized with default-coloured tokens. For example where the ordinary marking might be
;;; [2 0 0 0] ours would be [[{:type :a :id 1} {:type :a :id2}] [] [] []]. 

(def +tkn-id+ (atom 0))
(defn next-id! []
  (swap! +tkn-id+ inc))

(declare sim-effects pick-link sim-place-data step-state move-tokens)
;;; Not yet a stochastic simulation, also need to implement free choice.
;(simulate talking-m2-bas 10)
(defn simulate
  "Run a PN for nsteps"
  [pn nsteps]
  (as-> pn ?pn
    (assoc ?pn
           :sim {:log []
                 :state (vec (map (fn [n] (vec (repeatedly n (fn [] {:type :a :id (next-id!)}))))
                                  (:initial-marking ?pn)))})
    (reduce (fn [pn _] (sim-effects pn)) ?pn (range nsteps))))

;;; POD: Currently I'm using next-links, because there is only one colour. 

;(sim-effects talking-m2-bas [1 0 1 1 0] lll)
(defn sim-effects
  "Update the PN's :sim with the effects of one step."
  [pn]
  (let [link (pick-link (pnr/next-links pn (map count (-> pn :sim :state))))]
    (step-state ?pn link)))



;;; If the change in marking from :M to Mp implies that there is a difference in the number
;;; of tokens on the net, then under this queueing PN model, then the net effect of the
;;; elim and intro actions must equal this difference. New tokens are thus added and removed.
;;; If the change in marking from :M to Mp implies that there is no difference in the number
;;; of tokens, then tokens just move.
;;; [I'm trying to get away without bindings where the flow is obvious. ]  

;;; This isn't going to be good for GP! In GP you can have new tokens springing up / being eliminated
;;; all over the place. I think the convention will have to be that we have to pick some for 
;;; elim/intro and also assign bindings arbitrarily to pairs where transition is
;;; not 1 in 1 out (marked graph). An operator would be to swap bindings (thus "redirect tokens").
;;; Ooooh kaaaay.....
;;; There is a constraint propagation problem happening here. If introduce a free choice pick
;;; among binding types, I can push that through the marked graph portion until I come to a
;;; place where there is confluence of types. At that point forward it accepts a disjunction
;;; When there are additional free choice (like in a buffer) I think it is a matter of splitting
;;; them out. But it could also be to introduce new binding! (That gets weird!)
;;;  
;;; The mutation for MJP is going to have to be something that clones an entire line!

;;; POD currently I'm ignoring colour. 

(defn step-state
  "Update the (-> pn :sim :state) for the effect of firing the argument transition."
  [pn link]
  (let [trans (some #(when (= (:name %) (:fire link)) %) (:transitions pn))
        mkey (:marking-key pn)
        diff (map - (:Mp link) (map count (-> pn :sim state)))
        delta (reduce (fn [sum n] (+ sum n)) 0 diff)
        a-in-raw (remove #(= :inhibitor (:type %)) (pnu/arcs-into  pn (:name trans)))
        a-out-raw (pnu/arcs-outof  pn (:name trans))
        a-in   (remove #(contains? (:bind %) :act) a-in-raw)
        a-out  (remove #(contains? (:bind %) :act) a-out-raw)
        a-in-  (filter #(contains? (:bind %) :act) a-in-raw)   ; POD can only add or remove 1. OK?
        a-out+ (filter #(contains? (:bind %) :act) a-out-raw)]
    (unless (= delta
               (+ (apply + (map :multiplicity a-in))
                  (apply + (map :multiplicity a-in+))
                  (- (apply + (map :multiplicity a-out)))
                  (- (apply + (map :multiplicity a-in-)))))
            (throw (ex-info "token flow imbalance" {:transition (:name trans)})))
    (as-> pn ?pn
      (update-in ?pn [:sim :log] #(conj % ((:fn trans) :bogus))) ; POD :bogus should be activating tokens
      (update-in ?pn [:sim :state] (move-tokens ?pn a-in a-out a-in- a-out+)))))

(defn move-tokens
  "Return (-> pn :sim :state) updated according to argument arc info."
  [pn a-in a-out a-in- a-out+])



(defn sim-place-data
  "Return data [<act> <place> <change>] for the argument (-> pn :sim :state)"
  [pn link]
  (let 
    (filter identity
            (map (fn [place change] ; change here should be 'token-id / job-id' (once I have queues)
                   (cond (= change 0)
                         false
                         (> change 0)
                         [:add place change]
                         :else
                         [:rem place change]))
                 mkey
                 (map - (-> pn :sim :state) (:Mp link))))))

(defn pick-link
  "Return a random link according to the distribution provide by their rates."
  [links]
  (let [r (rand (reduce (fn [sum l] (+ sum (:rate l))) 0.0 links))]
    (loop [dist links
           sum (:rate (first links))]
      (if (> sum r)
        (first dist)
        (recur (rest dist)
               (+ sum (:rate (second dist))))))))

       
    
    

  
  
        
    
    
    

