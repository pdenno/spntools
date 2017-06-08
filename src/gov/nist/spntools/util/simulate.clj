(ns gov.nist.spntools.util.simulate
  (:require [clojure.pprint :refer (cl-format pprint pp)]
            [gov.nist.spntools.util.reach :as pnr]
            [gov.nist.spntools.util.utils :as pnu]
            [gov.nist.spntools.util.pnml  :as pnml]))

;;; Purpose: Run a PN, producing a log of its execution.

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
;;; In our implementation, we instead keep maps of queues containing tokens. Where we need the ordinary GSPN marking,
;;; we can convert this queue-base marking to it with (map count (queues-marking-order pn)).
;;; The PN is initialized with default-coloured tokens. For example where the ordinary marking might be
;;; [2 0 0 0] ours would be [[{:type :a :id 1} {:type :a :id2}] [] [] []].

;;; POD When I replace next-link with the QPN equivalent, this can go away. 
(defn queues-marking-order
  "Return a vector of queues in the marking order."
  [pn]
  (let [mk (:marking-key pn)
        state (-> pn :sim :state)]
    (vec (map #(% state) mk))))

(def +tkn-id+ (atom 0))
(defn next-id! []
  (swap! +tkn-id+ inc))

(declare sim-effects pick-link sim-place-data step-state move-tokens check-token-flow-balance binding-pairs)
;;; Not yet a stochastic simulation, also need to implement free choice.
;(simulate talking-m2-bas 10)
(defn simulate
  "Run a PN for nsteps"
  [pn nsteps]
  (as-> pn ?pn
    (pnr/renumber-pids ?pn)
    (assoc ?pn
           :sim {:log []
                 :state (zipmap
                         (:marking-key ?pn)
                         (map (fn [n] (vec (repeatedly n (fn [] {:type :a :id (next-id!)}))))
                                  (:initial-marking ?pn)))})
    (reduce (fn [pn _] (sim-effects pn)) ?pn (range nsteps))))

;;; POD: Currently I'm using next-links, because there is only one colour. 

;(sim-effects talking-m2-bas [1 0 1 1 0] lll)
(defn sim-effects
  "Update the PN's :sim with the effects of one step."
  [pn]
  (let [link (pick-link (pnr/next-links pn (vec (map count (queues-marking-order pn)))))]
    (step-state pn link)))

;;; If the change in marking from :M to Mp implies that there is a difference in the number
;;; of tokens on the net, then under this queueing PN model, the net effect of the
;;; elim and intro actions must equal this difference. New tokens are thus added and removed.
;;; If the change in marking from :M to :Mp implies that there is no difference in the number
;;; of tokens, then tokens just move.

;;; Binding makes GP a bit more complex. In GP you can have new tokens springing up / being eliminated
;;; anywhere. I think the need for intro/elim arises out of imbalance at a transition.
;;; Thankfully, there is a constraint propagation task here. When introducing a free choice pick
;;; among binding types, one can push that through the marked graph portion until a
;;; place where there is confluence of types is reached. At that point forward arcs accept a disjunction
;;; of the types in confluence.  When there are additional free choice (like in a buffer) there is the
;;; opportunity to to reuse the old binding types or choose new ones.

;;; BTW, there is no reason why an inhibitor can't have a binding. 

;;; I think the GP convention will have to be that we have to pick some for 
;;; elim/intro and also assign bindings arbitrarily to pairs where transition is
;;; not 1 in 1 out (marked graph). An operator would be to swap bindings (thus "redirect tokens").
;;;  
;;; The mutation for MJP is going to have to be something that clones an entire line!

;;; POD currently I'm ignoring colour; specifically, I'm using next-link and not evaluating bindings.

(defn step-state
  "Update the (-> pn :sim :state) for the effect of firing the argument transition."
  [pn link]
  (let [trans (some #(when (= (:name %) (:fire link)) %) (:transitions pn))
        mkey (:marking-key pn)
        a-in-raw (remove #(= :inhibitor (:type %)) (pnu/arcs-into  pn (:name trans)))
        a-out-raw (pnu/arcs-outof  pn (:name trans))
        a-in   (remove #(contains? (:bind %) :act) a-in-raw)
        a-out  (remove #(contains? (:bind %) :act) a-out-raw)
        a-in-  (filter #(contains? (:bind %) :act) a-in-raw)   ; POD can only add or remove 1. OK?
        a-out+ (filter #(contains? (:bind %) :act) a-out-raw)]
    (as-pn-ok-> pn ?pn
      (check-token-flow-balance ?pn link a-in a-out a-in- a-out+)
      (update-in ?pn [:sim :log] #(conj % ((:fn trans) :bogus))) ; POD :bogus should be activating tokens
      (move-tokens ?pn a-in a-out a-in- a-out+))))

(defn check-token-flow-balance
  [pn link a-in a-out a-in- a-out+]
  (let [diff (map - (:Mp link) (map count (vals (-> pn :sim :state))))
        delta (reduce (fn [sum n] (+ sum n)) 0 diff)]
    (if (not (= delta
                (+ (- (apply + (map :multiplicity a-out))  (apply + (map :multiplicity a-in)))
                   (- (apply + (map :multiplicity a-out+)) (apply + (map :multiplicity a-in-))))))
      (assoc pn :failure {:reason "token flow imbalance" :transition (:target a-in)})
      pn)))

(defn new-token
  "Create a new token as specified in the argument arc."
  [arc]
  (as-> arc ?a (:bind ?a) (dissoc ?a :act) (assoc ?a :id (next-id!))))

(defn move-tokens
  "Return (-> pn :sim :state) updated according to argument arc info which are collections of arcs."
  [pn a-in a-out a-in- a-out+]
  (as-> pn ?pn
    ;; Remove tokens that are being eliminated.
    (reduce (fn [pn arc] (update-in pn [:sim :state (:source arc)] #(vec (next %)))) ?pn a-in-)
    ;; Add tokens that are being introduced
    (reduce (fn [pn arc] (update-in pn [:sim :state (:target arc)] #(conj % (new-token arc)))) ?pn a-out+)
    ;; Move remaining tokens from input places to output places.
    (reduce (fn [pn [in out]]
              (let [tkn (first ((:source in) (-> pn :sim :state)))]
                (as-> pn ?pn2
                  (update-in ?pn2 [:sim :state (:source in)] #(vec (next %)))
                  (update-in ?pn2 [:sim :state (:target out)] #(conj % tkn)))))
            ?pn
            (binding-pairs a-in a-out))))

;;; POD currently expects matching pairs and multiplicity=1
(defn binding-pairs
  "Return pairs of in/out arcs that agree on bindings."
  [ins outs]
  (let [matched (map (fn [i]
                       (first ; POD should only be one. Needs to be checked?
                        (filter (fn [o]
                                  (and (= (set (keys (:bind o))) (set (keys (:bind i))))
                                       (every? #(= (get o %) (get i %)) (keys (:bind i)))))
                                outs)))
                     ins)]
    (map #(vector %1 %2) ins matched)))

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

       
    
    

  
  
        
    
    
    

