(ns gov.nist.spntools.util.simulate
  (:require [clojure.pprint :refer (cl-format pprint pp)]
            [gov.nist.spntools.util.reach :as pnr]
            [gov.nist.spntools.util.utils :as pnu :refer (as-pn-ok-> name2obj)]
            [gov.nist.spntools.util.pnml  :as pnml]))

;;; Purpose: Run a PN, producing a log of its execution.

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

(declare sim-effects pick-link sim-place-data step-state move-tokens check-token-flow-balance
         binding-pairs update-log-for-move)
;;; Not yet a stochastic simulation, also need to implement free choice.
;(simulate talking-m2-bas 10)
(defn simulate
  "Run a PN for nsteps"
  [pn nsteps]
  (reset! +tkn-id+ 0)
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
  (let [fire (:fire link)
        mkey (:marking-key pn)
        a-in-raw (remove #(= :inhibitor (:type %)) (pnu/arcs-into pn fire))
        a-out-raw (pnu/arcs-outof pn fire)
        a-in   (remove #(contains? (:bind %) :act) a-in-raw)
        a-out  (remove #(contains? (:bind %) :act) a-out-raw)
        a-in-  (filter #(contains? (:bind %) :act) a-in-raw)   ; POD can only add or remove 1. OK?
        a-out+ (filter #(contains? (:bind %) :act) a-out-raw)]
    (as-pn-ok-> pn ?pn
      (check-token-flow-balance ?pn link a-in a-out a-in- a-out+)
      (assoc-in ?pn [:sim :old-state] (-> ?pn :sim :state))
      (move-tokens ?pn a-in a-out a-in- a-out+)
      (update-log-for-move ?pn fire))))

(defn update-log-for-move
  [pn fire]
  (let [old-state (-> pn :sim :old-state)
        state (-> pn :sim :state)
        old (-> old-state vals flatten set)
        new (-> state vals flatten set)
        added (clojure.set/difference new old)
        removed (clojure.set/difference old new)
        remain (clojure.set/intersection old new)
        find-at (fn [tkn state] (some (fn [[key val]] (when (some #(= % tkn) val) key)) state))
        moved (reduce (fn [mvd stay]
                        (if (= (find-at stay old-state) (find-at stay state))
                          mvd
                          (conj mvd stay)))
                      [] remain)]
    (as-> pn ?pn
      (update-in ?pn [:sim :log] #(conj % ((:fn (name2obj pn fire)) (vec (clojure.set/union added moved)))))
      (reduce (fn [pn rem]
                (update-in pn [:sim :log] #(conj % {:on-act fire :tkn rem :motion :remove})))
              ?pn removed)
      (reduce (fn [pn add]
                (update-in pn [:sim :log] #(conj % {:on-act fire :tkn add :motion :add})))
              ?pn added)
      (reduce (fn [pn mv]
                (update-in pn [:sim :log] #(conj % {:on-act fire :tkn mv :motion :move
                                                    :from (find-at mv (-> pn :sim :old-state))
                                                    :to (find-at mv (-> pn :sim :state))})))
              ?pn moved))))

;;; POD Maybe throw instead of this??? It is a programming mistake. 
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
