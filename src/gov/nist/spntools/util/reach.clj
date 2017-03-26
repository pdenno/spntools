(ns gov.nist.spntools.util.reach
  (:require [clojure.data.xml :as xml :refer (parse-str)]
            [clojure.pprint :refer (cl-format pprint pp)]
            [gov.nist.spntools.util.utils :refer :all]))

;;; To Do: Implement place capacity restrictions. (maybe)
;;;        * Instead of all these +max-rs+ etc. might want a system wide ^:dynamice
;;;          binding of variable values in a map. (Call the current things +default-...)
;;;        * Why am I keeping :Mp and :fire ? Replace links with markings. 

(def +zippy+ (atom nil))

(defn fireable? 
  "Return true if transition is fireable under the argument marking."
  [pn mark tr-name]
  (reset! +zippy+ (list mark tr-name))
  (let [arcs (arcs-into pn tr-name)
        arc-groups (group-by :type arcs)
        marking-key (:marking-key pn)]
    (and 
     (every? (fn [ar] (>= (nth mark (.indexOf marking-key (:source ar)))
                          (:multiplicity ar)))
             (:normal arc-groups))
     (every? (fn [ar] (< (nth mark (.indexOf marking-key (:source ar)))
                         (:multiplicity ar)))
             (:inhibitor arc-groups)))))
     
;;; POD It seems like this and fireable? are so closely related ought to do them together. Wasteful.
(defn mark-at-link-head
  "Return the mark that is at the head of the argument link."
  [pn mark tr-name]
  (as-> mark ?m
    (reduce (fn [mar arc]
              (let [indx (:pid (name2obj pn (:source arc)))] 
                (update mar indx #(- % (:multiplicity arc)))))
            ?m
            (filter #(= (:type %) :normal) (arcs-into pn tr-name)))
    (reduce (fn [mar arc] 
              (let [indx (:pid (name2obj pn (:target arc)))] 
                (update mar indx #(+ % (:multiplicity arc)))))
            ?m ; inhibitors don't exit transitions
            (arcs-outof pn tr-name))))

;;; The target marking is completely specified by the source (marking at tail) and the transition.
(defn next-markings
  "Return a seq of maps ({:M <tail-marking> :trans <transition that fired> :Mp <head-marking>}...)
   which contain the argument state :M and unexplored states, :Mp reachable by firing :trans"
  ([pn marking]
   (next-markings pn marking true))
  ([pn marking check-visited?]
   (map (fn [trn]
          {:M marking
           :fire trn
           :Mp (mark-at-link-head pn marking trn)
           :rate (:rate (name2obj pn trn))})
        (if check-visited?
          (filter (fn [trn] (not-any? (fn [visited] (and (= marking (:M visited))
                                                         (= trn (:fire visited))))
                                      (:explored pn)))
                  (filter #(fireable? pn marking %) (map :name (:transitions pn))))
          (filter #(fireable? pn marking %) (map :name (:transitions pn)))))))
          

(def +k-bounded+ (atom 10)) ; Maybe better than (or addition to) k-bounded would be size of :explored
(def +max-rs+  "reachability set size" (atom 5000)) 
(declare renumber-pids reach-checking)

(defn tanvan
  "Partition markings into {:tangible ... :vanishing ...}"
  [pn markings]
  (let [parts (partition-by #(tangible? pn (:M %)) markings)]
    (if (tangible? pn (:M (first (first parts))))
      {:tangible (vec (first parts))
       :vanishing (map vec (second parts))}
      {:tangible (vec (second parts))
       :vanishing (vec (first parts))})))

(defn initial-tangible-states
  "Return the initial tangible states, give an initial state that might not be tangible."
  [pn]
  (let [im (:initial-marking pn)]
    (if (tangible? pn im)
      (next-markings pn im)
      (throw (ex-info {:in "initial-tangible-states" :reason "NYI"})))))
  
;;; POD should strip it down to just markings, not :M2MP {:M ... :fire ... :mp ...}
(defn reachability
  "Compute the reachability graph (:explored) depth-first starting at the initial marking, 
   removing vanishing states on-the-fly using the algorithm of Knottenbelt, 1996."
  [pn]
  (as-pn-ok-> pn ?pn
    (dissoc ?pn :explored)
    (renumber-pids ?pn)
    (assoc ?pn :explored (vec (initial-tangible-states pn)))
    (assoc ?pn :St (:explored ?pn))
    (assoc ?pn :Sv [])
    (loop [pn ?pn]
      (println "St = " (:St pn))
      ;(println "Sv = " (:Sv pn))
      (as-> pn ?pns
        (if (empty? (:Sv ?pns))
          ?pns
          (let [pn pn #_(-> pn (dissoc :explored))]
            ;; loop to update rates exploring vanishing
            ?pns))
        (cond (empty? (:St ?pns)) ?pns,
              (some #(> % @+k-bounded+) (:Mp (first (:St ?pns)))) ; POD first? sufficient?
              (assoc ?pns :failure {:reason :not-k-bounded :marking (:Mp (first (:St ?pns)))}),
              (> (count (:explored ?pns)) @+max-rs+)
              (assoc ?pns :failure {:reason :exceeds-max-rs :set-size (count (:explored ?pns))}),
              :else
              (let [nexts (next-markings pn (:Mp (first (:St ?pns))))
                    tan-van (tanvan ?pns nexts)]
                (recur
                 (-> ?pns 
                     (update :explored into nexts)
                     (assoc  :St (into (:tangible tan-van) (vec (rest (:St ?pns)))))
                     (assoc  :Sv (into (:vanishing tan-van) (:Sv ?pns)))))))))
    (reach-checking ?pn)))

(defn reach-checking
  "Check for reachability-related errors."
  [pn]
  (let [m  (set (distinct (map #(:M %) (:explored pn))))
        mp (set (distinct (map #(:Mp %) (:explored pn))))
        m-mp (clojure.set/difference m mp)
        mp-m (clojure.set/difference mp m)]
  (as-pn-ok-> pn ?pn
    (if (and (empty? m-mp) (empty? mp-m))
      ?pn
      (assoc ?pn :failure {:reason :absorbing-states
                           :data {:m-not-mp m-mp :mp-not-m mp-m}}))
    (if (> (count (:M2mp pn)) @+max-rs+)
      (assoc pn :failure {:reason :exceeds-max-rs :set-size (count (:explored ?pn))})
      ?pn)
    (if (empty? (:explored ?pn))
      (assoc ?pn :failure {:reason :null-reachability-graph})
      ?pn))))

(defn tangible? [pn mark]
  "Return true if marking M (not a link) is tangible. A marking is vanishing if it
   enables an immediate transitions. "
  (not-any? #(immediate? pn %) (map :fire (next-markings pn mark false))))

(defn tryme []
  (-> "data/knottenbelt.xml"
      gov.nist.spntools.util.pnml/read-pnml
      reachability))

;;; Reachability-specific utilities ---------------------------------------------
(defn markings2source
  "Return source state names and transitions that are sources of the argument marking."
  [mark graph name-map]
  (as-> graph ?g
    (filter #(= (:Mp %) mark) ?g)
    (map #(vector (get name-map (:source %)) (:fire %)) ?g)))

(defn markings2target
  "Return target state names and transitions that are targets of the argument marking."
  [mark graph name-map]
  (as-> graph ?g
    (filter #(= (:M %) mark) ?g)
    (map #(vector (get name-map (:target %)) (:fire %)) ?g)))

;;; Reorganize from individual firings to indexed by state with transitions to and from.
;;; Also, use name-map to rename states (currently markings) to names used in Pipe (S1, S2, etc.).
;;; POD probably can clean this up now that initial-marking returns a map with :marking-key.
(defn pipe-format
  "Reorganize the graph data from a list of transitions to markings with transitions."
  [graph pn name-map]
  (let [init-marking (:initial-marking (initial-marking pn))]
    (as-> graph ?g
      (group-by :source ?g)
      (reduce-kv (fn [m k v]
                   (as-> m ?m
                     (assoc ?m k (reduce (fn [state in]
                                           (as-> state ?s
                                             (assoc ?s :edges-from (markings2source k graph name-map))
                                             (assoc ?s :edges-to   (markings2target k graph name-map))
                                             (assoc ?s :marking k)
                                             (if (= init-marking k) (assoc ?s :initial-marking :true) ?s)
                                             (assoc ?s :type ; vanishing = at least one IMM is enabled.
                                                    (if (some #(immediate? pn (second %)) (:edges-to ?s)) ; POD ??????????
                                                      :vanishing
                                                      :tangible))))
                                         {}
                                         v))
                     (assoc ?m (get name-map k) (get ?m k))
                     (dissoc ?m k)))
                 ?g
                 ?g)
      (into (sorted-map) (zipmap (keys ?g) (vals ?g))))))

(defn renumber-pids
  "Number the pids from 0 so that they can be used as an index into the marker.
   Reduction makes this necessary. ALSO (no really this is the right way) set
   the :marking-key and :initial-marking"
  [pn]
  (as-> pn ?pn
    (update ?pn :places
            (fn [places]
              (let [order (vec (sort #(< (:pid %1) (:pid %2)) places))]
                (reduce (fn [order id]
                          (assoc-in order [id :pid] id))
                        order
                        (range (count order))))))
    (let [im (initial-marking ?pn)]
      (as-> ?pn ?pn2
        (assoc ?pn2 :marking-key (:marking-key im))
        (assoc ?pn2 :initial-marking (:initial-marking im))))))


(defn possible-live? [pn]
  "A Petri net certainly isn't live if it doesn't have a token in some place.
   This can be checked before doing a reachability graph."
  (if (some #(> (:initial-marking %) 0) (:places pn))
    pn
    (assoc pn :failure {:reason :possible-live})))
  
(defn live? [pn]
  "A Petri net is live if all its transitions are live (enabled in some marking)
   Reachability has already been calculated."
  (let [m2mp (:explored pn)]
    (if (every?
         (fn [tr] (some #(= tr (:fire %)) m2mp))
         (map :name (:transitions pn)))
      pn
      (assoc pn :failure {:reason :live?}))))
  
