(ns gov.nist.spntools.util.reach
  (:require [clojure.data.xml :as xml :refer (parse-str)]
            [clojure.pprint :refer (cl-format pprint pp)]
            [gov.nist.spntools.util.utils :refer :all]))

;;; To Do: Implement place capacity restrictions. (maybe)

(defn fireable? 
  "Return true if transition is fireable under the argument marking."
  [pn mark tr-name]
  (let [arcs (arcs-into pn tr-name)]
    (let [arc-groups (group-by :type arcs)
          marking-key (:marking-key pn)]
      (and 
       (every? (fn [ar] (>= (nth mark (.indexOf marking-key (:source ar)))
                            (:multiplicity ar)))
               (:normal arc-groups))
       (every? (fn [ar] (< (nth mark (.indexOf marking-key (:source ar)))
                           (:multiplicity ar)))
               (:inhibitor arc-groups))))))
     
(defn fireables
  "Return a vector of tids that are fireable under the argument marking."
  [pn mark]
  (filter #(fireable? pn mark %) (map :name (:transitions pn))))

;;; POD It seems like this and fireable are doing pretty much the same thing. Wasteful.
(defn mark-at-link-head
  "Return the mark that is at the head of the argument link."
  [pn [mark tr-name]]
   ;(reset! +diag+ (list mark tid))
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

(def ^:dynamic *visited-links* nil)

;;; A links between markings are all the transitions from the source marking.
;;; Uniqueness of the link is specified as the marking at the tail
;;; and the transition taken. Links look like (marking tid). 
;;; The target marking is completely specified by the source and the transition. 
(defn next-markings
  ;; "Return a seq of maps ({:M <mark> :trans <transition that fired> :Mp <new mark>}...)"
  [pn marking]
  (map (fn [l]
         (let [tr (name2obj pn (second l))]
           {:M marking
            :fire (:name tr)
            :Mp (mark-at-link-head pn l)
            :rate (:rate tr)}))
       (filter (fn [link] (not-any? (fn [vis] (= link vis)) @*visited-links*))
               (map (fn [tr-name] (list marking tr-name)) (fireables pn marking)))))

(def +k-bounded+ 10)

(defn reachability-aux
  [pn marking]
  (if (some #(> % +k-bounded+) marking)
    (assoc pn :failure {:reason :not-k-bounded :marking marking})
    (let [nexts (next-markings pn marking)]
      ;(println "Next " (map #(list (:M %) (:fire %)) nexts)) ; POD is :tid helpful? I like :name!
      (swap! *visited-links* into (map #(list (:M %) (:fire %)) nexts)) ; POD looks wasteful
      (as-> pn ?pn
        (update-in ?pn [:reach] into (vec nexts))
        (reduce (fn [pn nx] (reachability-aux pn (:Mp nx)))
                ?pn
                nexts)))))

(declare renumber-pids)
(defn reachability
  "Calculate the reachability of the argument gspn or spn." 
  [pn]
  (binding [*visited-links* (atom [])]
    (let [marking (initial-marking pn)
          pnn (as-> pn ?pn
                (renumber-pids ?pn) ; initial-marking sorts the by pid too. 
                (assoc ?pn :marking-key (:marking-key marking))
                (assoc ?pn :initial-marking (:initial-marking marking)))]
      (as-> pnn ?pn
        (assoc ?pn :reach [])
        (reachability-aux pnn (:initial-marking pnn))
        (update-in ?pn [:reach] vec)
        (let [m  (set (distinct (map #(:M %) (:reach ?pn))))
              mp (set (distinct (map #(:Mp %) (:reach ?pn))))
              m-mp (clojure.set/difference m mp)
              mp-m (clojure.set/difference mp m)]
          (if (and (empty? m-mp) (empty? mp-m))
            ?pn
            (assoc ?pn :failure {:reason :absorbing-states
                                 :data {:m-not-mp m-mp :mp-not-m mp-m}})))
        (if (and (empty? (:reach ?pn)) (not (:failure ?pn)))
          (assoc ?pn :failure {:reason :null-reachability-graph})
          ?pn)))))

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
   Reduction makes this necessary."
  [pn]
  (update pn :places
          (fn [places]
            (let [order (vec (sort #(< (:pid %1) (:pid %2)) places))]
              (reduce (fn [order id]
                        (assoc-in order [id :pid] id))
                      order
                      (range (count order)))))))
  
