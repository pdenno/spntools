(ns gov.nist.spntools.util.reach
  (:require [clojure.data.xml :as xml :refer (parse-str)]
            [clojure.pprint :refer (cl-format pprint pp)]))

(defn initial-marking
  [pn]
  (vec (map :initial-marking (sort #(< (:pid %1) (:pid %2)) (:places pn)))))

;;; POD maybe memoize to something that doesn't get the pn. 
(defn tid2obj
  [pn tid]
  (some #(when (= (:tid %) tid) %) (:transitions pn)))

(defn pid2obj
  [pn pid]
  (some #(when (= (:pid %) pid) %) (:places pn)))

(defn aid2obj
  [pn aid]
  (some #(when (= (:aid %) aid) %) (:arcs pn)))

(defn arcs-into-trans
  "Return the input arcs to a transition."
  [pn tid]
  (let [tr-name (:name (tid2obj pn tid))]
    (filter #(= (:target %) tr-name) (:arcs pn))))

(defn arcs-outof-trans
  "Return the output arcs of a transition."
  [pn tid]
  (let [tr-name (:name (tid2obj pn tid))]
    (filter #(= (:source %) tr-name) (:arcs pn))))

(defn arcs-outof-place
  "Return the output arcs of a place."
  [pn pl-name]
  (filter #(= (:source %) pl-name) (:arcs pn)))

(defn name2place
  [pn name]
  (some #(when (= name (:name %)) %) (:places pn)))

(defn name2transition
  [pn name]
  (some #(when (= name (:name %)) %) (:transitions pn)))

(defn fireable?
  "Return true if transition is fireable under the argument marking."
  [pn mark tid]
  (when-let [arcs (not-empty (arcs-into-trans pn tid))]
    (every? (fn [ar] (>= (nth mark (dec (:pid (name2place pn (:source ar)))))
                         (:multiplicity ar)))
            arcs)))

(defn fireables
  "Return a vector of tids that are fireable under the argument marking."
  [pn mark]
  (filter #(fireable? pn mark %) (map :tid (:transitions pn))))

(defn immediate?
  [pn name]
  (= :immediate (:type (name2transition pn name))))

(defn mark-at-link-head
  "Return the mark that is at the head of the argument link."
  [pn [mark tid]]
  (as-> mark ?m
    (reduce (fn [mar arc]
              (let [indx (dec (:pid (name2place pn (:source arc))))] 
                (update mar indx #(- % (:multiplicity arc)))))
            ?m
            (arcs-into-trans pn tid))
    (reduce (fn [mar arc]
              (let [indx (dec (:pid (name2place pn (:target arc))))] 
                (update mar indx #(+ % (:multiplicity arc)))))
            ?m
            (arcs-outof-trans pn tid))))

(def ^:dynamic *visited-links* nil)
(def ^:dynamic *graph* nil)

;;; A links between markings are all the transitions from the source marking.
;;; Uniqueness of the link is specified as the marking at the tail
;;; and the transition taken. Links look like (marking tid). 
;;; The target marking is completely specified by the source and the transition. 
(defn next-markings
  "Return a seq of maps ({:source <mark> :trans <transition that fired> :target <new mark>}...)"
  [pn marking]
  (map (fn [l]
         (let [tr (tid2obj pn (second l))]
           {:source marking
            :trans (:name tr)
            :target (mark-at-link-head pn l)}))
       (filter (fn [link] (not-any? (fn [vis] (= link vis)) @*visited-links*))
               (map (fn [tid] (list marking tid)) (fireables pn marking)))))

(defn calc-reachability-aux
  [pn marking]
  (let [nexts (next-markings pn marking)] 
    (swap! *visited-links* into (map #(list (:source %) (:tid (name2transition pn (:trans %)))) nexts))
    (swap! *graph* into nexts)
    (doseq [nx nexts]
      (calc-reachability-aux pn (:target nx)))))

(defn calc-reachability
  [pn]
  (binding [*visited-links* (atom [])
            *graph* (atom [])]
    (calc-reachability-aux pn (initial-marking pn))
    @*graph*))

(defn markings2source
  "Return source state names and transitions that are sources of the argument marking."
  [mark graph name-map]
  (as-> graph ?g
    (filter #(= (:target %) mark) ?g)
    (map #(vector (get name-map (:source %)) (:trans %)) ?g)))

(defn markings2target
  "Return target state names and transitions that are targets of the argument marking."
  [mark graph name-map]
  (as-> graph ?g
    (filter #(= (:source %) mark) ?g)
    (map #(vector (get name-map (:target %)) (:trans %)) ?g)))

(defn make-name-map
  "Make a map of [marking keyword] naming the markings."
  [graph]
  (let [cnt (atom 0)]
    (reduce (fn [m link] (assoc m (:source link) (keyword (str "S" (swap! cnt inc)))))
            {}
            graph)))

;;; Reorganize from individual firings to indexed by state with transitions to and from.
;;; Also, use name-map to rename states (currently markings) to names used in Pipe (S1, S2, etc.). 
(defn pipe-format
  "Reorganize the graph data from a list of transitions to markings with transitions."
  [graph pn name-map]
  (let [init-marking (initial-marking pn)]
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

