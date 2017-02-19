(ns gov.nist.spntools.util.reach
  (:require [clojure.data.xml :as xml :refer (parse-str)]
            [clojure.pprint :refer (cl-format pprint pp)]
            [gov.nist.spntools.util.utils :refer :all]
            [uncomplicate.neanderthal.core :as ne]
            [uncomplicate.neanderthal.native :as nen]))


;;; POD Consider making these marking vectors maps. I'd still use vectors
;;;     for +visited-links+ however. 
;;; POD still screwed up; it needs the :marking-key. 
(defn fireable? 
  "Return true if transition is fireable under the argument marking."
  [pn mark tid]
  (when-let [arcs (not-empty (arcs-into-trans pn tid))]
    (let [arc-groups (group-by :type arcs)]
      (and 
       (every? (fn [ar] (>= (nth mark (dec (:pid (name2place pn (:source ar)))))
                            (:multiplicity ar)))
               (:normal arc-groups))
       (every? (fn [ar] (< (nth mark (dec (:pid (name2place pn (:source ar)))))
                           (:multiplicity ar)))
               (:inhibitor arc-groups))))))
     
(defn fireables
  "Return a vector of tids that are fireable under the argument marking."
  [pn mark]
  (filter #(fireable? pn mark %) (map :tid (:transitions pn))))

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
  ;; "Return a seq of maps ({:M <mark> :trans <transition that fired> :Mp <new mark>}...)"
  [pn marking]
  (map (fn [l]
         (let [tr (tid2obj pn (second l))]
           {:M marking
            :fire (:name tr)
            :Mp (mark-at-link-head pn l)
            :rate (:rate tr)}))
       (filter (fn [link] (not-any? (fn [vis] (= link vis)) @*visited-links*))
               (map (fn [tid] (list marking tid)) (fireables pn marking)))))

(defn calc-reachability-aux
  [pn marking]
  (let [nexts (next-markings pn marking)] 
    (swap! *visited-links* into (map #(list (:M %) (:tid (name2transition pn (:fire %)))) nexts))
    (reset! +zippy+ @*visited-links*)
    (swap! *graph* into nexts)
    (doseq [nx nexts]
      (calc-reachability-aux pn (:Mp nx)))))

(defn calc-reachability
  [pn]
  (let [graph (initial-marking pn)]
    (binding [*visited-links* (atom [])
              *graph* (atom [])]
      (calc-reachability-aux pn (:initial-marking graph))
      (assoc graph :graph @*graph*))))



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
