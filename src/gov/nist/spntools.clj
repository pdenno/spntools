(ns gov.nist.spntools
  (:require [clojure.data.xml :as xml :refer (parse-str)]
            [clojure.pprint :refer (cl-format pprint pp)]
            [gov.nist.spntools.util.pnml :refer (read-pnml reorder-marking)]))

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
    (every? (fn [ar] (>= (nth mark (dec (:pid (id2place pn (:source ar)))))
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
              (let [indx (dec (:pid (id2place pn (:source arc))))] 
                (update mar indx #(- % (:multiplicity arc)))))
            ?m
            (arcs-into-trans pn tid))
    (reduce (fn [mar arc]
              (let [indx (dec (:pid (id2place pn (:target arc))))] 
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
    (swap! *visited-links* into (map #(list (:source %) (:tid (id2transition pn (:trans %)))) nexts))
    (swap! *graph* into nexts)
    (doseq [nx nexts]
      (calc-reachability-aux pn (:target nx)))))

(defn calc-reachability
  [pn]
  (binding [*visited-links* (atom [])
            *graph* (atom [])]
    (calc-reachability-aux pn (initial-marking pn))
    @*graph*))

;;; Put problem in pipe-normal-form ;^)
(def pn1
  (reorder-marking
   (read-pnml "data/two-machine-formatted.xml")
   [:free-buffer-spots :full-buffer-spots :m1-busy :m1-idle :m2-busy :m2-idle]))

(def pn2 (read-pnml "data/marsan69.xml"))
;(calc-reachability pn2)
;(pipe-format grph pn2 (make-name-map grph)))

(def pn1-state-names {[3 0 0 1 0 1] :s0,
                      [3 0 1 0 0 1] :s01,
                      [2 1 0 1 0 1] :s02,
                      [3 0 0 1 1 0] :s03,
                      [2 1 1 0 0 1] :s04,
                      [3 0 1 0 1 0] :s05,
                      [2 1 0 1 1 0] :s06,
                      [2 1 1 0 1 0] :s07,
                      [1 2 0 1 1 0] :s08,
                      [1 2 1 0 1 0] :s09,
                      [1 2 1 0 0 1] :s10,
                      [0 3 0 1 1 0] :s11,
                      [0 3 1 0 1 0] :s12,
                      [0 3 1 0 0 1] :s13,
                      #_[0 3 0 1 0 1] #_:bogus})

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

;;;==========================================================================
;;; GSPN --> SPN
;;;==========================================================================
(declare split2spn find-splits)
(defn gspn2spn [pn]
  (->
   (split2spn pn)))
;;;;   === ===  trans-in [multiple]
;;;     | |  place-ins [multiple]
;;;     V_V
;;;    (   ) place
;;;     ---
;;;      |
;;;      | imm-in 
;;;      V
;;;   XXXXXXX    imm
;;;    |   |  outs
;;;   (_) (_)    places-out

(defn split2spn
  "Eliminate IMMs that have outbound arcs to multiple places and a single inbound arc."
  [pn]
  (let [arcs (:arcs pn)
        new-cnt (atom 0)]
    (reduce (fn [pn imm]
              (let [imm-name (:name imm)
                    imm-in (some #(when (= imm-name (:target %)) %) arcs)
                    outs (filter #(= (:source %) imm-name) arcs)
                    places-out (map #(name2place pn %) (map :target outs))
                    place (name2place pn (:source imm-in))
                    place-ins (filter #(= (:target %) (:name place)) arcs)
                    trans-in (map #(name2transition pn (:source %)) place-ins)]
                (as-> pn ?pn
                  (assoc ?pn :transitions (remove #(= % imm) (:transitions ?pn)))
                  (assoc ?pn :places (remove #(= % place) (:places ?pn)))
                  (assoc ?pn :arcs (remove #(= % imm-in) (:arcs ?pn)))
                  (assoc ?pn :arcs (reduce (fn [arcs o] (remove #(= o %) arcs)) (:arcs ?pn) place-ins))
                  (assoc ?pn :arcs (reduce (fn [arcs o] (remove #(= o %) arcs)) (:arcs ?pn) outs))
                  ;; Add arcs from all the trans-in to each of the places-out
                  ;; Each place-out gets as many inbound arcs as there are places-in.
                  (assoc ?pn :arcs
                         (reduce (fn [arcs [t-in p-out]]
                                   (conj arcs {:aid (keyword (str "spl" (swap! new-cnt inc)))
                                               :source (:name t-in) :target (:name p-out)
                                               :multiplicity -1}))
                                 (:arcs ?pn)
                                 (for [t-in trans-in, p-out places-out] (vector t-in p-out)))))))
            pn
            (find-splits pn))))


(defn find-splits
  "Return IMMs that have multiple outbound arcs and a single inbound arc."
  [pn]
  (let [arcs (:arcs pn)]
    (filter (fn [tr]
              (let [tr-name (:name tr)]
                (and (immediate? pn tr-name)
                     (> (count (filter (fn [ar] (= (:source ar) tr-name)) arcs)) 1)
                     (= (count (filter (fn [ar] (= (:target ar) tr-name)) arcs)) 1))))
            (:transitions pn))))
                      
                 
  

