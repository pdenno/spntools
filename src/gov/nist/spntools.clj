(ns gov.nist.spntools
  (:require [clojure.data.xml :as xml :refer (parse-str)]
            [clojure.pprint :refer (cl-format pprint pp)]
            [clojure.math.combinatorics :as combo]
            [gov.nist.spntools.util.pnml :refer (read-pnml reorder-marking ppp ppprint)]))

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
(declare eliminate-pn add-pn next-tid next-aid make-arc) ; utils
(declare join2spn split2spn find-splits)
(defn gspn2spn [pn]
  (-> pn
   (split2spn)
   (join2spn)))

;;;    === ===  trans-in [multiple]
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
(defn split-binds
  "Return a map identifying a set of things involved in the pattern shown above."
  [pn imm]
  (let [arcs (:arcs pn)]
    (as-> {} ?b
      (assoc ?b :imm-name (:name imm))
      (assoc ?b :imm-in (some #(when (= (:imm-name ?b) (:target %)) %) arcs))
      (assoc ?b :outs (filter #(= (:source %) (:imm-name ?b)) arcs))
      (assoc ?b :places-out (map #(name2place pn %) (map :target (:outs ?b))))
      (assoc ?b :place (name2place pn (:source (:imm-in ?b))))
      (assoc ?b :place-ins (filter #(= (:target %) (:name (:place ?b))) arcs))
      (assoc ?b :trans-in (map #(name2transition pn (:source %)) (:place-ins ?b))))))

(defn split2spn
  "Eliminate IMMs that have outbound arcs to multiple places and a single inbound arc."
  [pn]
  (let [arcs (:arcs pn)
        new-cnt (atom 0)]
    (reduce (fn [pn imm]
              (let [b (split-binds pn imm)]
                (as-> pn ?pn
                  (eliminate-pn ?pn imm)
                  (eliminate-pn ?pn (:place b))
                  (eliminate-pn ?pn (:imm-in b))
                  (reduce (fn [pn ar] (eliminate-pn pn ar)) ?pn (:place-ins b))
                  (reduce (fn [pn ar] (eliminate-pn pn ar)) ?pn (:outs b))
                  ;; Add arcs from all the trans-in to each of the places-out
                  ;; Each place-out gets as many inbound arcs as there are places-in.
                  (reduce (fn [pn [t-in p-out]]
                                   (add-pn pn {:aid (keyword (str "spl" (swap! new-cnt inc)))
                                               :source (:name t-in) :target (:name p-out)
                                               :multiplicity 1})) ; POD fix this (not necessarily 1?) 
                          ?pn
                          (for [t-in (:trans-in b),
                                p-out (:places-out b)]
                            (vector t-in p-out))))))
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

(declare join2spn strip-name new-name new-name-ahead)
;;;    |      |     top-ins   -- These may include things from the iplaces!!!
;;;    V      V
;;;   ===    ===    trans [multiple]
;;;    |      |     places-ins [multiple]
;;;   _V_    _V_
;;;  (   )  (   )    iplaces   [Keep]
;;;   ---    ---
;;;    |      |
;;;    |      |     imm-ins 
;;;    V      V
;;;   XXXXXXXXXX    imm
;;;      |   place-out-in
;;;     _V_    
;;;    (___)   place-bottom      [Keep]
(defn join-binds
  "Return a map identifying a set of things involved in the pattern shown above."
  [pn imm]
  (let [arcs (:arcs pn)
        trs (:transitions pn)
        places (:places pn)]
    (as-> {} ?b
      (assoc ?b :imm-name (:name imm))
      (assoc ?b :imm-ins (filter #(= (:imm-name ?b) (:target %)) arcs))
      (assoc ?b :places* (map :source (:imm-ins ?b)))
      (assoc ?b :iplaces (map #(name2place pn %) (:places* ?b)))
      (assoc ?b :places-ins (filter (fn [ar] (some #(= (:target ar) %) (:places* ?b))) arcs))
      (assoc ?b :trans (filter #(some (fn [pl] (= (:name %) (:source pl))) (:places-ins ?b)) trs))
      (assoc ?b :top-ins (filter #(some (fn [tr] (= (:name tr) (:target %))) (:trans ?b)) arcs))
      (assoc ?b :place-out-in (some #(when (= (:source %) (:imm-name ?b)) %) arcs))
      (assoc ?b :place-bottom (some #(when (= (:name %) (:target (:place-out-in ?b))) %) places))
      ;; Every :normal arc with target in a trans has this place as its source.
      (let [narcs (filter (fn [ar] (and (= (:type ar) :normal)
                                        (some #(= (:target ar) (:name %)) (:trans ?b))))
                          (:top-ins ?b))]
        (assoc ?b :place-top (:name (some (fn [pl] (when (every? #(= (:source %) (:name pl)) narcs) pl))
                                          places)))))))

(defn join-new-trans
  "Creates 'command vectors' providing information to create new transitions and arcs."
  [pn binds owner]
  (let [owner-t (:source (some #(when (= owner (:target %)) %) (:places-ins binds)))
        rate (:rate (name2transition pn owner-t))
        others (remove #(= % owner) (:places* binds))]
    (loop [in-front 0
           accum []]
      (if (> in-front (count others))
        accum
        (cond
          (= in-front 0)
          (recur (inc in-front)
                 (conj accum {:name (new-name owner "-first")
                              :rate rate
                              :receive-top (:place-top binds)
                              :receive-inhibitors others
                              :send-activator owner}))
          (= in-front (count others))
          (recur (inc in-front)
                 (conj accum {:name (new-name owner "-last")
                              :rate rate
                              :receive-top (:place-top binds)
                              :receive-activators others
                              :send-activator (:name (:place-bottom binds))}))
          :else
          (recur (inc in-front)
                 (into accum 
                       (map (fn [ahead]
                              {:name (new-name-ahead owner ahead)
                               :rate rate
                               :receive-top (:place-top binds)
                               :receive-inhibitors (remove (fn [o] (some #(when (= o %) %) ahead)) others)
                               :send&receive-activators ahead
                               :send-activator owner})
                            (combo/combinations others in-front)))))))))
                                    
;(def pn3 (read-pnml "data/join2.xml"))
;(def pn4 (read-pnml "data/join3.xml"))
;(def bbb (join-binds pn4 (first (find-joins pn4))))
;(def foo (join-new-trans pn4 bbb :P1))

(defn find-joins
  "Return IMMs that have multiple inbound arcs."
  [pn]
  (let [arcs (:arcs pn)]
    (filter (fn [tr]
              (let [tr-name (:name tr)]
                (and (immediate? pn tr-name)
                     (> (count (filter (fn [ar] (= (:target ar) tr-name)) arcs)) 1))))
            (:transitions pn))))

(defn join2spn
  "Eliminate IMMs that have outbound arcs to multiple places and (a single???) inbound arc."
  [pn]
  (let [arcs (:arcs pn)
        trs (:transitions pn)
        places (:places pn)
        pn-pristine pn
        new-cnt (atom 0)]
    (reduce (fn [pn imm]
              (let [b (join-binds pn imm)]
                (as-> pn ?pn
                  (eliminate-pn ?pn imm)
                  ;; Some :top-ins might not have source in :place-top; keep those.
                  (reduce (fn [pn ar] (eliminate-pn pn ar)) ?pn
                          (filter #(= (:source %) (:place-top b)) (:top-ins b)))
                  (reduce (fn [pn tr] (eliminate-pn pn tr)) ?pn (:trans b))
                  (reduce (fn [pn ar] (eliminate-pn pn ar)) ?pn (:places-ins b))
                  (reduce (fn [pn ar] (eliminate-pn pn ar)) ?pn (:imm-ins b))
                  (eliminate-pn ?pn (:place-out-in b))
                  (reduce (fn [pn cmd-vec] ; cmd-vec, from join-new-trans is commands over one of :places*
                            (reduce (fn [pnn cmd] ; each cmd creates a new transition and the arcs to/from it.
                                      (as-> pnn ?pnp
                                        (add-pn ?pnp {:name (:name cmd) :tid (next-tid ?pnp)
                                                      :type :exponential :rate (:rate cmd)}) 
                                        (add-pn ?pnp (make-arc ?pnp (:receive-top cmd) (:name cmd)))
                                        (add-pn ?pnp (make-arc ?pnp (:name cmd) (:send-activator cmd)))
                                        (reduce (fn [pn inhib]
                                                  (add-pn pn (make-arc pn (:name cmd) inhib :type :inhibitor)))
                                                ?pnp
                                                (:receive-inhibitors cmd))
                                        (reduce (fn [pn inhib]
                                                  (add-pn pn (make-arc pn (:name cmd) inhib)))
                                                ?pnp
                                                (:receive-activators cmd))
                                        (reduce (fn [pn active]
                                                  (as-> pn ?pn2
                                                    (add-pn ?pn2 (make-arc ?pn2 (:name cmd) active))
                                                    (add-pn ?pn2 (make-arc ?pn2 active (:name cmd)))))
                                                ?pnp
                                                (:send&receive-activators cmd))))
                                    pn
                                    cmd-vec))
                          ?pn ; Maybe 'pristine' isn't necessary. Haven't thought about it.
                          (map #(join-new-trans pn-pristine b %) (:places* b))))))
            pn
            (find-joins pn))))

;;; ---- Utils ---------------
(defn eliminate-pn
  "Transform the PN graph by eliminating the argument element."
  [pn elem]
  (cond (:pid elem) ; It is a place.
        (assoc pn :places (remove #(= % elem) (:places pn)))
        (:tid elem) ; It is a transition
        (assoc pn :transitions (remove #(= % elem) (:transitions pn)))
        (:aid elem) ; It is an arc
        (assoc pn :arcs (remove #(= % elem) (:arcs pn)))))

(defn add-pn
  "Transform the PN graph by adding the argument element."
  [pn elem]
  (cond (:pid elem) ; It is a place.
        (assoc pn :places (conj (:places pn) elem))
        (:tid elem) ; It is a transition
        (assoc pn :transitions (conj (:transitions pn) elem))
        (:aid elem) ; It is an arc
        (assoc pn :arcs (conj (:arcs pn) elem))))

(defn next-tid [pn]
  (if (empty? (:transitions pn))
    1
    (inc (apply max (map :tid (:transitions pn))))))

(defn next-aid [pn]
  (if (empty? (:arcs pn))
    1
    (inc (apply max (map :aid (:arcs pn))))))

;;; Naming convention for transitions: who is ahead of you?
(defn strip-name
  [key]
  (str (str (subs (str key) 1))))

(defn new-name
  "Return the string naming the keyword."
  [key suffix]
  (keyword (str (str (subs (str key) 1)) suffix)))

(defn new-name-ahead
  [owner ahead]
  (new-name
   owner
   (str "--"
        (apply str (interpose "&" (map strip-name ahead)))
        "-before")))

(defn make-arc
  [pn source target & {:keys [type aid multiplicity]
                    :or {type :normal aid (next-aid pn) multiplicity 1}}]
  {:aid aid :source source :type type :multiplicity multiplicity})

        



                      
                 
  

