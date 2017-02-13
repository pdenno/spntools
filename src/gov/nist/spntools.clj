(ns gov.nist.spntools
  (:require [clojure.data.xml :as xml :refer (parse-str)]
            [clojure.pprint :refer (cl-format pprint pp)]
            [clojure.math.combinatorics :as combo]
            [gov.nist.spntools.util.reach :as reach :refer (calc-reachability name2place name2transition
                                                            arcs-outof-trans arcs-into-trans immediate?
                                                            arcs-into-place arcs-outof-place)]
            [gov.nist.spntools.util.pnml :as pnml :refer (read-pnml ppp ppprint)]))

;;; ToDo: See if the name2x aid2x stuff can be simplified.

(declare eliminate-pn add-pn next-tid next-aid make-arc) ; utils
(declare join2spn split2spn find-splits vanish2spn)
(defn gspn2spn [pn]
  (-> pn
   (split2spn)
   (join2spn)
   (vanish2spn)))

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
  (let [arcs (:arcs pn)]
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
                  (reduce (fn [pn [t-in p-out]] ; POD fix this (not necessarily 1?) 
                            (add-pn pn (make-arc pn (:name t-in) (:name p-out))))
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


(declare find-vanish vanish-binds)


(def pn1
  (-> (read-pnml "data/marsan69.xml")
      (split2spn)
      #_(join2spn)))


(defn vanish2spn
  "Remove a vanishing place and IMMs that are attached."
  [pn]
  (reduce (fn [pn place]
            (let [b (vanish-binds pn place)]            
              pn))
          pn
          (find-vanish pn)))

;;;      XXXX XXXX   trans-ins (multiple)
;;;        |   |     place-ins (multiple)
;;;        V   V
;;;        ------
;;;       (      )   place
;;;        ------
;;;        |   |     place-outs (multiple)
;;;        V   V
;;;     XXXX  XXXX   trans (multiple)
;;;        |   |    
;;;        V   V     trans-outs (multiple)
(defn vanish-binds
  "Return a map identifying a set of things involved in the pattern shown above."
  [pn place]
  (as-> {} ?b
    (assoc ?b :place place)
    (assoc ?b :place-outs (arcs-outof-place pn (:place ?b)))
    (assoc ?b :trans (map :target (:place-outs ?b)))
    (assoc ?b :trans-outs (map #(arcs-outof-trans pn %)
                               (map #(:tid (name2transition pn %)) (:trans ?b))))
    (assoc ?b :place-ins (arcs-into-place pn (:place ?b)))
    (assoc ?b :trans-ins (map :source (:place-ins ?b)))))

(defn find-vanish
  [pn]
  (filter (fn [pl]
            (let [arcs-out (arcs-outof-place pn (:name pl))
                  trans (map :target arcs-out)
                  tids (map #(:tid (name2transition pn %)) trans)]
              (and ; POD these may be too restrictive. We'll see.
               (every? #(immediate? pn %) trans)
               ;; Each trans has just one  in and one out.
               (every? #(= 1 (count (arcs-outof-trans pn %))) tids)
               (every? #(= 1 (count (arcs-into-trans pn %))) tids))))
          (:places pn)))

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

(def +zippy+ (atom nil))

(defn next-aid [pn]
  (reset! +zippy+ pn)
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

        



                      
                 
  

