(ns gov.nist.spntools
  (:require [clojure.data.xml :as xml :refer (parse-str)]
            [clojure.pprint :refer (cl-format pprint pp)]
            [clojure.math.combinatorics :as combo]
            [gov.nist.spntools.util.reach :as reach :refer (calc-reachability)]
            [gov.nist.spntools.util.pnml :as pnml :refer (read-pnml)]
            [gov.nist.spntools.util.utils :refer :all]))

;;; ToDo: See if the name2x aid2x stuff can be simplified.

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

(declare join2spn)
;;;   ___    ___
;;;  (   )  (   )   places-top   May be one or more
;;;   ---    ---
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
        (as-> ?b ?bb ; POD remove when :place-top goes.
          (assoc ?bb :places-top (distinct (map :source narcs)))
          ;; This one needs to go.
          (assoc ?bb :place-top (:name (some (fn [pl] (when (every? #(= (:source %) (:name pl)) narcs) pl))
                                             places)))
          (assoc ?bb :preserve-top-ins (remove (fn [tin] (some #(= (:source tin) %) (:places-top ?bb)))
                                               (:top-ins ?bb)))
          (assoc ?bb :top-ins (remove (fn [tin] (some #(= % tin) (:preserve-top-ins ?bb))) (:top-ins ?bb))))))))


(defn join-new-trans
  "Creates 'command vectors' providing information to create new transitions and arcs."
  [pn binds owner]
  (let [owner-t (:source (some #(when (= owner (:target %)) %) (:places-ins binds)))
        rate (:rate (name2transition pn owner-t))
        kill-trans (map :name (:trans binds))
        receive-preserves (filter #(= owner (:source %)) (:preserve-top-ins binds))
        send-preserves (filter #(= owner (:target %)) (:preserve-top-ins binds))
        others (remove #(= % owner) (:places* binds))]
    (loop [in-front 0
           accum []]
      (if (> in-front (count others))
        accum
        (cond
          (= in-front 0)
          (recur (inc in-front)
                 (let [n (new-name owner "-first")]
                   (conj accum {:name n
                                :rate rate
                                :preserves (into (map #(assoc % :target n) receive-preserves)
                                                 (map #(assoc % :source % n) send-preserves))
                                :receive-tops (:places-top binds)
                                :receive-inhibitors others
                                :send-activator owner})))
          (= in-front (count others))
          (recur (inc in-front)
                 (let [n (new-name owner "-last")]
                   (conj accum {:name n
                                :rate rate
                                :receive-tops (:places-top binds)
                                :preserves (into (map #(assoc % :target  n) receive-preserves)
                                                 (map #(assoc % :source n) send-preserves))
                                :receive-activators others
                                :send-activator (:name (:place-bottom binds))})))
          :else
          (recur (inc in-front)
                 (into accum 
                       (map (fn [ahead]
                              (let [n (new-name-ahead owner ahead)] 
                                {:name n
                                 :rate rate
                                 :receive-tops (:places-top binds)
                                 :preserves (into (map #(assoc % :target n) receive-preserves)
                                                  (map #(assoc % :source n) send-preserves))
                                 :receive-inhibitors (remove (fn [o] (some #(when (= o %) %) ahead)) others)
                                 :send&receive-activators ahead
                                 :send-activator owner}))
                              (combo/combinations others in-front)))))))))
                                    
;(def j2 (read-pnml "data/join2.xml"))
;(def bbb (join-binds j2 (first (find-joins j2))))
;(def foo (join-new-trans j2 bbb :P1))
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
                  (reduce (fn [pn ar] (eliminate-pn pn ar)) ?pn (:top-ins b))
                  (reduce (fn [pn ar] (eliminate-pn pn ar)) ?pn (:preserve-top-ins b)) 
                  (reduce (fn [pn tr] (eliminate-pn pn tr)) ?pn (:trans b))
                  (reduce (fn [pn ar] (eliminate-pn pn ar)) ?pn (:places-ins b))
                  (reduce (fn [pn ar] (eliminate-pn pn ar)) ?pn (:imm-ins b))
                  (eliminate-pn ?pn (:place-out-in b))
                  (reduce (fn [pn cmd-vec] ; cmd-vec, from join-new-trans is commands over one of :places*
                            (reduce (fn [pnn cmd] ; each cmd creates a new transition and the arcs to/from it.
                                      (as-> pnn ?pnp
                                        (add-pn ?pnp {:name (:name cmd) :tid (next-tid ?pnp)
                                                      :type :exponential :rate (:rate cmd)})
                                        (reduce (fn [pn receiver] ; POD 2017-02-13
                                                  (add-pn pn (make-arc pn receiver (:name cmd))))
                                                ?pnp
                                                (:receive-tops cmd))
                                        (reduce (fn [pn psv]
                                                  (add-pn pn (make-arc pn (:source psv) (:target psv)
                                                                       :type (:type psv) :multiplicity (:multiplicity psv))))
                                                ?pnp
                                                (:preserves cmd))
                                        (add-pn ?pnp (make-arc ?pnp (:name cmd) (:send-activator cmd)))
                                        (reduce (fn [pn inhib]
                                                  (add-pn pn (make-arc pn inhib (:name cmd) :type :inhibitor)))
                                                ?pnp
                                                (:receive-inhibitors cmd))
                                        (reduce (fn [pn activ]
                                                  (add-pn pn (make-arc pn activ (:name cmd))))
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


;;;------- Diagnostic 

(def pn1
  (-> (read-pnml "data/marsan69.xml")
      (split2spn)
      #_(join2spn)))

(defn one-step
  [filename]
    (-> (read-pnml filename)
        (split2spn)))

(defn two-step
  [filename]
    (-> (read-pnml filename)
        (split2spn)
        (join2spn)))


(def bbb (join-binds pn1 (first (find-joins pn1))))

(defn find-arc
  [pn source target]
  (filter #(and (= (:source %) source)
                (= (:target %) target))
          (:arcs pn)))
                      

;;; Ones with commas are inhibitors
(defn j2-has-arcs []    
  (let [j2 (gspn2spn (read-pnml "data/join2.xml"))
        data  [[:Pstart :P1-last 1] [:Pstart :P1-first 2] [:Pstart :P2-first 3] [:Pstart :P2-last 4]
               [:P1-first :P1 5]  [:P1 :P1-first, 6] [:P2 :P1-first 7]  [:P1 :P2-first, 8]  [:P2-first :P2 9]
               [:P2 :P2-first, 10] [:P2 :P1-last 11] [:P1 :P2-last 12] [:P1 :P1-last, 13] [:P2 :P2-last, 14]
               [:P1-last :Pjoin 15]  [:P2-last :Pjoin 16] [:Pjoin :Treturn 17]  [:Treturn :Pstart 18]]]
    (println "Testing" (count data) "arcs")
    (every? (fn [r] r)
            (reduce (fn [result [source target num]]
                      (if (= (count (find-arc j2 source target)) 1) ; just worked out that way.
                        (conj result true)
                        (do (println "--- Failing:" num  "[" source target "]")
                            (conj result false))))
                    []

                    data))))

(defn j2-weird-arcs []
  (let [j2 (gspn2spn (read-pnml "data/join2.xml"))
        data  [[:Pstart :P1-last 1] [:Pstart :P1-first 2] [:Pstart :P2-first 3] [:Pstart :P2-last 4]
               [:P1-first :P1 5]  [:P1 :P1-first, 6] [:P2 :P1-first 7]  [:P1 :P2-first, 8]  [:P2-first :P2 9]
               [:P2 :P2-first, 10] [:P2 :P1-last 11] [:P1 :P2-last 12] [:P1 :P1-last, 13] [:P2 :P2-last, 14]
               [:P1-last :Pjoin 15]  [:P2-last :Pjoin 16] [:Pjoin :Treturn 17]  [:Treturn :Pstart 18]]
        cdata (map (fn [[s t _]] [s t]) data)]
    (remove (fn [a] (some #(= [(:source a) (:target a)] %) cdata)) (:arcs j2))))


                        
