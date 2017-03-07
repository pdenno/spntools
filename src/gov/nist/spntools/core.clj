(ns gov.nist.spntools
  (:require [clojure.data.xml :as xml :refer (parse-str)]
            [clojure.pprint :refer (cl-format pprint pp)]
            [clojure.math.combinatorics :as combo]
            [gov.nist.spntools.util.reach :as reach :refer (reachability)]
            [gov.nist.spntools.util.pnml :as pnml :refer (read-pnml reorder-places)]
            [gov.nist.spntools.util.utils :as utils :refer :all]
            [clojure.core.matrix :as m :refer :all]
            [clojure.core.matrix.linear :as ml :refer (svd)]))

;;; ToDo: Remove :preserves or :receives-top from join-cmd.
;;;         (1) use aids, not arcs. 
;;;         (2) call it :preserves tops. 

;;; Four steps to most reductions:
;;;  1) Find instances of the pattern.
;;;  2) Create bindings of elements of the instance.
;;;  3) Create 'command vectors' of graph editing instructions.
;;;  4) Reduce the graph by executing the instructions.

(m/set-current-implementation :vectorz)

(declare join2spn split2spn find-splits vanish2spn)
(defn gspn2spn [pn]
  (-> pn
   (split2spn)
   (join2spn)
   (vanish2spn)))

;;;   === ===  trans-in [multiple]
;;;     | |  place-ins [multiple]
;;;     V_V
;;;    (   ) place
;;;     ---
;;;      |
;;;      | imm-in 
;;;      V
;;;   XXXXXXX    imm
;;;    |   |  outs
;;;    V   V
;;;   (_) (_)    places-out
(defn split-binds
  "Return a map identifying a set of things involved in the pattern shown above."
  [pn imm]
  (let [arcs (:arcs pn)]
    (as-> {} ?b
      (assoc ?b :IMM (:name imm))
      (assoc ?b :imm-in (some #(when (= (:IMM ?b) (:target %)) %) arcs))
      (assoc ?b :outs (filter #(= (:source %) (:IMM ?b)) arcs))
      (assoc ?b :places-out (map #(name2obj pn %) (map :target (:outs ?b)))) ; POD fix :places-out (naming convention).
      (assoc ?b :place (name2obj pn (:source (:imm-in ?b))))
      (assoc ?b :place-ins (filter #(= (:target %) (:name (:place ?b))) arcs))
      (assoc ?b :trans-in (map #(name2obj pn (:source %)) (:place-ins ?b))))))

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

(declare join2spn join-cmd-every)
;;;   ___    ___
;;;  (   )  (   )   places-top   May be one or more
;;;   ---    ---
;;;    |      ^     top-arcs (everything to/from places-top) -- Ephemeral trans-in&outs include things from the places* 
;;;    V      |
;;;   ===    ===    trans [multiple]
;;;    |      |     places-ins, places-in&outs [multiple]
;;;   _V_    _V_
;;;  (   )  (   )    places*   [Keep]
;;;   ---    ---
;;;    |      |
;;;    |      |     imm-ins 
;;;    V      V
;;;   XXXXXXXXXX    IMM   -- The thing we are removing, provided by find-joins.
;;;      |   place-bottom-in
;;;     _V_    
;;;    (___)   place-bottom      [Keep]
(defn join-cmd-middles
  [owner binds pn in-front & {:keys [tight?]}] ; POD More to do here for :tight?
  (let [owner-t (:source (some #(when (= owner (:target %)) %) (:places-ins binds)))
        rate (:rate (name2obj pn owner-t))
        imm (:IMM binds)
        others (remove #(= % owner) (:places* binds))]
    (map (fn [ahead]
           (let [name (new-name-ahead imm owner ahead)]
             (as-> (join-cmd-every name owner binds pn :tight? tight?) ?cmd
               (assoc ?cmd
                      :receive-inhibitors (vec (clojure.set/difference (set others) (set ahead)))
                      :send&receive-activators ahead
                      :send-activators (vector owner))
               ;; Remove stuff from :psv-trans&places that isn't part of middles
               (assoc ?cmd
                      :psv-trans&places
                      (remove #(or (and (= :normal (:type %))    (= owner (:target %)) (= name (:source %)))
                                   #_(and (= :inhibitor (:type %)) (= owner (:source %)) (= name (:target %))))
                              (:psv-trans&places ?cmd))))))
         (combo/combinations others in-front))))

(defn join-cmd-every
  [name owner binds pn & {:keys [tight?]}]
  (let [owner-t (:source (some #(when (= owner (:target %)) %) (:places-ins binds)))
        rate (:rate (name2obj pn owner-t))
        receive-preserves (filter #(= owner (:source %)) (:places-in&outs binds))
        send-preserves (filter #(= owner (:target %)) (:places-in&outs binds))]
    {:name name
     :tight? tight?
     :rate rate ; :psv-trans&places don't make new ones, they reuse!
     :psv-trans&places (into (map #(assoc % :target name) receive-preserves) 
                             (map #(assoc % :source name) send-preserves))
     :receive-tops (filter #(first (paths-to pn % owner 4)) (:places-top binds))}))

(defn join-cmd-first&last
  [owner binds pn first?  & {:keys [tight?]}]
  (let [imm (:IMM binds)
        others (remove #(= % owner) (:places* binds))
        name (new-name imm owner (if first? "-first" "-last"))
        receive-preserves (filter #(= owner (:source %)) (:places-in&outs binds))
        send-preserves (filter #(= owner (:target %)) (:places-in&outs binds))]
    (as-> (join-cmd-every name owner binds pn :tight? tight?) ?cmd
      (if first?
        (assoc ?cmd
               :receive-inhibitors (if tight? (conj others owner) others))
        ;; Remove stuff from :psv-trans&places that isn't part of -last.
        (as-> ?cmd ?c
          (assoc ?c
                 :psv-trans&places
                 (remove #(or (and (= :normal (:type %))    (= owner (:target %)) (= name (:source %)))
                              (and (= :inhibitor (:type %)) (= owner (:source %)) (= name (:target %))))
                         (:psv-trans&places ?c)))
          (assoc ?c
                 :receive-inhibitors (if tight? (conj others owner) (vector owner))
                 :receive-activators others
                 :send-activators (if tight?
                                    (conj (:places-top binds) (:place-bottom binds))
                                    (vector (:place-bottom binds)))))))))
(defn join-binds
  "Return a map identifying a set of things involved in the pattern shown above."
  [pn imm]
  (let [arcs (:arcs pn)
        trs (:transitions pn)
        places (:places pn)]
    (as-> {} ?b
      (assoc ?b :IMM (:name imm))
      (assoc ?b :imm-ins (filter #(= (:IMM ?b) (:target %)) arcs))
      (assoc ?b :places* (set (map :source (:imm-ins ?b))))
      (assoc ?b :places-ins (set (filter (fn [ar] (some #(= (:target ar) %) (:places* ?b))) arcs)))
      (assoc ?b :trans (set (map :name (filter #(some (fn [pl] (= (:name %) (:source pl))) (:places-ins ?b)) trs))))
      (assoc ?b :trans-in&outs  (set (filter #(or (contains? (:trans ?b) (:source %))
                                                  (contains? (:trans ?b) (:target %))) arcs)))
      (assoc ?b :place-bottom-in (some #(when (= (:source %) (:IMM ?b)) %) arcs))
      (assoc ?b :place-bottom (:name (some #(when (= (:name %) (:target (:place-bottom-in ?b))) %) places)))
      (assoc ?b :places-top (set
                             (map :source
                                  (remove #(or (contains? (:trans ?b) (:source %))
                                               (contains? (:places* ?b) (:source %)))
                                          (:trans-in&outs ?b)))))
      (assoc ?b :top-arcs (filter #(or (contains? (:places-top ?b) (:source %))
                                       (contains? (:places-top ?b) (:target %))) arcs))
      (assoc ?b :places-in&outs (vec (clojure.set/difference
                                     (set (:trans-in&outs ?b))
                                     (set (:top-arcs ?b)))))
      (reduce (fn [b key] (update-in b [key] vec)) ?b [:trans :places-top :places-ins :places*])
      (dissoc ?b :trans-in&outs))))

(declare join-cmd-aux join-cmd-first&last join-cmd-middles join-cmd-every)
(defn join-cmd
  "Creates 'command vectors' each element of which provides instructions 
   concerning how to create a new transition and its arcs."
  [pn binds owner]
  (let [problem (some #(when (= % (:name (:place-bottom binds))) %) (:places-top binds))]
    (join-cmd-aux pn binds owner :tight? problem)))

(defn join-cmd-aux
  [pn binds owner & {:keys [tight?]}]
  (let [m1 (dec (count (:places* binds)))]
    (reduce (fn [accum in-front]
              (cond
                (= in-front 0)  (conj accum (join-cmd-first&last owner binds pn true  :tight? tight?)),
                (= in-front m1) (conj accum (join-cmd-first&last owner binds pn false :tight? tight?)),
                :else           (into accum (join-cmd-middles owner binds pn in-front))))
            []
            (range (inc m1)))))


(defn find-joins
  "Return IMMs that have multiple inbound arcs."
  [pn]
  (let [arcs (:arcs pn)]
    (filter (fn [tr]
              (let [tr-name (:name tr)]
                (and (immediate? pn tr-name)
                     (> (count (filter (fn [ar] (= (:target ar) tr-name)) arcs)) 1))))
            (:transitions pn))))

(defn join2spn-adds [pn cmd binds]
  (as-> pn ?pn
    (add-pn ?pn {:name (:name cmd) :tid (next-tid ?pn)
                 :type :exponential :rate (:rate cmd)})
    ;;(when (:tight? cmd)
    ;;(eliminate-pn pn ar)) ?pn (:top-arcs b)))  <=====  TODO
    (if (:tight? cmd) ; On tight, both of the trans above the imm get replaced
      (reduce (fn [pn tr]
                (reduce (fn [pn ar] (eliminate-pn pn ar))
                        pn
                        (filter #(or (= (:source %) (:name tr)) (= (:target %) (:name tr))) (:arcs pn))))
              ?pn
              (:trans binds))
      ?pn)
    (reduce (fn [pn receiver] ; POD 2017-02-13
              (add-pn pn (make-arc pn receiver (:name cmd) :debug :receive-tops)))
            ?pn
            (:receive-tops cmd))
    (reduce (fn [pn psv]
              (add-pn pn (make-arc pn (:source psv) (:target psv) 
                                   :type (:type psv) :multiplicity (:multiplicity psv)
                                   :debug (:debug :psv-trans&places))))
            ?pn
            (:psv-trans&places cmd))
    (reduce (fn [pn activ]
              (add-pn ?pn (make-arc ?pn (:name cmd) activ :debug :send-activators)))
            ?pn
            (:send-activators cmd))
    (reduce (fn [pn inhib]
              (add-pn pn (make-arc pn inhib (:name cmd) :type :inhibitor :debug :receive-inhibitors)))
            ?pn
            (:receive-inhibitors cmd))
    (reduce (fn [pn activ]
              (add-pn pn (make-arc pn activ (:name cmd) :debug :receive-activators)))
            ?pn
            (:receive-activators cmd))
    (reduce (fn [pn active]
              (as-> pn ?pn2
                (add-pn ?pn2 (make-arc ?pn2 (:name cmd) active :debug :s&r))
                (add-pn ?pn2 (make-arc ?pn2 active (:name cmd) :debug :s&r))))
            ?pn
            (:send&receive-activators cmd))))

(defn join2spn
  "Eliminate IMMs that have outbound arcs to multiple places and (a single???) inbound arc."
  [pn]
  (reduce (fn [pn imm]
            (let [b (join-binds pn imm)
                  set-trans (set (:trans b))]
              (as-> pn ?pn               
                (eliminate-pn ?pn imm)   
                (let [nimm (:name imm)]
                  (reduce (fn [pn ar] (eliminate-pn pn ar)) ; Remove any arc that references the IMM.
                          ?pn (filter #(or (= (:source %) nimm) (= (:target %) nimm)) (:arcs ?pn))))
                (reduce (fn [pn ar] (eliminate-pn pn ar)) ?pn (:places-in&outs b))
                (reduce (fn [pn ar] (eliminate-pn pn ar)) ?pn
                        (filter #(or (contains? set-trans (:source %))
                                     (contains? set-trans (:target %)))
                                (:top-arcs b))) ; Don't delete the innocent unrelated top arcs.
                (reduce (fn [pn tr] (eliminate-pn pn tr)) ?pn (map #(name2obj ?pn %) (:trans b)))
                (reduce (fn [pn ar] (eliminate-pn pn ar)) ?pn (:places-ins b))
                ;; cmd-vec, from join-cmd is commands over one of :places* ('owner')
                ;; each cmd creates a new transition and the arcs to/from it.
                (reduce (fn [pn cmd-vec] (reduce (fn [pn cmd] (join2spn-adds pn cmd b)) pn cmd-vec)) 
                        ?pn 
                        (map #(join-cmd pn b %) (:places* b)))))) 
          pn 
          (find-joins pn)))

;;;     (   ) ( )    splaces             -- Not recorded. Use strans-ins. Keep these.
;;;      | |   |     strans-ins          -- Don't keep anything from here through trans-outs.
;;;      v v   v
;;;      XXXX XXXX   strans (multiple)   
;;;        |   |     
;;;        V   V     place-ins (multiple)
;;;        ------
;;;       (      )   vplace (owner)
;;;        ------
;;;        |    |     place-outs (multiple)
;;;        V    V
;;;     XXXX   XXXX   trans (multiple)
;;;      |      |    
;;;      V      V     trans-outs (multiple)
;;;     ---    ---
;;;    (   )  (   )    tplaces (multiple)
;;;     ---    ---
(declare find-vanish vanish-binds vanish-cmd)
(defn vanish-binds
  "Return a map identifying a set of things involved in the pattern shown above."
  [pn place]
  (as-> {} ?b
    (assoc ?b :VPLACE place)
    (assoc ?b :vplace-outs (arcs-outof pn (:name (:VPLACE ?b))))
    (assoc ?b :trans (map #(name2obj pn (:target %)) (:vplace-outs ?b)))
    (assoc ?b :trans-outs (mapcat #(arcs-outof pn %) (map :name (:trans ?b))))
    (assoc ?b :tplaces (map :target (:trans-outs ?b)))
    (assoc ?b :vplace-ins (arcs-into pn (:name (:VPLACE ?b))))
    (assoc ?b :strans (map #(name2obj pn (:source %)) (:vplace-ins ?b)))
    (assoc ?b :strans-ins (map (fn [tr] {:trans tr
                                         :ins (arcs-into pn (:name tr))})
                              (:strans ?b)))))

(defn vanish2spn
  "Remove vanishing places and IMMs that are attached. Add in replacements."
  [pn]
  (reduce (fn [pn place]
            (let [b (vanish-binds pn place)]
              (as-> pn ?pn
                (reduce (fn [pn ar] (eliminate-pn pn ar)) ?pn (map :trans (:strans-ins b)))
                (reduce (fn [pn ar] (eliminate-pn pn ar)) ?pn (mapcat :ins (:strans-ins b)))
                (reduce (fn [pn tr] (eliminate-pn pn tr)) ?pn (:strans b))
                (reduce (fn [pn ar] (eliminate-pn pn ar)) ?pn (:vplace-ins b))
                (eliminate-pn ?pn (:VPLACE b))
                (reduce (fn [pn ar] (eliminate-pn pn ar)) ?pn (:vplace-outs b))
                (reduce (fn [pn tr] (eliminate-pn pn tr)) ?pn (:trans b))
                (reduce (fn [pn ar] (eliminate-pn pn ar)) ?pn (:trans-outs b))
                (reduce (fn [pn cmd]
                          (let [new-trans (:new-trans cmd)]
                            (as-> pn ?pnn
                              (add-pn ?pnn {:name (:name new-trans) :tid (next-tid ?pnn)
                                            :type :exponential :rate (:rate new-trans)})
                              (add-pn ?pnn (make-arc ?pnn (:name new-trans) (:name (:send-to cmd))))
                              (update ?pnn ; Add tokens lost from the vanishing place, if any. 
                                      :places
                                      (fn [places]
                                        (vec (map (fn [pl] (if (= (:name pl) (:name (:send-to cmd)))
                                                             (update-in pl [:initial-marking]
                                                                        #(+ % (:gets-tokens (:send-to cmd))))
                                                             pl))
                                                  places))))
                              (reduce (fn [pn ar]
                                        (add-pn pn (make-arc pn (:source ar) (:name new-trans)
                                                             :type (:type ar)
                                                             :multiplicity (:multiplicity ar))))
                                      ?pnn
                                      (:receive-from-make-copy cmd)))))
                        ?pn
                        (vanish-cmd b)))))
          pn
          (find-vanish pn)))

(defn find-vanish
  [pn]
  (filter (fn [pl]
            (let [arcs-out (arcs-outof pn (:name pl))
                  trans (map :target arcs-out)]
              (and ; POD these may be too restrictive. We'll see.
               (every? #(immediate? pn %) trans)
               ;; Each trans has just one in and one out.
               (every? #(= 1 (count (arcs-outof pn %))) trans)
               (every? #(= 1 (count (arcs-into pn %))) trans))))
          (:places pn)))

(defn name-prime
  [n1 n2]
  (keyword (str (subs (str n1) 1) "-" (subs (str n2) 1))))

(defn vanish-cmd
  "Creates 'command vectors' providing instructions to create new transitions and arcs."
  [binds]
  (as-> nil ?cmd
    (vec (reduce (fn [cmd tplace]
                   (into cmd
                         (map (fn [strans-in]
                                {:new-trans {:name (name-prime (:name (:trans strans-in)) tplace)
                                             ;; POD rate is s-rate*t-weight, but I'm using default weight=1
                                             :rate (/ (:rate (:trans strans-in)) (count (:trans binds)))} 
                                 :send-to {:name tplace :gets-tokens 0}
                                 :receive-from-make-copy (:ins strans-in)})
                              (:strans-ins binds))))
                 ?cmd
                 (:tplaces binds)))
    ;; The idea here is that the vanishing place might have a token. We should conserve it.
    (update-in ?cmd [0 :send-to :gets-tokens]  #(+ % (:initial-marking (:VPLACE binds))))))

;;;------- Diagnostic

;;;(def m (read-pnml "data/tight-join.xml"))
;;;(def bbb (join-binds m (first (find-joins m))))
;;;(ppprint (join-cmd m bbb (first (:places* bbb))))

;;;(def m (read-pnml "data/join2.xml"))
;;;(def bbb (join-binds m (first (find-joins m))))
;;;(ppprint (join-cmd m bbb (first (:places* bbb))))

;;;(def m (read-pnml "data/join3.xml"))
;;;(def bbb (join-binds m (first (find-joins m))))
;;;(ppprint (join-cmd m bbb (first (:places* bbb))))



(defn zero-step
  [filename]
  (read-pnml filename))

(defn one-step
  [filename]
  (-> (read-pnml filename)
      (split2spn)))

(defn two-step
  [filename]
  (-> (read-pnml filename)
      (split2spn)
      (join2spn)))

(defn full-step
  [filename]
  (-> (read-pnml filename)
      (gspn2spn)))

(defn run-step
  [filename]
  (-> (read-pnml filename)
      (gspn2spn)
      (pn-steady-state)))

      
(defn find-arc
  [pn source target]
  (filter #(and (= (:source %) source)
                (= (:target %) target))
          (:arcs pn)))
                      
;;; =========== Steady State Calculation ===============================================
(declare Q-matrix steady-state-props avg-tokens-on-place)
(defn pn-steady-state
  [pn]
  "Calculate and add steady-state properties to the argument PN."
  (-> pn
      (gspn2spn)
      (reachability)
      (Q-matrix)
      (steady-state-props)))

;;; The transition rate M --> Mp  (i not= j) is the sum of the firing rates of
;;; the transitions enabled by the markings Mi that generate Mj. 
;;; Where M=Mp, it is negative of the the sum of the firing rates enabled.
(defn calc-rate 
  "Return the transition rate between marking M and Mp."
  [pn m mp]
  (let [graph (:reach pn)]
    (if (= m mp)
      (- (reduce #(+ %1 (:rate %2)) 0.0 (filter #(and (= (:M %) m) (not (= (:Mp %) m))) graph)))
      (reduce #(+ %1 (:rate %2)) 0.0 (filter #(and (= (:M %) m) (= (:Mp %) mp)) graph)))))
    
(defn Q-matrix 
  "Calculate the infinitesimal generator matrix from the reachability graph"
  [pn & {:keys [force-ordering]}] ; force-ordering is for debugging.
  (if (:failure pn)
    pn
    (let [states (or force-ordering (distinct (map :M (:reach pn))))
          size (count states)]
      (as-> pn ?pn
        (assoc ?pn :Q ; POD someday, this will be parametric. 
               (vec (map
                     (fn [irow]
                       (vec (map (fn [icol] (calc-rate ?pn (nth states (dec irow)) (nth states (dec icol))))
                                 (range 1 (inc size)))))
                     (range 1 (inc size)))))
        (assoc ?pn :states states)))))

(defn zero-pos
  "Return the position of the value closest to zero."
  [v]
  (let [size (count v)]
    (loop [i 1
           mini (abs (first v))
           min-pos 0]
      (cond (= i size) min-pos,
            (< (abs (nth v i)) mini)
            (recur (inc i) (abs (nth v i)) i),
            :else
            (recur (inc i) mini min-pos)))))

(defn steady-state-props
  "Calculate steady-state props for a PN for which the Q matrix has been generated."
  [pn]
  (if (:failure pn)
    pn
    (let [sol (ml/svd (m/array (:Q pn))) ; U makes sense xA=0 --> left null space.
          svec (vec (m/get-column (:U sol) (zero-pos (vec (:S sol)))))
          scale (apply + svec)]
      (as-> pn ?pn
        (assoc ?pn :steady-state (zipmap (:states ?pn) (map #(/ % scale) svec)))
        (assoc ?pn :avg-tokens-on-place (avg-tokens-on-place ?pn))
        (dissoc ?pn :states)))))

(defn avg-tokens-on-place
  "Calculate the average number of tokens on a place."
  [pn]
  (let [steady (:steady-state pn)
        mk (:marking-key pn)]
    (zipmap mk
            (map (fn [place]
                   (let [place-pos (.indexOf mk place)]
                     (reduce (fn [sum [state prob]] (+ sum (* (nth state place-pos) prob)))
                             0.0
                             steady)))
                 mk))))





                             
