(ns gov.nist.spntools
  (:require [clojure.data.xml :as xml :refer (parse-str)]
            [clojure.pprint :refer (cl-format pprint pp)]
            [clojure.math.combinatorics :as combo]
            [gov.nist.spntools.util.reach :as reach :refer (reachability)]
            [gov.nist.spntools.util.pnml :as pnml :refer (read-pnml reorder-places)]
            [gov.nist.spntools.util.utils :as utils :refer :all]
            [clojure.core.matrix :as m :refer :all]
            [clojure.core.matrix.linear :as ml :refer (svd)]))

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

(declare join2spn)
;;;   ___    ___
;;;  (   )  (   )   places-top   May be one or more
;;;   ---    ---
;;;    |      |     top-ins   -- These may include things from the places* 
;;;    V      V
;;;   ===    ===    trans [multiple]
;;;    |      |     places-ins [multiple]
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
(defschema :join
  {:name :join
   :focus-obj :IMM
   :topology
   {:name :places-top :type :place :multiplicity [1,1] :plan :keep
    :child
    {:name :top-ins :type :arc :multiplicity [1,-1] :plan :replace 
     :child 
     {:name :trans :type :normal :multiplicity [1,-1] :plan :eliminate 
      :child 
      {:name :places-in :type :arc :multiplicity [1,-1] :plan :eliminate 
       :child
       {:name :places* :type :place :multiplicity [1,-1] :plan :keep 
        :child
        {:name :imm-ins :multiplicity [1,-1] :plan :eliminate :type :arc 
         :child
         {:name :IMM :type :immediate :multiplicity [1,1] :plan :eliminate 
          :child
          {:name :place-bottom-in :type :normal :multiplicity [1,1] :plan :eliminate 
           :child
           {:name :place-bottom :type :place :multiplicity [1,1] :plan :keep}}}}}}}}}})

(defn join-binds
  "Return a map identifying a set of things involved in the pattern shown above."
  [pn imm]
  (let [arcs (:arcs pn)
        trs (:transitions pn)
        places (:places pn)]
    (as-> {} ?b
      (assoc ?b :IMM (:name imm))
      (assoc ?b :imm-ins (filter #(= (:IMM ?b) (:target %)) arcs))
      (assoc ?b :places* (map :source (:imm-ins ?b)))
      (assoc ?b :places-ins (filter (fn [ar] (some #(= (:target ar) %) (:places* ?b))) arcs))
      (assoc ?b :trans (filter #(some (fn [pl] (= (:name %) (:source pl))) (:places-ins ?b)) trs))
      
      (assoc ?b :top-ins (filter #(some (fn [tr] (= (:name tr) (:target %))) (:trans ?b)) arcs))
      
      (assoc ?b :place-bottom-in (some #(when (= (:source %) (:IMM ?b)) %) arcs))
      (assoc ?b :place-bottom (some #(when (= (:name %) (:target (:place-bottom-in ?b))) %) places))
      ;; Every :normal arc with target in a trans has this place as its source.
      (let [narcs (filter (fn [ar] (and (= (:type ar) :normal)
                                        (some #(= (:target ar) (:name %)) (:trans ?b))))
                          (:top-ins ?b))]
        (assoc ?b :places-top (distinct (map :source narcs))))
      (assoc ?b :preserve-top-ins (remove (fn [tin] (some #(= (:source tin) %) (:places-top ?b))) (:top-ins ?b)))
      (assoc ?b :top-ins (remove (fn [tin] (some #(= % tin) (:preserve-top-ins ?b))) (:top-ins ?b))))))

(defn join-cmd
  "Creates 'command vectors' each element of which provides instructions 
   concerning how to create a new transition and its arcs."
  [pn binds owner]
  (let [owner-t (:source (some #(when (= owner (:target %)) %) (:places-ins binds)))
        rate (:rate (name2obj pn owner-t))
        imm (:IMM binds)
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
                 (let [n (new-name imm owner "-first")]
                   (conj accum {:name n
                                :rate rate
                                :preserves (into (map #(assoc % :target n) receive-preserves)
                                                 (map #(assoc % :source % n) send-preserves))
                                :receive-tops (filter #(first (paths-to pn % owner 4)) (:places-top binds))
                                :receive-inhibitors others
                                :send-activator owner})))
          (= in-front (count others))
          (recur (inc in-front)
                 (let [n (new-name imm owner "-last")]
                   (conj accum {:name n
                                :rate rate
                                :receive-tops (filter #(first (paths-to pn % owner 4)) (:places-top binds))
                                :preserves (into (map #(assoc % :target  n) receive-preserves)
                                                 (map #(assoc % :source n) send-preserves))
                                :receive-activators others
                                :send-activator (:name (:place-bottom binds))})))  
          :else
          (recur (inc in-front)
                 (into accum 
                       (map (fn [ahead]
                              (let [n (new-name-ahead imm owner ahead)] 
                                {:name n
                                 :rate rate
                                 :receive-tops (filter #(first (paths-to pn % owner 4)) (:places-top binds))
                                 :preserves (into (map #(assoc % :target n) receive-preserves)
                                                  (map #(assoc % :source n) send-preserves))
                                 :receive-inhibitors (remove (fn [o] (some #(when (= o %) %) ahead)) others)
                                 :send&receive-activators ahead
                                 :send-activator owner}))
                              (combo/combinations others in-front)))))))))
                                    
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
        new-cnt (atom 0)]
    (reduce (fn [pn imm]
              (let [b (join-binds pn imm)] ; Consider moving all this inside the next reduce
                (as-> pn ?pn               ; Can't really do that because join-binds needs to 
                  (eliminate-pn ?pn imm)   ; See the original structure.
                  (reduce (fn [pn ar] (eliminate-pn pn ar)) ?pn (:top-ins b))
                  (reduce (fn [pn ar] (eliminate-pn pn ar)) ?pn (:preserve-top-ins b)) 
                  (reduce (fn [pn tr] (eliminate-pn pn tr)) ?pn (:trans b))
                  (reduce (fn [pn ar] (eliminate-pn pn ar)) ?pn (:places-ins b))
                  (reduce (fn [pn ar] (eliminate-pn pn ar)) ?pn (:imm-ins b))
                  (eliminate-pn ?pn (:place-bottom-in b))
                  (reduce (fn [pn cmd-vec] ; cmd-vec, from join-cmd is commands over one of :places*
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
                          ?pn 
                          (map #(join-cmd pn b %) (:places* b))))))
            pn
            (find-joins pn))))


;;;     (   ) ( )    splaces             
;;;      | |   |     strans-ins          
;;;      v v   v
;;;      XXXX XXXX   strans 
;;;        |   |     
;;;        V   V     place-ins 
;;;        ------
;;;       (      )   VPLACE 
;;;        ------
;;;        |    |     place-outs 
;;;        V    V
;;;     XXXX   XXXX   trans (focus, immediates) 
;;;      |      |    
;;;      V      V     trans-outs 
;;;     ---    ---
;;;    (   )  (   )    tplaces                           
;;;     ---    ---
(defschema :vanish
  {:name :vanish,
   :type :source,
   :topology
   {:name :splaces, :type :place, :multiplicity [1,-1], :plan :keep,
    :search #(arcs-into %1 %2),
    :child
    {:name :strans-ins, :type :arc, :multiplicity [1,-1], :plan :keep,
     :search-up #(name2obj %1 (:source %2)) 
     :child
     {:name :strans, :type :normal, :multiplicity [1,-1], :plan :keep,
      :search-up #(arcs-into %1 %2),
      :child
      {:name :place-ins, :type :arc, :multiplicity [1,-1], :plan :eliminate,
       :search-up #(name2obj %1 (:source %2)) 
       :child
       {:name :VPLACE, :type :place, :multiplicity [1,1], :plan :eliminate,
        :search #(arcs-into %1 %2),
        :child
        {:name :place-outs, :type :arc, :multiplicity [1,-1], :plan :eliminate,
         :search-up #(name2obj %1 (:source %2)) 
         :child
         {:name :trans, :type :focus, :multiplicity [1,-1], :plan :eliminate, ; <======= FOCUS
          :select #(filter (fn [x] (= :immediate (:type x))) (:transitions %)),
          :search #(arcs-outof %1 %2),
          :search-up #(arcs-into %1 %2),
          :child
          {:name :trans-outs, :type :arc, :multiplicity [1,-1], :plan :eliminate,
           :search #(name2obj %1 (:target %2)),
           :child
           {:name :tplaces :type :place :multiplicity [1,-1] :plan :keep}}}}}}}}}})


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
;;;(ppprint (join-cmd m bbb))
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





                            
                             
