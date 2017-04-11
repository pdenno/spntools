(ns gov.nist.spntools.util.reach
  (:require [clojure.data.xml :as xml :refer (parse-str)]
            [clojure.pprint :refer (cl-format pprint pp)]
            [clojure.core.matrix :as m :refer :all]
            [clojure.math.combinatorics :as combo]
            [gov.nist.spntools.util.utils :refer :all]
            [gov.nist.spntools.util.pnml :refer (read-pnml)]))

;;; To Do: Implement place capacity restrictions. (maybe)
;;;     * Instead of all these +max-rs+ etc. might want a system wide ^:dynamic
;;;       binding of variable values in a map. (Call the current things +default-...)
;;;     * Why am I keeping :Mp and :fire ? Replace links with markings. - NOT GONNA DO IT
;;;     * I think vanishing places that are inside a network (like P4 in qo10) can be
;;;       removed from the analysis. DOUBTFUL
;;;     * Eliminate summarize-reach; It should be one line in reachability.
;;;     * Rewrite the reduction of :explore to use next-link on every step of vpaths :fire
;;      * Maybe write the find-link / filter-links thing. Needs thought on efficiency. 

(def +zippy+ (atom nil))

(defn fireable? 
  "Return true if transition is fireable under the argument marking."
  [pn mark tr-name]
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
(defn next-mark
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
(defn next-links
  "Return nil or a vector of maps [{:M <tail-marking> :trans <transition that fired> :Mp <head-marking>}...]
   which contain the argument state :M and unexplored states, :Mp reachable by firing :trans.
   Returned links have adjusted weights when transitions are immediate."
  ([pn mark check-list]
   (let [trns
         (as-> (map :name (:transitions pn)) ?trns
           (filter #(fireable? pn mark %) ?trns)
           (if (some #(immediate? pn %) ?trns) (filter #(immediate? pn %) ?trns) ?trns)
           (if check-list
             (remove (fn [trn] (some #(and (= mark (:M %)) (= trn (:fire %))) (check-list pn))) ?trns)
             ?trns))
         imm? (immediate? pn (first trns))
         trs (map #(name2obj pn %) trns)
         sum (when imm? (apply + (map :rate trs)))]
     (not-empty
      (vec
       (map (fn [tr]
              {:M mark
               :fire (:name tr)
               :Mp (next-mark pn mark (:name tr))
               :rate (if imm? (/ (:rate tr) sum) (:rate tr))})
            trs)))))
  ([pn mark] (next-links pn mark false)))

(def +k-bounded+ (atom 10)) ; Maybe better than (or addition to) k-bounded would be size of :explored
(def +max-rs+  "reachability set size" (atom 5000)) 
(declare renumber-pids check-reach tangible? vanishing? in-loop-checks loop-reduce summarize-reach)
(declare initial-tangible-state vanish-paths terminate-vpath)

(defn reachability
  "Compute the reachability graph (:M2Mp) depth-first starting at the initial marking, 
   removing vanishing states on-the-fly using the algorithm of Knottenbelt, 1996."
  [pn]
  (reset! +diag+ [])
  (as-pn-ok-> pn ?pn
    (dissoc ?pn :explored)
    (assoc ?pn :vpath-rates [])
    (renumber-pids ?pn)
    (initial-tangible-state ?pn)
    (assoc ?pn :explored (next-links ?pn (:initial-tangible ?pn)))
    (assoc ?pn :St (:explored ?pn), :Sv [])
    (loop [pn ?pn]
      ;(println "Sv = " (:Sv pn))
      ;(println "St = " (:St pn) "\n")
      (as-pn-ok-> pn ?pn2
        (reduce (fn [pn v-link] (vanish-paths pn v-link)) ?pn2 (:Sv ?pn2))
        (assoc ?pn2 :Sv [])
        (in-loop-checks ?pn2)
        (if (empty? (:St ?pn2))
          ?pn2                      
          (let [nexts (next-links ?pn2 (:Mp (first (:St ?pn2))) :explored)
                tang? (and nexts (tangible? ?pn2 (-> nexts first :M)))]
            (recur (-> ?pn2 
                       (update :explored into nexts)
                       (assoc :St (into (or nexts []) (vec (rest (:St ?pn2)))))
                       (assoc :Sv (into (if tang? [] nexts) (:Sv ?pn2)))))))))
    (loop-reduce ?pn)
    (summarize-reach ?pn)
    (check-reach ?pn)))

(defn match-root
  "Find the tangible root that lead to the v-link. It should be near the top of :explored."
  [pn v-link]
  (let [state (:M v-link)]
    (some #(when (= (:Mp %) state) %) (:explored pn))))

(defn vanish-paths
 "Navigate from root to all ending tangible states. 
  Return with vpath-rates updated."
  [pn v-link]
  (as-> pn ?pn
      (assoc ?pn :explored-v (vector (:root pn)))
      (assoc ?pn :paths (vector (vector v-link)))
      (assoc ?pn :root (match-root ?pn v-link))
      (loop [pn ?pn]
        (as-> pn ?pn2
          (if (empty? (:paths ?pn2)) ; calc-vpath-rate removes one for each :tangible. 
            ?pn2
            (let [current (-> ?pn2 :paths first last :Mp)
                  nexts (next-links ?pn2 current :explored-v)
                  tang? (and nexts (tangible? ?pn2 (-> nexts first :M)))]
              (recur (as-> ?pn2 ?pn3
                       (if nexts
                         (update ?pn3 :explored-v into nexts)
                         (terminate-vpath ?pn3 current)) ; loops back -- POD NOT SURE
                       (if tang?
                         (reduce (fn [pn _] (terminate-vpath pn)) ?pn3 nexts)
                         (assoc ?pn3 :paths ; Create for current path a new path for each new vanishing state
                                (into (vec (map #(conj (-> ?pn3 :paths first) %) nexts))
                                      (-> ?pn3 :paths rest))))))))))))

;;; POD I think it is sufficient to find a single marking. 
(defn initial-tangible-state 
  "Return an initial tangible state, given a PN where the initial marking might not be tangible."
  [pn]
  (let [im (:initial-marking pn)]
    (as-> pn ?pn
      (if (tangible? ?pn im)
        (assoc ?pn :initial-tangible im)
        (as-> ?pn ?pn2
          (assoc ?pn2 :explored-i [])
          (loop [pn ?pn2
                 stack (vec (next-links ?pn2 im :explored-i))]
            (as-> pn ?pn3
              (update ?pn3 :explored-i into stack)
              (cond (tangible? ?pn3 (:M (first stack)))
                    (assoc ?pn3 :initial-tangible (:M (first stack))),
                    (empty? stack)
                    (assoc ?pn3 :failure {:reason :no-tangible-state}),
                    :else
                    (recur ?pn3
                           (vec (rest (into stack (next-links ?pn3 (:Mp (first stack)) :explored-i))))))))
          (dissoc ?pn2 :explored-i))))))

;;; The maps look like this:
;;;   Typical:  {:M <root> :fire [<root-to-v> <v> ...<v> <v-to-tang>] :Mp <tangible>}"
;;;   Loop   :  {:M <root> :fire [<root-to-v> <v> ...<v>] :Mp <not relevant> :loop? true}"
(defn terminate-vpath 
  "Calculate (add to) :vpath-rates, the rate from the root to a tangible state reachable 
   through a path ending on the next tangible state reachable. Drop the path from :paths."
  ([pn] (terminate-vpath pn false))
  ([pn loop?]
   (if-let [path (-> pn :paths first)]
     (as-> pn ?pn
       (update ?pn :vpath-rates
               conj
               {:M (-> ?pn :root :M)
                :fire (vec (conj (map :fire path) (-> ?pn :root :fire)))
                :Mp (-> path last :Mp)
                :rate (reduce * (-> ?pn :root :rate) (map :rate path))
                :loop? loop?})
       (if loop?
         (assoc ?pn :paths [])
         (assoc ?pn :paths (-> ?pn :paths rest vec))))
     pn)))

(declare links-on links-off vanishing2subnets Qt-calc Qtv-calc Pv-calc Pvt-calc)
(declare Q-prime merge-subnets loop-clean-paths loop-add-rates)

(defn loop-reduce
  "Update the :vpath-rates for a looping subnet."
  [pn]
  (as-> pn ?pn
    (reduce (fn [pn [k subnet]]
              (as-> pn ?pn
                (assoc ?pn :subnet subnet)
                (Qt-calc ?pn)
                (Qtv-calc ?pn)
                (assoc ?pn :Pv (Pv-calc ?pn))
                (assoc ?pn :Pvt (Pvt-calc ?pn))
                (assoc ?pn :loop-rates (Q-prime (:Qt ?pn) (:Qtv ?pn) (:Pv ?pn) (:Pvt ?pn)))
                (loop-clean-paths ?pn)
                (loop-add-rates ?pn k)))
            ?pn (vanishing2subnets ?pn))
    #_(dissoc ?pn :subnet :Qt :Qtv :Pv :Pvt :loop-rates 
            :Qt-states :Qtv-states :loop-rates)))

(defn Qt-calc
  "Calculate the vector of rates from the root directly to tangible states."
  [pn]
  (let [root (-> pn :root :M)]
    (as-> pn ?pn 
      (assoc ?pn :Qt-states (vec (filter #(tangible? ?pn %) ; look for 'exiting vanishing'
                                         (map :Mp (filter #(vanishing? ?pn (:M %)) (:subnet ?pn))))))
      (assoc ?pn :Qt (vec (map (fn [target]
                                 (reduce (fn [r link] (+ r (:rate link)))
                                         0.0
                                         (filter #(and (= root (:M %)) (= target (:Mp %))) (:explored ?pn))))
                               (:Qt-states ?pn)))))))

(defn Qtv-calc
  "Calculate the vector of rates from the root directly to vanishing states."
  [pn]
  (let [root (-> pn :root :M)]
    (as-> pn ?pn
      (assoc ?pn :Qtv-states (distinct (vec (filter #(vanishing? ?pn %) (map :M (:subnet ?pn))))))
      (assoc ?pn :Qtv (vec (map (fn [target]
                                  (reduce (fn [r link] (+ r (:rate link)))
                                          0.0 
                                          (filter #(and (= root (:M %)) (= target (:Mp %))) (:explored ?pn))))
                                (:Qtv-states ?pn)))))))

(defn Pv-calc
  "Calculate matrix of weights among the vanishing states"
  [pn]
  (vec (map (fn [r]
              (vec (map (fn [c]
                          (reduce (fn [sum link] (+ sum (:rate link)))
                                  0.0
                                  (filter #(and (= (:M %) r) (= (:Mp %) c))
                                          (:subnet pn))))
                        (:Qtv-states pn))))
            (:Qtv-states pn))))


(defn Pvt-calc [pn]
    (vec (map (fn [r]
              (vec (map (fn [c]
                          (reduce (fn [sum link] (+ sum (:rate link)))
                                  0.0
                                  (filter #(and (= (:M %) r) (= (:Mp %) c))
                                          (:subnet pn))))
                        (:Qt-states pn))))
              (:Qtv-states pn))))

(defn loop-clean-paths
  "Remove from :vpath-rates any path that has in its :fire something which
  matches a :fire from :subnet; it has been addressed by the loop."
  [pn]
  (let [fires (map :fire (:subnet pn))]
    (-> pn 
        (assoc :vpath-rates
               (vec (reduce (fn [vp fire]
                              (remove (fn [vr] (some #(= fire %) (:fire vr))) vp))
                            (:vpath-rates pn)
                            fires)))
        (assoc :explored
               (vec
                (distinct ; POD not sure why this is necessary.
                 (reduce (fn [exp fire] (remove #(= fire (:fire %)) exp))
                         (:explored pn)
                         fires)))))))

(defn loop-add-rates
  "Add rates between the root state and the tangible states exiting the loop."
  [pn key] ; Use :fire key multi-loop debugging. Otherwise I like :fire :loop!
  (let [root (-> pn :root :M)]
    (update pn
            :explored
            into
            (map (fn [[mp r]] {:M root :fire :loop! :Mp mp :rate r})
                 (zipmap (:Qt-states pn) (:loop-rates pn))))))

(defn summarize-reach
  "Merge :vpath-rates and :explored (sans vanishing) resulting in :M2Mp"
  [pn]
  (as-> pn ?pn ; POD Investigate the need for distinct here; its a DFS thing. 
    (update ?pn :explored (fn [e] (vec (filter #(and (tangible? ?pn (:Mp %))
                                                     (tangible? ?pn (:M %)))
                                               (distinct e)))))
   (assoc ?pn :M2Mp (into (:explored ?pn) (:vpath-rates ?pn)))
   #_(dissoc ?pn :vpath-rates :explored :explored-v :St :Sv :paths :root)))

(defn clean-explored
  "Remove from :explored everything state transition achieved on a vpath."
  [pn])


(defn vanishing2subnets [pn]
  "Create a map of subnets that can be solved independently."
  (as-> (filter :loop? (:vpath-rates pn)) ?subnets
    (zipmap (map :fire ?subnets) (map #(links-on pn %) ?subnets))
    (reduce (fn [s key] (update s key into (links-off pn (get s key))))
            ?subnets (keys ?subnets))
    (merge-subnets ?subnets)))

(defn merge-subnets
  "Combine entries in the argument map that have overlapping markings."
  [subnets]
  (let [progress (atom true)]
    (loop [s subnets]
      (reset! progress false)
      (let [combos (combo/combinations (keys s) 2)
            subs (reduce (fn [s1 [p1 p2]]
                           (if (empty? (clojure.set/intersection (set (get s1 p1)) (set (get s1 p2))))
                             s1
                             (do (reset! progress true)
                                 (as-> s1 ?s
                                   (assoc ?s (vector p1 p2) (distinct (into (get ?s p1) (get ?s p2))))
                                   (dissoc ?s p1 p2)))))
                         s combos)]
        (if @progress (recur subs) subs)))))
      
(defn links-on
  "Find all the simple links that are part of the argument path link."
  [pn plink]
  (distinct 
   (reduce (fn [accum trn]
             (let [prev (if (empty? accum) (:M plink) (-> accum last :Mp))
                   tr (name2obj pn trn)]
               (conj accum
                     {:M prev
                      :fire trn
                      :Mp (next-mark pn prev trn)
                      :type (:type tr)
                      :rate (:rate tr)})))
           []
           (:fire plink))))

(defn links-off
  "Find all the simple links that are not among those found by links-on 
   but share a marking. Add these to set generated by links-on."
  [pn link-set]
  (let [marks (into (map :M link-set) (map :Mp link-set))
        other-paths (filter (fn [vpath] (some (fn [m] (or (= (:M vpath) m) (= (:Mp vpath) m))) marks))
                            (:vpath-rates pn))]
    (reduce (fn [ls op] (distinct (into ls (links-on pn op))))
            link-set
            other-paths)))

;;; Note: If m/inverse is Gauss-Jordan, it is O(n^3) 20 states 8000 ops. Could be better.
;;; Knottenbelt suggest LU decomposition. 
(defn Q-prime
  "Calculate Q' = Qt + Qtv (I-Pv)^-1 Pvt This is the rates between
   a tangible state and its tangible descendant states through a network
   of vanishing states."
  [Qt Qtv Pv Pvt]
  (let [Qt (m/array Qt)
        Qtv (m/transpose (m/array Qtv))
        v (count Pv)
        Pv (m/array Pv)
        Pvt (m/array Pvt)
        N  (m/inverse (m/sub (m/identity-matrix v v) Pv))] ; N = (I - Pv)^-1
    (when N ; If couldn't calculate inverse, then 'timeless trap'
      (m/add Qt (m/mmul Qtv N Pvt)))))

(defn in-loop-checks [pn]
  (cond 
    (some #(> % @+k-bounded+) (:Mp (first (:St pn))))
    (assoc pn :failure {:reason :not-k-bounded :marking (:Mp (first (:St pn)))}),
    (> (count (:M2Mp pn)) @+max-rs+)
    (assoc pn :failure {:reason :exceeds-max-rs :set-size (count (:M2Mp pn))}),
    :else pn))

(defn check-reach
  "Check for reachability-related errors."
  [pn]
  (let [m  (set (distinct (map #(:M %) (:M2Mp pn))))
        mp (set (distinct (map #(:Mp %) (:M2Mp pn))))
        m-mp (clojure.set/difference m mp)
        mp-m (clojure.set/difference mp m)]
  (as-pn-ok-> pn ?pn
    (if (and (empty? m-mp) (empty? mp-m))
      ?pn
      (assoc ?pn :failure {:reason :absorbing-states
                           :data {:m-not-mp m-mp :mp-not-m mp-m}}))
    (if (> (count (:M2mp pn)) @+max-rs+)
      (assoc pn :failure {:reason :exceeds-max-rs :set-size (count (:M2Mp ?pn))})
      ?pn)
    (if (empty? (:M2Mp ?pn))
      (assoc ?pn :failure {:reason :null-reachability-graph})
      ?pn))))

(defn tangible? [pn mark]
  "Return true if marking MARK (not a link) is tangible. 
   A marking is vanishing if it enables an immediate transitions. "
  (not-any? #(immediate? pn %) (map :fire (next-links pn mark))))

(defn vanishing? [pn mark]
  "Return true if marking MARK (not a link) is vanishing. 
   A marking is vanishing if it enables an immediate transitions. "
  (not (tangible? pn mark)))

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
                (reduce (fn [order id] (assoc-in order [id :pid] id))
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
  (let [m2mp (:M2Mp pn)]
    (if (every?
         (fn [tr] (some #(= tr (:fire %)) m2mp))
         (map :name (:transitions pn)))
      pn
      (assoc pn :failure {:reason :live?}))))
