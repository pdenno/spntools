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
;;;     * Eliminate summarize-reach; It should be one line in reachability.
;;;     * Rewrite the reduction of :explored to use next-link on every step of vpaths :fire
;;;     * Now that I've written terminating-tangibles, it could probably be adapted
;;;       to collect all the links needed to do the Q-prime calculation. 

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

(defn find-link
  [pn M trn list]
  (some #(when (and (= M (:M %)) (= trn (:fire %))) %) list))

;;; The target marking is completely specified by the source (marking at tail) and the transition.
(defn next-links
  "Return nil or a vector of maps [{:M <tail-marking> :trans <transition that fired> :Mp <head-marking>}...]
   which contain the argument state :M and unexplored states, :Mp reachable by firing :trans.
   Returned links have adjusted weights when transitions are immediate."
  ([pn mark] (next-links pn mark false))
  ([pn mark clist]
   (let [trns
         (as-> (map :name (:transitions pn)) ?trns
           (filter #(fireable? pn mark %) ?trns)
           (if (some #(immediate? pn %) ?trns) (filter #(immediate? pn %) ?trns) ?trns)
           (if clist
             (remove #(find-link pn mark % (if (keyword? clist) (clist pn) clist)) ?trns)
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
            trs))))))

(def +k-bounded+ (atom 10)) ; Maybe better than (or addition to) k-bounded would be size of :explored
(def +max-rs+  "reachability set size" (atom 5000)) 
(declare renumber-pids check-reach tangible? vanishing? in-loop-checks loop-reduce summarize-reach)
(declare initial-tangible-state reachability-loop vanish-paths terminate-vpath terminating-tangibles)

(defn reachability
  "Compute the reachability graph (:M2Mp) depth-first starting at the initial marking, 
   removing vanishing states on-the-fly using the algorithm of Knottenbelt, 1996."
  [pn]
  (reset! +diag+ [])
  (as-pn-ok-> pn ?pn
    (assoc ?pn :vpath-rates [])
    (renumber-pids ?pn)
    (initial-tangible-state ?pn)
    (assoc ?pn :explored (next-links ?pn (:initial-tangible ?pn)))
    (assoc ?pn :St (:explored ?pn), :Sv [])
    (assoc ?pn :Sv-explored [])
    (reachability-loop ?pn)
    (loop-reduce ?pn)
    (summarize-reach ?pn)
    (check-reach ?pn)))

(defn reachability-loop [pn]
  (loop [pn pn]
    ;;(println "St = " (:St pn))
    ;;(println "Sv = " (:Sv pn))
    (as-pn-ok-> pn ?pn
       (if-let [e (or (-> ?pn :Sv first) (-> ?pn :St first))]
         (update ?pn :explored conj e) 
         ?pn)
       (assoc ?pn :Sv (remove #(some (fn [[sve rt]] (and (= sve %) (= rt (:root ?pn))))
                                     (:Sv-explored ?pn))
                              (:Sv ?pn)))
       (assoc ?pn :Sv-explored (into (:Sv-explored ?pn) (map #(vector % (:root ?pn)) (:Sv ?pn))))
       (reduce (fn [pn v-link] (vanish-paths pn v-link)) ?pn (:Sv ?pn))
       (assoc ?pn :explored (remove #(immediate? ?pn (:fire %)) (:explored ?pn)))
       ;;(do (println "vpath-rates = " (:vpath-rates pn)) ?pn)
       (in-loop-checks ?pn)
       (if (empty? (:St ?pn))
         ?pn                      
         (let [nexts (next-links ?pn (:Mp (first (:St ?pn))) :explored)
               tang? (and nexts (tangible? ?pn (-> nexts first :M)))]
           ;;(println "nexts = " nexts "\n")
           (recur (-> ?pn 
                      (assoc :root (if tang? (first nexts) (first (:St ?pn))))
                      (assoc :St (into (if tang? nexts [])
                                       (vec (if (empty? (:Sv ?pn)) (rest (:St ?pn)) (:St ?pn)))))
                      (assoc :Sv (if tang? [] nexts)))))))))

(defn vanish-paths
 "Navigate from root to all ending tangible states. 
  Return with vpath-rates updated."
  [pn v-link]
  (as-> pn ?pn
      (assoc ?pn :explored-v (vector (:root pn) v-link))
      (assoc ?pn :paths (vector (vector v-link)))
      ;;(do (println "root = " (:root ?pn)) ?pn)
      (loop [pn ?pn]
        (as-> pn ?pn2
          (if (empty? (:paths ?pn2)) ; terminate-vpath removes one for each end.
           ?pn2
            (let [current (-> ?pn2 :paths first last :Mp)
                  nexts (next-links ?pn2 current :explored-v)
                  tang? (and nexts (tangible? ?pn2 (-> nexts first :M)))]
              (recur (as-> ?pn2 ?pn3
                       (if nexts
                         (update ?pn3 :explored-v into nexts)
                         (as-> ?pn3 ?pn4 ; else loops. Terminate it.
                           (terminate-vpath ?pn4 current)
                           (let [tt (terminating-tangibles ?pn4 current)]
                             (assoc ?pn4 :St (into (:terms tt) (:St ?pn4))))))
                       (if tang?
                         (reduce (fn [pn end]
                                   (as-> pn ?pn4
                                     ;;(do (println "end =" end) ?pn4)
                                     (assoc ?pn4 :St (into (vector end) (:St ?pn4)))
                                     (terminate-vpath ?pn4))) ; not loop back. ends.
                                 ?pn3 nexts)
                         (assoc ?pn3 :paths ; Create for current path a new path for each new vanishing state
                                (into (vec (map #(conj (-> ?pn3 :paths first) %) nexts))
                                      (-> ?pn3 :paths rest))))))))))))
;;; The maps look like this:
;;;   Typical:  {:M <root> :fire [<root-to-v> <v> ...<v> <v-to-tang>] :Mp <tangible>}"
;;;   Loop   :  {:M <root> :fire [<root-to-v> <v> ...<v>] :Mp <not relevant> :loop? true}"
(defn terminate-vpath 
  "Calculate (add to) :vpath-rates, the rate from the root to a tangible state reachable 
   through a path ending on the next tangible state reachable. Drop the path from :paths.
   If called with loop?=true do all the paths on :paths -- they share a root, that's all."
  ([pn] (terminate-vpath pn false))
  ([pn loop?]
   ;;(println "terminate-vpath....")
   ;; If loop, do them all. don't worry about :Mp termination nor :rate
   (let [paths (if loop?
                 (:paths pn) ; POD next line is due to it being called w/o a path! FIX THIS!
                 (if-let [p (-> pn :paths first)]
                   (list p)
                   []))]
     (reduce (fn [pn path] ; loop do them all.
               (as-> pn ?pn
                 (update ?pn :vpath-rates
                         conj
                         {:M (-> ?pn :root :M)
                          :fire (vec (conj (map :fire path) (-> ?pn :root :fire)))
                          :Mp (if loop? :NA (-> path last :Mp))
                          :rate (if loop? :NA (reduce * (-> ?pn :root :rate) (map :rate path)))
                          :loop? loop?})
                 ;;(do (println "---Added " (last (:vpath-rates ?pn))) ?pn)
                 (assoc ?pn :paths (-> ?pn :paths rest vec))))
             pn
             paths))))

(defn terminating-tangibles
  "Return a list of tangible states that can be reached from the root mark."
  [pn root-mark]
  (loop [accum []
         explored []
         paths (vec (map vector (next-links pn root-mark)))]
    (let [nexts (when (not-empty paths) (next-links pn (-> paths first last :Mp) explored))
          tang? (and (not-empty nexts) (tangible? pn (-> nexts first :M)))]
      (if (empty? paths)
        (do ;(println "IN TT: explored =" explored)
            {:terms accum :explored explored})
          (recur
           (if tang? (into accum nexts) accum)
           (into explored nexts)
           (if (or tang? (empty? nexts))
             (rest paths)
             (into (vec (map #(conj (first paths) %) nexts)) (rest paths))))))))

;;; POD I think it is sufficient to find a single marking. 
(defn initial-tangible-state 
  "Set :initial-tangible state, given a PN where the initial marking might not be tangible."
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

(declare links-on add-links-off vanishing2subnets Qt-calc Qtv-calc Pv-calc Pvt-calc)
(declare Q-prime merge-loops loop-clean-vpaths loop-add-rates)


;;;================================================================================
;;; This is toplevel for reduction of loops; called from reachability. 
(defn loop-reduce
  "Update the :vpath-rates for a looping subnet."
  [pn]
  (as-> pn ?pn
    (assoc ?pn :explored (distinct (:explored ?pn))) ; POD I really doubt this will work for two loops!
    (reduce (fn [pn [k subnet]]
              (as-> pn ?pn
                (assoc ?pn :subnet subnet)
                (assoc ?pn :root-mark (-> ?pn :subnet first :root)) ; POD UGH!
                (Qt-calc ?pn)
                (Qtv-calc ?pn)
                (assoc ?pn :Pv (Pv-calc ?pn))
                (assoc ?pn :Pvt (Pvt-calc ?pn))
                (assoc ?pn :loop-rates (Q-prime (:Qt ?pn) (:Qtv ?pn) (:Pv ?pn) (:Pvt ?pn)))
                (loop-clean-vpaths ?pn)
                (loop-add-rates ?pn k)))
            ?pn
            (vanishing2subnets ?pn))
        #_(dissoc ?pn :subnet :Qt :Qtv :Pv :Pvt :loop-rates 
                  :Qt-states :Qtv-states :loop-rates)))

(defn vanishing2subnets [pn]
  "Create a map of subnets that can be solved independently."
    (as-> (filter :loop? (:vpath-rates pn)) ?loops
      (zipmap (map :fire ?loops) (map #(add-links-off pn (links-on pn %) %) ?loops))
      (merge-loops ?loops)))

(defn merge-loops
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
  [pn vpath]
  (let [root (:M vpath)]
    (distinct 
     (reduce (fn [accum trn]
             (let [prev (if (empty? accum) (:M vpath) (-> accum last :Mp))
                   tr (name2obj pn trn)]
               (conj accum
                     {:M prev
                      :fire trn
                      :Mp (next-mark pn prev trn)
                      :type (:type tr)
                      :root root
                      :rate (:rate tr)}))) ; POD Is this getting the normalized weight?
             []
             (:fire vpath)))))

(defn add-links-off
  "Find all the simple links that are not among those found by links-on 
   but share a marking. Add these to the set generated by links-on."
  [pn link-set vpath] 
  (let [marks-on (set (into (map :M link-set) (map :Mp link-set)))
        other-paths
        (filter (fn [vpath]
                  (let [link-set-off (links-on pn vpath)
                        marks-off (set (into (map :M link-set-off)
                                             (map :Mp link-set-off)))]
                    (not-empty (clojure.set/intersection marks-on marks-off))))
                  (remove #(= % vpath) (:vpath-rates pn)))]
    (reduce (fn [ls op] (distinct (into ls (links-on pn op))))
            link-set
            other-paths)))

(defn loop-clean-vpaths
  "Remove from :vpath-rates any path that has in its :fire something which
  matches a :fire from :subnet; it has been addressed by the loop."
  [pn]
  (let [fires (map :fire (:subnet pn))]
    (-> pn 
        (assoc :vpath-rates
               (vec (reduce (fn [vp fire]
                              (remove (fn [vr] (some #(= fire %) (:fire vr))) vp))
                            (:vpath-rates pn)
                            fires))))))

(defn loop-add-rates
  "Add rates between the root state and the tangible states exiting the loop."
  [pn key] ; Use :fire key multi-loop debugging. Otherwise I like :fire :loop!
  (let [root (:root-mark pn)]
    (update pn
            :explored
            into
            (map (fn [[mp r]] {:M root :fire :loop! :Mp mp :rate r})
                 (zipmap (:Qt-states pn) (:loop-rates pn))))))

(defn Qt-calc
  "Calculate the vector of rates from the root directly to tangible states."
  [pn]
  (let [root (:root-mark pn)]
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
  (let [root (:root-mark pn)]
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

(defn follow-transitions
  "Return a vector [<mark> <mark>...] that are the list of states followed by
   taking the argument first state and applying each trns."
  [pn mark trns]
  (reduce (fn [path trn]
            (conj path (next-mark pn (last path) trn)))
          [mark]
          trns))

;;; POD good place for a transient?
(defn summarize-reach
  "Merge :vpath-rates and :explored (sans vanishing) resulting in :M2Mp"
  [pn]
  (as-> pn ?pn
    (assoc ?pn :explored (distinct (:explored ?pn)))  ; pod neither this...
    (assoc ?pn :vpath-rates (distinct (:vpath-rates ?pn))) ; nor this is justified
    (assoc ?pn :explored (remove #(immediate? ?pn (:fire %)) (:explored ?pn)))
    (assoc ?pn :explored (filter #(and (tangible? ?pn (:Mp %))
                                       (tangible? ?pn (:M %)))
                                 (:explored ?pn)))
    (reduce (fn [pn [mark trn]]
              (assoc pn :explored
                     (remove #(find-link pn mark trn %) (:explored pn))))
            ?pn
            (map (fn [vpath]
                   (map #(vector %1 %2)
                        (butlast (follow-transitions ?pn (:M vpath) (:fire vpath)))
                        (:fire vpath)))
                 (:vpath-rates ?pn)))
  (assoc ?pn :M2Mp (into (:explored ?pn) (:vpath-rates ?pn)))
   #_(dissoc ?pn :vpath-rates :explored :explored-v :St :Sv :Sv-explored :paths :root :root-mark)))


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
    (> (count (:explored pn)) 500) ; POD 500
    (assoc pn :failure {:reason :exceeds-reach :set-size (count (:explored pn))}),
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

    
