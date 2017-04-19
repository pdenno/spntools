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
;;;    BUGS: 1) Handle 'by-pass' t-->t...-->t from root.
;;;          2) Probably what I'm doing to specify root before calling to reduce vpaths is insufficient.

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

(defn next-marks
  "Return a list of states enabled by the argument state."
  ([pn mark] (next-marks pn mark false))
  ([pn mark clist]
   (let [trns
         (as-> (map :name (:transitions pn)) ?trns
           (filter #(fireable? pn mark %) ?trns)
           (if (some #(immediate? pn %) ?trns)
             (filter #(immediate? pn %) ?trns)
             ?trns))
         marks (map #(next-mark pn mark %) trns)]
     (remove (fn [m] (some #(= % m)
                           (cond (keyword? clist) (clist pn)
                                 clist clist
                                 :else [])))
             marks))))

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
(declare renumber-pids check-reach tangible? vanishing? in-loop-checks initial-tangible-state reachability-loop
          summarize-reach reach-reduce-vpaths)


(def ^:dynamic *loop-count* (atom 0))

(defn reachability
  "Compute the reachability graph (:M2Mp) depth-first starting at the initial marking, 
   removing vanishing states on-the-fly using the algorithm of Knottenbelt, 1996."
  [pn]
  (as-pn-ok-> pn ?pn
    (renumber-pids ?pn)
    (initial-tangible-state ?pn)
    (binding [*loop-count* (atom 0)]
      (let [res (reachability-loop ?pn)]
        (-> ?pn
            (assoc :t-rates (:t-rates res))
            (assoc :v-rates (:v-rates res)))))
    (summarize-reach ?pn)
    (check-reach ?pn)))

(defn reachability-loop [pn]
  "Calculate reachability graph. pn is not touched."
  (let [root (:initial-tangible pn)]
    (loop [res {:t-rates [],
                :nexts (next-links pn root),
                :St [root], :root root, :tang? true, :loop? false
                :Sv [], :Sv-explored [], :v-rates []}]
      (as-pn-ok->  res ?r ;(in-loop-checks res) ?r
        ;;(do (println "res =" ?r "\n") ?r)
        (if (and (empty? (:St ?r)) (empty? (:Sv ?r)))
          ?r
          (recur     
           (if (empty? (:Sv ?r))
             (as-> ?r ?r1
               (update ?r1 :t-rates into (if (and (:nexts ?r1) (tangible? pn (-> ?r1 :nexts first :M)))
                                           (:nexts ?r1)
                                           []))
               ;; The remaining below sets up for next iteration.
               ;; ?tang looks ahead one step, setting up Sv and root for a vpath. 
               (if-let [ahead (-> ?r1 :nexts first :Mp)]
                 (assoc ?r1 :tang? (tangible? pn ahead))
                 (assoc ?r1 :tang? false)) ; distinct for self-loops
               (assoc ?r1 :St (distinct (into (if (:tang? ?r1) (vec (map :Mp (:nexts ?r1))) []) (next (:St ?r1)))))
               (assoc ?r1 :Sv (if (:tang? ?r1) [] (map :Mp (:nexts ?r1))))
               (assoc ?r1 :root (if (:tang? ?r1) (-> ?r1 :nexts first :M) (:root ?r1)))
               (assoc ?r1 :nexts (if (-> ?r1 :St first) (next-links pn (-> ?r1 :St first) (:t-rates ?r1)) [])))
             (as-> ?r ?r1
               (assoc ?r1 :Sv (remove #(some (fn [[sve rt]] (and (= sve %) (= rt (:root ?r1))))
                                             (:Sv-explored ?r1))
                                      (:Sv ?r1)))
               (assoc ?r1 :Sv-explored (into (:Sv-explored ?r1) (map #(vector % (:root ?r1)) (:Sv ?r1))))
               (reach-reduce-vpaths ?r1 pn (:Sv ?r1))
               (assoc ?r1 :nexts (next-links pn (-> ?r1 :St first) (:t-rates ?r1)))))))))))

(declare follow-vpaths update-vpath-for-search terminate-vpath loop-reduce-vpath terminating-tangibles
         calc-vpath-rate fire-vpath)
;;;========================================================================
;;; Toplevel function for vpaths. 
(defn reach-reduce-vpaths
  "Toplevel reduction of :vpaths, returning updates to the results map :Sv, :St. 
   Just calls out for the real work (follow-vpaths) and copies data. Does not touch the pn."
  [res pn vpaths]
  (as-> res ?r
    (assoc ?r :loop? false)
    (reduce (fn [res v-mark]
              (if (:loop? res) ; Stop the reduce if reduced a loop
                res
                (let [vp (follow-vpaths pn (:root ?r) v-mark)]
                  (as-> res ?r1
                    (update ?r1 :v-rates into (:new-vpath-rates vp))
                    (assoc ?r1 :loop? (:loop vp))
                    (assoc ?r1 :tang? true)
                    (if (:loop? ?r1) (assoc ?r1 :Sv []) (update ?r1 :Sv next))
                    (if (:loop? ?r1)
                      (assoc ?r1 :St (:new-St vp))
                      (assoc ?r1 :St (into (:new-St vp) (:St ?r1))))))))
            ?r      
            vpaths))) 

(defn follow-vpaths
 "Navigate from root to all ending tangible states. 
  v-mark is a vanishing state enabled by a transition from root. 
  Calls out for loops and calculation when a terminal is reached. 
  Return a map with :new-vpath-rates and :new-St. DOES NOT CHANGE pn."
  [pn root v-mark]
  (loop [res {:new-vpath-rates [] :root root
              :explored (vector root v-mark)
              :paths (vector (vector root v-mark))
              :loop false :new-St (:St pn)
              :nexts [] :tang? :init}]
      (as-> res ?r
        (update-vpath-for-search ?r pn)
        (if (empty? (:paths ?r)) 
          ?r
          (recur (cond (some (fn [n] (some #(= n %) (:explored ?r))) (:nexts ?r))
                       (as-> ?r ?r2 ; Loop. Terminate all.
                         (assoc ?r2 :paths [])
                         (assoc ?r2 :loop (loop-reduce-vpath pn root))
                         (update ?r2 :new-vpath-rates into (-> ?r2 :loop :lv-rates))
                         (update ?r2 :new-St into (-> ?r2 :loop :lv-St))),
                       (:tang? ?r) ; Not loop, but hit a tangible. End this path.
                       (as-> ?r ?r2
                         (update ?r2 :new-St conj (-> ?r2 :paths first last))
                         (update ?r2 :new-vpath-rates conj (terminate-vpath pn (-> ?r2 :paths first)))
                         (update ?r2 :paths next)),
                       :else ?r))))))

(defn update-vpath-for-search [res pn]
  "Update path, dealing with odd cases such as where the current path might 
   already have a terminal on it. Shorten it if necessary."
  (reset! +diag+ res)
  (cond (empty? (:paths res)) res,
        (= (:tang? res) :init) (assoc res :tang? false),
        (tangible? pn (-> res :paths first last)) (assoc res :tang? true)
        :else
        (as-> res ?r
          (assoc ?r :nexts (next-marks pn (-> ?r :paths first last)))
          (assoc ?r :paths
                 (if (empty? (:nexts ?r))
                   (next (:paths ?r))
                   (into (vec (map #(conj (-> ?r :paths first) %) (:nexts ?r)))
                         (rest (:paths ?r)))))
          (assoc ?r :tang? (tangible? pn (-> res :paths first last))))))


;;; The maps look like this:
;;;   Typical:  {:M <root> :fire [<root-to-v> <v> ...<v> <v-to-tang>] :Mp <tangible>}"
;;;   Loop   :  {:M <root> :fire [<root-to-v> <v> ...<v>] :Mp <not relevant> :loop? true}"
(defn terminate-vpath
  "Create a vpath link object, calculating the rate from the root to the tangible state 
   that is the last state in the path argument. "
  [pn path]
  (let [fired (fire-vpath pn path)]
    {:M (first path)
     :fire fired
     :Mp  (last path)
     :rate (apply * (map (fn [m f]
                           (:rate (some #(when (= (:fire %) f) %)
                                        (next-links pn m))))
                         path fired))
     :loop? false}))

(defn fire-vpath
  "Calculate the sequence of transitions that fire corresponding to the argument sequence of marks.
   Returns a sequence of length (dec (count marks))"
  [pn marks]
  (let [result (reduce (fn [trns i]
                         (conj trns
                               (some #(when (= (nth marks (inc i)) (:Mp %)) (:fire %))
                                     (next-links pn (nth marks i)))))
                       []
                       (range (dec (count marks))))]
    (if (every? identity result)
      result
      (throw (ex-info "Bad fire-path" {:marks marks})))))

(declare vanish-matrices Q-prime)
;;;================================================================================
;;; This is toplevel for reduction of loops; called from vanish-paths.
(defn loop-reduce-vpath
  "Top-level calculation of vpaths for loops. Creates a structure for use by vanish-paths"
  [pn root]
  (let [tt (terminating-tangibles pn root)]
    (as-> (vanish-matrices pn root tt) ?calc
      (assoc ?calc :lv-rates ; :loop! is used later on to identify loops.
             (map (fn [mp r] {:M root :fire :loop! :Mp mp :rate r})
                  (:Qt-states ?calc) (:loop-rates ?calc)))
      (assoc ?calc :lv-St (:terms tt)))))

;;; POD fix this to include paths t-->...t-->t (qorchard.xml is all 0.0)
(defn vanish-matrices
  "Compute rates between a root a every tangible terminated in paths with cycles."
  [pn root tt]
    (as-> {} ?calc
      (assoc ?calc :Qt-states (:terms tt))
      (assoc ?calc :Qt (map (fn [target]
                              (reduce (fn [r link] (+ r (:rate link)))
                                      0.0
                                      (filter #(and (= root (:M %)) (= target (:Mp %))) (:explored tt))))
                            (:Qt-states ?calc)))
      (assoc ?calc :Qtv-states (distinct (filter #(vanishing? pn %) (map :M (:explored tt)))))
      (assoc ?calc :Qtv (map (fn [target] (reduce (fn [r link] (+ r (:rate link)))
                                                  0.0 
                                                  (filter #(and (= root (:M %)) (= target (:Mp %))) (:explored tt))))
                                  (:Qtv-states ?calc)))
      (assoc ?calc :Pv (map (fn [r]
                              (map (fn [c] (reduce (fn [sum link] (+ sum (:rate link)))
                                                   0.0
                                                   (filter #(and (= (:M %) r) (= (:Mp %) c))
                                                           (:explored tt))))
                                   (:Qtv-states ?calc)))
                            (:Qtv-states ?calc)))
      (assoc ?calc :Pvt (map (fn [r]
                               (map (fn [c] (reduce (fn [sum link] (+ sum (:rate link)))
                                                    0.0
                                                    (filter #(and (= (:M %) r) (= (:Mp %) c))
                                                            (:explored tt))))
                                    (:Qt-states ?calc)))
                             (:Qtv-states ?calc)))
      (assoc ?calc :loop-rates (Q-prime (:Qt ?calc) (:Qtv ?calc) (:Pv ?calc) (:Pvt ?calc)))))

(defn terminating-tangibles
  "Return a list of tangible states that can be reached from the root mark.
   Once a tangible state has been reached, that path is terminated. Takes at least one step."
  [pn root-mark]
  (loop [terms []
         explored (into [{:M root-mark}] (next-links pn root-mark))
         paths (vec (map #(conj [{:M root-mark}] %) (next-links pn root-mark)))]
    (let [nexts (when (not-empty paths) (next-links pn (-> paths first last :Mp) explored))
          tang? (and (not-empty nexts) (tangible? pn (-> nexts first :M)))]
      (if (empty? paths)
        {:root root-mark
         :terms (map :M terms)
         :explored explored}
        (recur
         (if tang? (into terms nexts) terms)
         (if tang? explored (into explored nexts))
         (if (or tang? (empty? nexts))
           (next paths)
           (into (vec (map #(conj (first paths) %) nexts)) (next paths))))))))

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
                           (vec (next (into stack (next-links ?pn3 (:Mp (first stack)) :explored-i))))))))
          (dissoc ?pn2 :explored-i))))))

(declare links-on add-links-off vanishing2subnets Qt-calc Qtv-calc Pv-calc Pvt-calc)
(declare Q-prime merge-loops loop-clean-vpaths loop-add-rates)

(defn follow-transitions
  "Return a vector [<mark> <mark>...] that are the list of states followed by
   taking the argument first state and applying each trns."
  [pn mark trns]
  (reduce (fn [path trn]
            (conj path (next-mark pn (last path) trn)))
          [mark]
          trns))

(defn summarize-reach
  "Merge :vpath-rates and :explored (sans vanishing) resulting in :M2Mp"
  [pn]
  (let [loop-marks (distinct
                    (map :M
                         (filter #(or (= :loop! (:fire %)) (vector? (:fire %)))
                                 (:v-rates pn))))]
    (as-> pn ?pn ; vanish-paths can leave paths covered by loops in :t-rates.
      (assoc ?pn :t-rates (remove (fn [r] (some #(= (:M r) %) loop-marks)) (:t-rates ?pn)))
      (assoc ?pn :M2Mp (into (:t-rates ?pn) (:v-rates ?pn)))
   #_(dissoc ?pn :explored :St :Sv :Sv-explored :paths :root :root-mark))))

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

(defn in-loop-checks [res]
  (swap! *loop-count* inc)
  (reset! +diag+ res)
  (let [state (:St res)]
    (cond
      (> @*loop-count* 200) ; POD
      (assoc res :failure {:reason :loop-count-exceeded}),
      (and state (some #(> % @+k-bounded+) state))
      (assoc res :failure {:reason :not-k-bounded :marking state}),
      (> (count (:explored res)) @+max-rs+)
      (assoc res :failure {:reason :exceeds-max-rs :set-size (count (:explored res))}),
      :else res)))

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

    
