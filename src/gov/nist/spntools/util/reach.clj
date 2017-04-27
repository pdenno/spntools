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
;;;    BUGS: 1) Handle 'by-pass' t-->t...-->t from loop root state. 
;;;          2) clip-head-to-root probably isn't sufficient; check for roots more
;;;             encompassing of vanishing transitions. 

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
   (if mark
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
              trs))))
     nil)))

(def +k-bounded+ (atom 10)) ; Maybe better than (or addition to) k-bounded would be size of :explored
(def +max-rs+  "reachability set size" (atom 5000)) 
(declare renumber-pids check-reach tangible? vanishing? in-loop-checks initial-tangible-state reachability-loop
         summarize-reach reach-reduce-vpaths reach-step-tangible conj-t-rate into-v-rates)

(def ^:dynamic *loop-count* (atom 0))

(defn reachability
  "Compute the reachability graph (:M2Mp) depth-first starting at the initial marking, 
   removing vanishing states on-the-fly using the algorithm of Knottenbelt, 1996.
   The links that end up in :t-states and :v-state should have tangible :M and :Mp."
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
    (loop [res {:spaths (vec (map vector (next-links pn root)))
                :v-rates [], :t-rates [], :explored []}] 
      (reset! +diag+ res)
      (let [active (-> res :spaths first last)]
        ;;(println "------- Return to toplevel ----")    ; keep 
        ;;(println ":spaths = ") (ppprint (:spaths res))
        ;;(println ":t-rates = ") (ppprint (:t-rates res))
        ;;(println ":active = " active)
        ;;(println ":explored = ") (ppprint (:explored res))
        (as-> res ?r
          (in-loop-checks ?r)
          (if (empty? (:spaths ?r))
            ?r
            (recur
             (cond (and (tangible? pn (:M active))
                        (tangible? pn (:Mp active)))
                   (reach-step-tangible ?r pn),
                   (some #(= active %) (:explored ?r))
                   (assoc ?r :spaths (-> ?r :spaths next))
                   :else
                   (reach-reduce-vpaths ?r pn)))))))))

(defn reach-step-tangible
  "This one doesn't have it's own map; it works off the search-level map."
  [res pn]
  (as-> res ?r
    (conj-t-rate ?r (-> ?r :spaths first last) pn)
    (update ?r :t-rates distinct) ; POD need investigation. 
    (update ?r :explored conj (-> ?r :spaths first last))
    (assoc ?r :nexts (next-links pn (-> ?r :spaths first last :Mp) (:explored ?r)))
    ;; If there is a point to saving the whole path, rather than just starting a new one for each next,
    ;; it is that you might want to travel up it to find the root for cycles of vanishing states. 
    (if (empty? (:nexts ?r)) ; This part is navigation, whereas :search-paths (reach-reduce-vpaths)...
      (assoc ?r :spaths (vec (next (:spaths ?r)))) ; ... is a process for terminating paths and loops.
      (assoc ?r :spaths (into (vec (map #(conj (-> ?r :spaths first) %) (:nexts ?r))) (-> ?r :spaths next))))))

(defn into-v-rates
  [obj links pn]
  (if-let [bad (some #(when (or (vanishing? pn (:M %)) (vanishing? pn (:Mp %))) %) links)]
    (throw (ex-info "Adding a vanishing link to :v-rates." {:link bad :links links :obj obj}))
    (update obj :v-rates into links)))

(defn conj-t-rate
  [obj link pn]
  (when (or (vanishing? pn (:M link)) (vanishing? pn (:Mp link)))
    (println "Adding the wrong thing to :t-rates: " link))
  (update obj :t-rates conj link))

(declare follow-vpath clip-head-to-root update-paths-for-nav update-paths-for-loop
         calc-vpath-rate loop-reduce-vpath terminating-tangibles)
;;;========================================================================
;;; Toplevel function for vpaths.
;;; POD What I'm doing with clip-head-to-root might not be sufficient. There might
;;;     be a loop above all this stuff. It might be better to call terminating-tangibles
;;;     on every tangible backwards on path towards the :initial-tangible. Take as root
;;;     the last one where :explored expanded. Need a test case for this.
(defn reach-reduce-vpaths
  "Toplevel reduction of :vpaths, returning updates to the results map :paths :v-rates etc.
   Just calls out for the real work (follow-vpaths) and copies data. Does not touch the pn."
  [res pn]
  (as-> res ?r
    (assoc ?r :cycle? false)
    (assoc ?r :collected-terms [])
    (reduce (fn [res clipped-vpath]
              ;;(println "clipped-vpath = ") (ppprint clipped-vpath) ; keep
              (if (:cycle? res) ; Stop the reduce if reduced a loop
                res ; fp starts a new map, containing :vexplored, etc. 
                (let [fp (follow-vpath pn clipped-vpath (:spaths res) (:explored res))] 
                  (as-> res ?r1
                    (update ?r1 :collected-terms into (:new-St fp))
                    (into-v-rates ?r1 (:new-vpath-rates fp) pn)
                    ;;(do (println "v-rates = ") (ppprint (:v-rates ?r1))  ; keep
                    ;;    (println "new-St = " ) (ppprint (:new-St fp)) ?r1)
                    (update ?r1 :explored into clipped-vpath) 
                    (update ?r1 :explored into (:vexplored fp))
                    (update ?r1 :explored distinct)
                    (assoc  ?r1 :spaths (if (= (:search-paths fp) :drop-first)
                                          (-> ?r1 :spaths next vec) ; <--- return from path
                                          (:search-paths fp))) ; <--- return from loop
                    (assoc  ?r1 :cycle? (:cycle? fp))))))
            ?r
            (map #(clip-head-to-root % pn)
                 (filter #(or (vanishing? pn (-> % last :M))
                              (vanishing? pn (-> % last :Mp)))
                         (:spaths ?r))))
    ;; UPdate search paths with whatever terminals were found (from loop or vpath).
    (assoc ?r :spaths (into (vec (map vector (:collected-terms ?r))) (:spaths ?r)))
    ;;(do (println ":collected-terms = ") (ppprint (:collected-terms ?r)) ; keep
    ;;    (println ":spaths now = ") (ppprint (:spaths ?r))
    ;;    ?r)
    (dissoc ?r :collected-terms)))

(def loop-count (atom 0))
(declare follow-vpath-loop follow-vpath-to-tang cycle?)

(defn follow-vpath
 "Continue navigation of vpath (links) to all ending tangible states. 
  vpath is a path of links, all elements of which are tangible. 
  Calls out for loops and calculation when a terminal is reached. 
  Return a map with :new-vpath-rates and :new-St. DOES NOT CHANGE pn.
  Argument search-paths is the 'global' search path used by the reachability-loop."
  [pn vpath search-paths explored]
  (loop [fp {:new-vpath-rates [] :vexplored explored :cycle? false, :init? true, 
             :paths (vector vpath) :loop false :new-St [], :tang? false
             :vpath vpath :search-paths search-paths}] ; These two for debugging. 
    (swap! loop-count inc)
    ;;(reset! +diag+ fp) ; keep
    ;;(when (or (> @loop-count 50) (> (count (:paths fp)) 10) (> (count (-> fp :paths first)) 10)) (break "path length")) ; keep
    ;; By not looking at :vexplored for next-links here, we'll pick up duplicate v-rates.
    ;; OTOH not doing so will result in missing rates.
    (let [nexts (and (not-empty (:paths fp))
                     (next-links pn (-> fp :paths first last :Mp)))
          tang? (and (not-empty nexts) (tangible? pn (-> nexts first :M)))]
      (as-> fp ?fp
        (assoc ?fp :paths
               (cond (empty? nexts) (next (:paths ?fp)),
                     ;; We don't call follow-vpath-to-tang with a tangible on the path
                     (and (not (= 1 (count (-> ?fp :paths first)))) tang?) (:paths ?fp), 
                     :else (into (vec (map #(conj (-> ?fp :paths first) %) nexts))
                                 (rest (:paths ?fp)))))
        (assoc ?fp :cycle? (cycle? pn ?fp))
        (assoc ?fp :tang? (if (:init? ?fp) false tang?))
        ;; Don't put terminating tangibles on explored. Need to search from those. 
        (update ?fp :vexplored into (if (:tang? ?fp) [] nexts)) 
        (assoc ?fp :init? false)
        (if (empty? (:paths ?fp))
          ?fp
          (recur
           (cond (:cycle? ?fp) (follow-vpath-loop ?fp pn)
                 (:tang? ?fp)  (follow-vpath-to-tang ?fp pn) 
                 :else ?fp)))))))

(defn follow-vpath-to-tang
  "Hit a tangible. End this path."
  [fp pn]
  (when (vanishing? pn (-> fp :paths first last :Mp))
    (throw (ex-info "follow-vpath-to-tang, but it's not!" {:path (-> fp :paths first)})))
  ;;(println "Candidate :new-ST = ") (ppprint (next-links pn (-> fp :paths first last :Mp))) ; keep
  ;;(println "Actual :new-ST = ") (ppprint (next-links pn (-> fp :paths first last :Mp) (:vexplored fp)))
  ;;(println ":vexplored (in fvptt) = ") (ppprint (:vexplored fp))
  (as-> fp ?fp 
    (update ?fp :new-St into (next-links pn (-> ?fp :paths first last :Mp) (:vexplored ?fp)))
    (update ?fp :new-vpath-rates conj (calc-vpath-rate pn (-> ?fp :paths first)))
    (assoc ?fp :paths (-> ?fp :paths next vec)) 
    (assoc ?fp :search-paths :drop-first)))

(defn follow-vpath-loop
  "Encountered a loop. Big update based on loop-reduce-vpath."
  [fp pn]
  (let [lp (loop-reduce-vpath pn (:vpath fp))]
    (as-> fp ?fp1 ; Loop. Terminate all.
      (assoc ?fp1 :search-paths (update-paths-for-loop pn lp (:search-paths ?fp1)))
      (assoc ?fp1 :paths [])
      (update ?fp1 :vexplored into (:vexplored lp))
      (update ?fp1 :new-vpath-rates into (:lv-rates lp))
      (update ?fp1 :new-St into (:lv-St lp))
      (assoc ?fp1 :cycle? true))))

(defn update-paths-for-loop
  "Use the root, explored, and terminals of the sub-network loop to update
   what still requires to be searched. lp is loop reduce map."
  [pn lp search-paths]
  (let [explored (-> lp :vexplored)]
    (vec (remove
          (fn [spath] (some (fn [step] (some #(= step %) explored)) spath))
          search-paths))))

;;; POD It might not be sufficient to simply drop paths that contain all tangible states.
;;; I chose to look at paths rather than having visited the state because I thought it would
;;; be more robust (fewer false positives). The jury is still out.
(defn cycle? [pn fp]
  "Return true if a cycle of vanishing states is detected starting with the active state. 
   Searches backward through explored states looking for the active state.
   Drops paths that contain tangible states."
  (let [space (:vexplored fp)
        finding (-> fp :paths first last :M)]
    (loop [found false
           paths (vector (vector (-> fp :paths first last)))]
      (cond found (first paths)
            (empty? paths) (when found (first paths))
            :else
            (let [active (-> paths first last :M)
                  match? (and (= finding active) (not= 1 (count (first paths))))
                  vanishing? (every? #(vanishing? pn (:M %)) (first paths))
                  nexts (distinct (filter #(= active (:Mp %)) space))]
              (recur
               (and match? vanishing?)
               (cond (empty? nexts) (-> paths next vec) ; move to next search path
                     (and match? vanishing?) paths ; found, don't care what is returned.
                     (not vanishing?) (-> paths next vec) ; Contains tangible states. Drop it.
                     :else (into (vec (map #(conj (first paths) %) nexts)) (next paths)))))))))

(defn calc-vpath-rate
  "Create a vpath link object, calculating the rate from the root to the tangible state 
   that is the last state in the path argument. The path ends (:Mp) in a tangible state."
  [pn path]
  (let [fired (map :fire path)]
    {:M (-> path first :M)
     :fire (vec fired)
     :Mp  (-> path last :Mp)
     :rate (apply * (map (fn [l f]
                           (:rate (some #(when (= (:fire %) f) %)
                                        (next-links pn (:M l)))))
                         path fired))
     :cycle? false}))

(defn clip-head-to-root
  "Return a path (links with all the front tangibles except last removed.
   All the states on the end of the path are vanishing."
  [path pn]
  (let [stop? (atom false)]
    (vec (reverse (reduce (fn [path link]
                            (cond @stop? path,
                                  (tangible? pn (:M link))
                                  (do (reset! stop? true)
                                      (conj path link)),
                                  :else (conj path link)))
                          []
                          (reverse path))))))

(declare vanish-matrices Q-prime)
;;;================================================================================
;;; This is toplevel for reduction of loops; called from vanish-paths.
(defn loop-reduce-vpath
  "Top-level calculation of vpaths for loops. Creates a structure for use by vanish-paths"
  [pn vpath]
  (let [tt (terminating-tangibles pn vpath)]
    (as-> (vanish-matrices pn vpath tt) ?lp
      (assoc ?lp :lv-rates ; :loop! is used later on to identify loops.
             (map (fn [mp r] {:M (-> vpath first :M) :fire :loop! :Mp mp :rate r})
                  (:Qt-states ?lp)
                  (:loop-rates ?lp)))
      (assoc ?lp :lv-St (:terms tt))
      (assoc ?lp :vexplored (:texplored tt)))))

(defn vanish-matrices
  "Compute rates between a root a every tangible terminated in paths with cycles."
  [pn root-path tt]
    (as-> {} ?calc
      (assoc ?calc :Qt-states (map :M (:terms tt)))
      (assoc ?calc :Qt (map (fn [target]
                              (reduce (fn [r link] (+ r (:rate link)))
                                      0.0
                                      (filter #(and (= (first root-path) (:M %)) (= target (:Mp %))) (:texplored tt))))
                            (:Qt-states ?calc)))
      (assoc ?calc :Qtv-states (distinct (filter #(vanishing? pn %) (map :M (:texplored tt)))))
      (assoc ?calc :Qtv (map (fn [target] (reduce (fn [r link] (+ r (:rate link)))
                                                  0.0 
                                                  (filter #(and (= (:M (first root-path)) (:M %)) (= target (:Mp %))) (:texplored tt))))
                                  (:Qtv-states ?calc)))
      (assoc ?calc :Pv (map (fn [r]
                              (map (fn [c] (reduce (fn [sum link] (+ sum (:rate link)))
                                                   0.0
                                                   (filter #(and (= (:M %) r) (= (:Mp %) c))
                                                           (:texplored tt))))
                                   (:Qtv-states ?calc)))
                            (:Qtv-states ?calc)))
      (assoc ?calc :Pvt (map (fn [r]
                               (map (fn [c] (reduce (fn [sum link] (+ sum (:rate link)))
                                                    0.0
                                                    (filter #(and (= (:M %) r) (= (:Mp %) c))
                                                            (:texplored tt))))
                                    (:Qt-states ?calc)))
                             (:Qtv-states ?calc)))
      (assoc ?calc :loop-rates (Q-prime (:Qt ?calc) (:Qtv ?calc) (:Pv ?calc) (:Pvt ?calc)))))

(defn terminating-tangibles
  "Called from loop-reduce-vpath, thus the vpath has a cycle. 
   Return a list of tangible states that can be reached beyond the last state in the 
   argument path and excluding visited states (on the argument path).  Once a tangible 
   state has been reached, that path is terminated (and the terminal state added to :terms. 
   Takes at least one step."
  [pn vpath]
  (loop [res {:terms [], :texplored vpath, :init? true, :tang? true,
              :nexts (next-links pn (-> vpath first :M)),
              :paths (vector vpath)}]
    (as-> res ?r
      (assoc ?r :nexts (if (:init? ?r)
                         (:nexts ?r)
                         (next-links pn (-> ?r :paths first last :Mp) (:texplored ?r))))
      (assoc ?r :tang? (and (not-empty (:nexts ?r)) (tangible? pn (-> ?r :nexts first :M))))
      (if (empty? (:paths ?r))
        ?r
        (recur
         (as-> ?r ?r1
           (if (and (:tang? ?r1) (not (some (fn [n] (some #(= n %) vpath)) (:nexts ?r1))))
             (update ?r1 :terms into (:nexts ?r1))
             ?r1)
           (update ?r1 :texplored into (:nexts ?r1)) ; POD this was in (if (:tang? ?r1)....
           (update ?r1 :texplored distinct) ; POD needs review. Starting one twice on qorchard
           (if (and (not (:init? ?r)) (or (:tang? ?r1) (empty? (:nexts ?r1))))
             (update ?r1 :paths next)
             (assoc ?r1 :paths (into (vec (map #(conj (first (:paths ?r1)) %) (:nexts ?r1)))
                                     (next (:paths ?r1)))))
           (assoc ?r1 :init? false)))))))

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
  (as-> pn ?pn
   (assoc ?pn :M2Mp (into (:t-rates ?pn) (distinct (:v-rates ?pn)))) 
   (dissoc ?pn :explored :vexplored :spaths :t-rates :v-rates))) ; keep

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
  (let [state (-> res :spaths first last :M)] 
    (cond
      (> @*loop-count* 400) ; POD
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
                           :data {:m-not-mp m-mp :mp-not-m mp-m}
                           :explanation [":m-not-mp means got into this state, but we don't see how."
                                         ":mp-not-m means don't know how to get out of this state."
                                         "If these these states are vanishing, it's a bug." ]}))
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
    
#_(defn marks2links
  "Return the path vector of links corresponding to the argument path vector of marks.
   Returns a sequence of length (dec (count marks)) First mark is in :M , last in :Mp"
  [pn marks]
  (let [result (reduce (fn [trns i]
                         (conj trns
                               (some #(when (= (nth marks (inc i)) (:Mp %)) %)
                                     (next-links pn (nth marks i)))))
                       []
                       (range (dec (count marks))))]
    (if (every? identity result)
      result
      (throw (ex-info "Bad link-path" {:marks marks})))))


