(ns gov.nist.spntools.utils
  (:require [clojure.spec.alpha :as s]
            #?(:cljs [cljs.reader :refer (read-string)])
            [clojure.set :as set]
            [clojure.pprint :refer (cl-format pprint pp)]))

#?(:clj
   (defmacro pn-ok->
  "Macro to thread a Petri net through forms binding VAR until the end is reach or it picks up a :failure key."
     [pn & forms]
     (let [g (gensym)
           steps (map (fn [step] `(if (contains? ~g :failure) ~g (-> ~g ~step)))
                      forms)]
       `(let [~g ~pn
              ~@(interleave (repeat g) (butlast steps))]
          ~(if (empty? steps)
             g
             (last steps))))))
#?(:clj
   (defmacro as-pn-ok->
     [pn name & forms]
     (let [steps (map (fn [step] `(if (contains? ~name :failure) ~name ~step))
                      forms)]
       `(let [~name ~pn
              ~@(interleave (repeat name) steps)]
          ~name))))

;;;=== General =========================
(defn ppp []
  (binding [clojure.pprint/*print-right-margin* 140]
    (pprint *1)))

(defn ppprint [arg]
  (binding [clojure.pprint/*print-right-margin* 140]
    (pprint arg)))

(defn break
  ([] (throw (ex-info "Break!" {})))
  ([text] (throw (ex-info text {})))
  ([text args] (throw (ex-info text args))))

#_(defn testme []
  (binding [*ns* (find-ns 'gov.nist.spntools-test)]
    (clojure.test/run-tests)))

;;;=== Petri Nets =========================
(def +obj-cnt+ (atom 0))

;;; POD clojure.spec question. How do I handle the same keyword :type used for mulitple purposes?
;;; :type in arcs is (:normal / :inhibitor). :type in transitions is (:exponential / :immediate).


(s/def ::type (fn [t] (some #(= t %) [:normal :inhibitor :exponential :immediate])))
(s/def ::target keyword?)
(s/def ::source keyword?)
(s/def ::multiplicity (s/and integer? pos?))
(s/def ::aid (s/and integer? #(not (neg? %))))
(s/def ::tid (s/and integer? #(not (neg? %))))
(s/def ::pid (s/and integer? #(not (neg? %))))
(s/def ::name keyword?)
(s/def ::arc (s/keys :req-un [::aid ::source ::target ::name ::multiplicity]))
(s/def ::transition (s/keys :req-un [::name ::tid ::type ::rate]))
(s/def ::place (s/keys :req-un [::name ::pid ::initial-tokens]))
(s/def ::transitions (s/coll-of ::transition :kind vector? :min-count 1))
(s/def ::arcs (s/coll-of ::arc :kind vector? :min-count 1))
(s/def ::places (s/coll-of ::place :kind vector? :min-count 1))
(s/def ::pn (s/keys :req-un [::places ::arcs ::transitions]))

(s/def ::mark-val (s/int-in 0 ##Inf))
(s/def ::marking (s/coll-of ::mark-val :kind vector?))

(defn pn?
  "If the argument is a Petri net, return it; otherwise return false
   Used where s/spec would be too demanding (eg. when building PNs)."
  [obj]
  (and (:places obj) (:transitions obj) (:arcs obj) obj))

(defn tid2obj
  [pn tid]
  (assert (keyword? tid))
  (some #(when (= (:tid %) tid) %) (:transitions pn)))

(defn pid2obj
  [pn pid]
  (assert (keyword? pid))
  (some #(when (= (:pid %) pid) %) (:places pn)))

(defn aid2obj
  [pn aid]
  (assert (keyword? aid))
  (some #(when (= (:aid %) aid) %) (:arcs pn)))

(defn arcs-into
  "Return the arcs into the named object."
  [pn name]
  (assert (keyword? name))
  (s/assert ::pn pn)
  (filter #(= (:target %) name) (:arcs pn)))

(defn arcs-outof
  "Return the arcs exiting the named object."
  [pn name]
  (assert (keyword? name))
  (s/assert ::pn pn)
  (filter #(= (:source %) name) (:arcs pn)))

(defn name2obj
  [pn name]
  (assert (keyword? name))
  (s/assert ::pn pn)
  (or 
   (some #(when (= name (:name %)) %) (:places pn))
   (some #(when (= name (:name %)) %) (:transitions pn))
   (some #(when (= name (:name %)) %) (:arcs pn))))

(def ^:dynamic *path-to* nil)
(def ^:dynamic *visited* nil)
(defn follow-path
  "Return a sequence of places, transitions, arcs forward of OBJ."
  [pn obj]
  (s/assert ::pn pn)
  (cond (:tid obj) (arcs-outof pn (:name obj)),
        (:pid obj) (arcs-outof pn (:name obj)),
        (:aid obj) (if (contains? @*visited* (:target obj))
                     nil
                     (do (swap! *visited* conj (:target obj))
                         (list (name2obj pn (:target obj)))))))

(defn follow-path-back
  "Return a sequence of places, transitions, arcs forward of OBJ."
  [pn obj]
  (s/assert ::pn pn)
  (cond (:tid obj) (arcs-into pn (:name obj)),
        (:pid obj) (arcs-into pn (:name obj)),
        (:aid obj) (if (contains? @*visited* (:source obj))
                     nil
                     (do (swap! *visited* conj (:source obj))
                         (list (name2obj pn (:source obj)))))))

(defn paths-to-aux
  [pn here to nsteps & {:keys [so-far back?] :or {so-far []}}]
  (cond (= nsteps 0)
        (when (= (:name (last so-far)) to)
          (swap! *path-to* conj so-far))
        (> nsteps 0)
        (doseq [p (if back?
                    (follow-path-back pn here)
                    (follow-path pn here))]
          (paths-to-aux pn p to (dec nsteps)
                        :so-far (conj so-far p)
                        :back? back?))))

(defn paths-to
  "Return the paths from FROM to TO (both are names of places or transitions) 
   in exactly STEPS steps (counting places, transitions and arcs)."
  [pn from to nsteps & {:keys [back?]}]
  (s/assert ::pn pn)
  (binding [*path-to* (atom [])
            *visited* (atom #{from})]
    (paths-to-aux pn (name2obj pn from) to nsteps :back? back?)
    @*path-to*))

(defn arc? [obj] (:aid obj))
(defn place? [obj] (:pid obj))
(defn transition? [obj] (:tid obj))
(defn pn-obj? [obj] (or (:aid obj) (:tid obj) (:pid obj)))

(defn immediate?
  [pn name]
  (assert (keyword? name) (cl-format nil "~S is not a keyword" name))
  (s/assert ::pn pn)
  (= :immediate (:type (name2obj pn name))))

(defn eliminate-pn
  "Transform the PN graph by eliminating the argument element."
  [pn elem]
  (s/assert ::pn pn)
  (cond (:pid elem) ; It is a place.
        (assoc pn :places (vec (remove #(= % elem) (:places pn))))
        (:tid elem) ; It is a transition
        (assoc pn :transitions (vec (remove #(= % elem) (:transitions pn))))
        (:aid elem) ; It is an arc
        (assoc pn :arcs (vec (remove #(= % elem) (:arcs pn))))))

(defn add-pn
  "Transform the PN graph by adding the argument element."
  [pn elem]
  (s/assert ::pn pn)
  (cond (:pid elem) ; It is a place.
        (assoc pn :places (conj (:places pn) elem))
        (:tid elem) ; It is a transition
        (assoc pn :transitions (conj (:transitions pn) elem))
        (:aid elem) ; It is an arc
        (assoc pn :arcs (conj (:arcs pn) elem))))

(def ^:private diag (atom nil))
(def +next-tid+ (atom 0))
(def +next-aid+ (atom 0))
(def +next-pid+ (atom 0))
(defn reset-ids! [pn]
  (reset! +next-tid+ (if (empty? (:transitions pn)) 1 (apply max (map :tid (:transitions pn)))))
  (reset! +next-aid+ (if (empty? (:arcs pn)) 1 (apply max (map :aid (:arcs pn)))))
  (reset! +next-pid+ (if (empty? (:places pn)) 1 (apply max (map :pid (:places pn))))))

(defn next-tid [pn] (swap! +next-tid+ inc))
(defn next-aid [pn] (swap! +next-aid+ inc))
(defn next-pid [pn] (swap! +next-pid+ inc))

(defn new-name
  "Return the string naming the keyword."
  [imm key suffix]
  (keyword (str (name imm) "-" (name key) suffix)))

(defn name-with-prefix
  "Return the 'next' name string with PREFIX. Thus 
   (name-with-prefix pn 'wait') might return 'wait-1'.
   AVOID is other names (keywords) to avoid, perhaps because they
   are about to be added to the PN."
  ([pn prefix] (name-with-prefix pn prefix []))
  ([pn prefix avoid] 
   (let [regex (re-pattern (str "^" prefix "-(\\d+)"))
         used (-> (map :name (:places pn))
                  (into (map :name (:arcs pn)))
                  (into (map :name (:transitions pn)))
                  (into avoid)
                  (->>
                   (map name)
                   (filter #(re-matches regex %))
                   (map #(re-matches regex %))
                   (map #(-> % second read-string))))
         id (if (empty? used) 1 (inc (apply max used)))]
     (keyword (str prefix "-" id)))))

;;; Naming convention for transitions: who is ahead of you?
(defn new-name-ahead
  [imm owner ahead]
  (new-name
   imm
   owner
   (str "--"
        (apply str (interpose "&" (map name ahead)))
        "-before")))

(defn make-arc
  [pn source target & {:keys [type aid multiplicity debug]
                       :or {type :normal aid (next-aid pn) multiplicity 1}}]
  (assert (pn? pn))
  (assert (keyword? type))
  (as-> {:aid aid :source source :target target :name (keyword (str "aa-" aid))
         :type type :multiplicity multiplicity} ?ar
    (if debug (assoc ?ar :debug debug) ?ar)))

(defn make-place
  [pn & {:keys [name pid initial-tokens]
         :or {name (keyword (str "Place-" (inc @+next-pid+)))
              pid (next-pid pn)
              initial-tokens 0}}]
  (assert (pn? pn))
  (assert (number? initial-tokens))
  {:name name :pid pid :initial-tokens initial-tokens})

(defn make-transition
  [pn & {:keys [name tid rate type]
         :or {name (keyword (str "Trans-" (inc @+next-tid+)))
              type :exponential
              tid (next-tid pn)
              rate 1.0}}]
  (assert (pn? pn))
  (assert (keyword? name))
  (assert (keyword? type))
  (assert (number? rate))
  {:name name :tid tid :type type :rate rate})

(defn initial-marking
  "Return a map {:marking-key <vector of place names> :initial-marking <vector of integers>}
   This doesn't care what the actual pid numbers are, just there relative ordering."
  [pn]
  (s/assert ::pn pn)
  (let [sorted (sort #(< (:pid %1) (:pid %2)) (:places pn))]
    {:marking-key (vec (map :name sorted))
     :initial-marking
     (vec (map :initial-tokens (sort #(< (:pid %1) (:pid %2)) sorted)))}))

(defn reorder-markings
  "Reorder the markings calculated from the reachability graph so as to match a textbook example."
  [pn new-order]
  (s/assert ::pn pn)
  (let [sgraph (set (:marking-key pn))
        sorder (set new-order)
        isect (set/intersection sgraph sorder)]
    (when (not (= (count sgraph) (count isect))) 
      (throw (ex-info "new-order invalid (count)"
                      {:diff (set/difference sgraph sorder)})))
    (assoc pn :marking-key new-order)))

(defn =*
   "Check that v1 is = v2 +/i tolerance."
  [v1 v2 tol]
  (< (- v1 tol) v2 (+ v1 tol)))

(defn vec=*
  "Check that v1 is = v2 +/i tolerance at every element."
  [v1 v2 tol]
  (every? (fn [ans] ans)
          (map #(< (- %2 tol) %1 (+ %2 tol)) v1 v2)))

;;; POD This check should not be necessary in bug-free code. 
(defn bipartite? [pn]
  (every? #(or (and (:pid (name2obj pn (:source %)))
                    (:tid (name2obj pn (:target %))))
               (and (:pid (name2obj pn (:target %)))
                    (:tid (name2obj pn (:source %)))))
          (:arcs pn)))

(defn enter-and-exit-places? [pn]
  "A state is absorbing if pjj = 1. This doesn't test that directly (steady-state calc does).
   This only checks that every place has arcs in and arcs out."
  (if (every? (fn [pl] (and (some #(= (:source %) pl) (:arcs pn))
                            (some #(= (:target %) pl) (:arcs pn))))
              (map :name (:places pn)))
    pn
    (assoc pn :failure {:reason :enter-and-exit-places})))

(defn enter-and-exit-trans? [pn]
  "A state is absorbing if pjj = 1. This doesn't test that directly (steady-state calc does).
   This only checks that every transition has arcs in and arcs out."
  (if (every? (fn [tr] (and (some #(= (:source %) tr) (:arcs pn))
                            (some #(= (:target %) tr) (:arcs pn))))
              (map :name (:transitions pn)))
    pn
    (assoc pn :failure {:reason :enter-and-exit-trans})))

(defn validate-pn
  "Return a vector of errors or [] if none."
  [pn]
  (let [arcs (filter #(= (:type %) :normal) (:arcs pn))]
    (as-> [] ?f
      ;; bipartite check
      (loop [failures ?f
             arcs (:arcs pn)]
        ;; All arcs are between places and transitions
        (let [ar (first arcs)]
          (if (empty? arcs)
            failures
            (recur (if (or (and (:pid (name2obj pn (:source ar)))
                                (:tid (name2obj pn (:target ar))))
                           (and (:pid (name2obj pn (:target ar)))
                                (:tid (name2obj pn (:source ar)))))
                     failures
                     (conj failures {:reason "PN not bipartite" :arc (:name ar)}))
                   (next arcs)))))
      ;; places have inbound and outbound
      (reduce (fn [fails pl]
                (let [name (:name pl)]
                  (if (and (some #(= name (:source %)) arcs)
                           (some #(= name (:target %)) arcs))
                    fails
                    (conj fails {:reason "Place without both in/outbound" :place name}))))
              ?f (:places pn))
      ;; transitions have inbound and outbound
      (reduce (fn [fails tr]
                (let [name (:name tr)]
                  (if (and (some #(= name (:source %)) arcs)
                           (some #(= name (:target %)) arcs))
                    fails
                    (conj fails {:reason "Transition without both in/outbound" :trans name}))))
              ?f (:transitions pn)))))

(defn pn-size
  "Calculate the size of the PN as a counting of its structural components."
  [pn]
  (+ (count (:places pn))
     (reduce (fn [sum pl] (+ sum (:initial-tokens pl))) 0 (:places pn))
     (count (:transitions pn))
     (count (:arcs pn))))

(defn avg [vals]
  (/ (float (apply + vals))
     (count vals)))

(defn arc-index
  "Return the index of the named arc in pn. (For use with assoc-in, update-in, etc.)"
  [pn name]
  (assert (keyword? name))
  (s/assert ::pn pn)
  (loop [n 0
         arcs (:arcs pn)]
    (cond (empty? arcs) nil
          (= name (:name (first arcs))) n
          true (recur (inc n) (next arcs)))))

(defn trans-index
  "Return the index of the named index in pn. (For use with assoc-in, update-in, etc.)"
  [pn name]
  (assert (keyword? name))
  (s/assert ::pn pn)
  (loop [n 0
         trans (:transitions pn)]
    (cond (empty? trans) nil
          (= name (:name (first trans))) n
          true (recur (inc n) (next trans)))))

(defn place-index
  "Return the index of the named index in pn. (For use with assoc-in, update-in, etc.)"
  [pn name]
  (assert (keyword? name))
  (s/assert ::pn pn)
  (loop [n 0
         places (:places pn)]
    (cond (empty? places) nil
          (= name (:name (first places))) n
          true (recur (inc n) (next places)))))

(defn set-marking
  "Set the marking to the argument value."
  [pn marking]
  (s/assert ::pn pn)
  (as-> pn ?pn
    (assoc ?pn :initial-marking marking)
    (update ?pn :places
            #(mapv (fn [pl val] (assoc pl :initial-tokens val))
                   %
                   marking))))

(s/fdef set-marking
        :args (s/cat :pn ::pn :m ::marking)
        :ret ::pn
        :fn #(== (-> % :args :pn :places count)
                 (-> % :args :m count)))

(defn m-mp-mp-m-valid?
  "Check a reachability graph for m-mp and mp-m errors. 
   Okay, the name is a bit silly."
  [rgraph]
   (let [m  (set (distinct (map #(:M %)  rgraph)))
         mp (set (distinct (map #(:Mp %) rgraph)))
         m-mp (set/difference m mp)
         mp-m (set/difference mp m)]
     (and (empty? m-mp)
          (empty? mp-m))))

;;; POD Does this have to consider multiplicity? 
(defn free-choice?
  "A PN is a free choice PN if every arc from a place to a transition is either
    -  the only arc from that place or 
    -  the only arc to that transition. 
   Either concurrently enabled transitions or conflict but not both at the same marking."
  [pn]
  (let [normal (filter #(= :normal (:type %)) (:arcs pn))
        pl2tr  (filter #(place? (name2obj pn (:source %))) normal)]
    (every? (fn [p2t]
              (let [the-place (:source p2t)
                    the-trans (:target p2t)]
                (or (= 1 (count (filter #(= (:source %) the-place) normal)))
                    (= 1 (count (filter #(= (:target %) the-trans) normal))))))
            pl2tr)))




