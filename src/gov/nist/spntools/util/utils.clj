(ns gov.nist.spntools.util.utils
  (:require [clojure.data.xml :as xml :refer (parse-str)]
            [clojure.pprint :refer (cl-format pprint pp)]))

;;;=== General =========================
(defn ppp []
  (binding [clojure.pprint/*print-right-margin* 150]
    (pprint *1)))

(defn ppprint [arg]
  (binding [clojure.pprint/*print-right-margin* 150]
    (pprint arg)))

;;;=== Petri Nets =========================
(def +obj-cnt+ (atom 0))

(defn tid2obj
  [pn tid]
  (some #(when (= (:tid %) tid) %) (:transitions pn)))

(defn pid2obj
  [pn pid]
  (some #(when (= (:pid %) pid) %) (:places pn)))

(defn aid2obj
  [pn aid]
  (some #(when (= (:aid %) aid) %) (:arcs pn)))

(defn arcs-into
  "Return the arcs into the named object."
  [pn name]
  (filter #(= (:target %) name) (:arcs pn)))

(defn arcs-outof
  "Return the arcs exiting the named object."
  [pn name]
  (filter #(= (:source %) name) (:arcs pn)))

(defn name2obj
  [pn name]
  (or 
   (some #(when (= name (:name %)) %) (:places pn))
   (some #(when (= name (:name %)) %) (:transitions pn))
   (some #(when (= name (:name %)) %) (:arcs pn))))

(def ^:dynamic *path-to* nil)
(def ^:dynamic *visited* nil)
(defn follow-path
  "Return a sequence of places, transitions, arcs forward of OBJ."
  [pn obj]
  (cond (:tid obj) (arcs-outof pn (:name obj)),
        (:pid obj) (arcs-outof pn (:name obj)),
        (:aid obj) (if (contains? @*visited* (:target obj))
                     nil
                     (do (swap! *visited* conj (:target obj))
                         (list (name2obj pn (:target obj)))))))

(defn follow-path-back
  "Return a sequence of places, transitions, arcs forward of OBJ."
  [pn obj]
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
  (binding [*path-to* (atom [])
            *visited* (atom #{from})]
    (paths-to-aux pn (name2obj pn from) to nsteps :back? back?)
    @*path-to*))

(defn pn?
  "If the argument is a Petri net, return it; otherwise return false."
  [obj]
  (and (:places obj) (:transitions obj) (:arcs obj) obj))

(defn arc? [obj] (:aid obj))
(defn place? [obj] (:pid obj))
(defn transition? [obj] (:tid obj))
(defn pn-obj? [obj] (or (:aid obj) (:tid obj) (:pid obj)))

(defn immediate?
  [pn name]
  (= :immediate (:type (name2obj pn name))))

(defn eliminate-pn
  "Transform the PN graph by eliminating the argument element."
  [pn elem]
  (cond (:pid elem) ; It is a place.
        (assoc pn :places (vec (remove #(= % elem) (:places pn))))
        (:tid elem) ; It is a transition
        (assoc pn :transitions (vec (remove #(= % elem) (:transitions pn))))
        (:aid elem) ; It is an arc
        (assoc pn :arcs (vec (remove #(= % elem) (:arcs pn))))))

(defn add-pn
  "Transform the PN graph by adding the argument element."
  [pn elem]
  (cond (:pid elem) ; It is a place.
        (assoc pn :places (conj (:places pn) elem))
        (:tid elem) ; It is a transition
        (assoc pn :transitions (conj (:transitions pn) elem))
        (:aid elem) ; It is an arc
        (assoc pn :arcs (conj (:arcs pn) elem))))

(def +diag+ (atom nil))
(def +next-tid+ (atom 0))
(def +next-aid+ (atom 0))
(def +next-pid+ (atom 0))
(defn reset-ids! [pn]
  (reset! +next-tid+ (if (empty? (:transitions pn)) 0 (apply max (map :tid (:transitions pn)))))
  (reset! +next-aid+ (if (empty? (:arcs pn)) 0 (apply max (map :aid (:arcs pn)))))
  (reset! +next-pid+ (if (empty? (:places pn)) 0 (apply max (map :pid (:places pn))))))

(defn next-tid [pn] (swap! +next-tid+ inc))
(defn next-aid [pn] (swap! +next-aid+ inc))
(defn next-pid [pn] (swap! +next-pid+ inc))

(defn new-name
  "Return the string naming the keyword."
  [imm key suffix]
  (keyword (str (name imm) "-" (name key) suffix)))

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
  (as-> {:aid aid :source source :target target :name (keyword (str "aa-" aid))
         :type type :multiplicity multiplicity} ?ar
    (if debug (assoc ?ar :debug debug) ?ar)))

(defn make-place
  [pn & {:keys [name pid initial-marking]
         :or {name (keyword (str "Place-" (inc @+next-pid+)))
              pid (next-pid pn)
              initial-marking 0}}]
  {:name name :pid pid :initial-marking initial-marking})

(defn make-transition
  [pn & {:keys [name tid rate type]
         :or {name (keyword (str "Trans-" (inc @+next-tid+)))
              type :exponential
              tid (next-tid pn)
              rate 1.0}}]
  {:name name :tid tid :type type :rate rate})

(defn initial-marking
  "Return a map {:marking-key <vector of place names> :initial-marking <vector of integers>}"
  [pn]
  (let [sorted (sort #(< (:pid %1) (:pid %2)) (:places pn))]
    {:marking-key (vec (map :name sorted))
     :initial-marking
     (vec (map :initial-marking (sort #(< (:pid %1) (:pid %2)) sorted)))}))

(defn reorder-markings
  "Reorder the markings calculated from the reachability graph so as to match a textbook example."
  [pn new-order]
  (let [sgraph (set (:marking-key pn))
        sorder (set new-order)
        isect (clojure.set/intersection sgraph sorder)]
    (when (not (= (count sgraph) (count isect))) 
      (throw (ex-info "new-order invalid (count)"
                      {:diff (clojure.set/difference sgraph sorder)})))
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
  "A state is absorbing in pjj = 1. This doesn't test that directly (steady-state calc does).
   This only checks that every place has arcs in and arcs out."
  (every? (fn [pl] (and (some #(= (:source %) pl) (:arcs pn))
                        (some #(= (:target %) pl) (:arcs pn))))
          (map :name (:places pn))))

(defn enter-and-exit-trans? [pn]
  "A state is absorbing in pjj = 1. This doesn't test that directly (steady-state calc does).
   This only checks that every place has arcs in and arcs out."
  (every? (fn [pl] (and (some #(= (:source %) pl) (:arcs pn))
                        (some #(= (:target %) pl) (:arcs pn))))
          (map :name (:transitions pn))))

(defn validate-pn
  [pn]
  (let [failures (atom [])]
    (loop [arcs (:arcs pn)]
      (when-not (empty? arcs)
        (let [ar (first arcs)]
          (when-not
              ;; All arcs are between places and transitions
              (or (and (:pid (name2obj pn (:source ar)))
                       (:tid (name2obj pn (:target ar))))
                  (and (:pid (name2obj pn (:target ar)))
                       (:tid (name2obj pn (:source ar)))))
            (swap! failures conj {:reason "PN not bipartite" :arc ar})))
        (recur (rest arcs))))
    ;; Every place and transition has arcs in and arcs out. 
    @failures))

