(ns gov.nist.spntools.util.utils
  (:require [clojure.data.xml :as xml :refer (parse-str)]
            [clojure.pprint :refer (cl-format pprint pp)]))

;;;=== General =========================
(defn ppp []
  (binding [clojure.pprint/*print-right-margin* 120]
    (pprint *1)))

(defn ppprint [arg]
  (binding [clojure.pprint/*print-right-margin* 120]
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

(defn follow-path
  "Return a sequence of places, transitions, arcs forward of OBJ."
  [pn obj]
  (cond (:tid obj) (arcs-outof pn (:name obj)),
        (:pid obj) (arcs-outof pn (:name obj)),
        (:aid obj) (list (name2obj pn (:target obj)))))

(defn follow-path-back
  "Return a sequence of places, transitions, arcs forward of OBJ."
  [pn obj]
  (cond (:tid obj) (arcs-into pn (:name obj)),
        (:pid obj) (arcs-into pn (:name obj)),
        (:aid obj) (list (name2obj pn (:source obj)))))

(def ^:dynamic *path-to* nil)
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
  "Return a path from FROM to TO (both are names of places or transitions) 
   in exactly STEPS steps (counting places, transitions and arcs)."
  [pn from to nsteps & {:keys [back?]}]
  (binding [*path-to* (atom [])]
    (paths-to-aux pn (name2obj pn from) to nsteps :back? back?)
    @*path-to*))

(defn pn? [obj]
  (and (:places obj) (:transitions obj) (:arcs obj)))

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

(defn next-tid [pn]
  (if (empty? (:transitions pn))
    1
    (inc (apply max (map :tid (:transitions pn))))))

(def +diag+ (atom nil))

(defn next-aid [pn]
  (if (empty? (:arcs pn))
    1
    (inc (apply max (map :aid (:arcs pn))))))

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
  [pn source target & {:keys [type aid multiplicity]
                    :or {type :normal aid (next-aid pn) multiplicity 1}}]
  {:aid aid :source source :target target :name (keyword (str "aa-" aid))
   :type type :multiplicity multiplicity})

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

(defn validate-pn
  [pn]
  (let [failures (atom [])]
    (loop [arcs (:arcs pn)]
      (when-not (empty? arcs)
        (let [ar (first arcs)]
          (when-not
              ;; All arcs are between places and transitions
              (or (and (:pid (:source ar))
                       (:tid (:target ar)))
                  (and (:pid (:target ar))
                       (:tid (:source ar))))
            (swap! failures conj {:reason "Arc not pointing to a place or transition" :arc ar})))
        (recur (rest arcs))))
    ;; Every place and transition has arcs in and arcs out. 
    @failures))


;;;=== Schema =========================
(def +schemas+ (atom {}))

;;; POD Need to learn clojure.spec!
(defn check-schema
  [top-node]
  (let [errors (atom [])]
    (loop [node (:topology top-node)]
      (when-not (contains? #{:place :immediate :normal :arc :focus} (:type node))
        (swap! errors conj {:reason "Bad type" :node node}))
      (when-not (contains? #{:keep :eliminate :replace} (:plan node))
        (swap! errors conj {:reason "Bad plan" :node node}))
      (when-not (contains? #{-1 0 1} (first (:multiplicity node)))
        (swap! errors conj {:reason "Bad multiplicity" :node node}))
      (when-not (contains? #{-1 0 1} (second (:multiplicity node)))
        (swap! errors conj {:reason "Bad multiplicity" :node node}))
      (if-let [child (:child node)]
        (recur child)
        @errors))))

;;; So far, don't need a macro. 
(defn defschema
  [name body]
  (let [check (check-schema body)]
    (if (empty? check)
      (swap! +schemas+ assoc name body)
      {:reason "failed check-schema" :fail check})))

(defn schema-search-aux
  [body search-fn]
  (cond (search-fn body) body
        (:child body) (schema-search-aux (:child body) search-fn)))

(defn schema-search
  "Search the schema for a node matching the search-fn"
  [schema-name search-fn & {:keys [truncate?]}]
  (let [schema (schema-name @+schemas+)
        result (schema-search-aux (:topology schema) search-fn)]
    (if truncate?
      (dissoc result :child)
      result)))

(defn schema-node-parent
  [schema-name node-name]
  (schema-search schema-name #(= (:name (:child %)) node-name)))

;;;========= PN binding to schema ===============================
(def +schema-binds+ (atom {}))
(def ^:dynamic *schema-name*)

(defn schema-binds-nav-fn
  [pn elem node & {:keys [dir] :or {dir :search}}]
  ;; For now, just this. Might want argument info in schema.
  (when-let [search-fn (dir node)]
    (let [result (search-fn pn elem)]
      (if (pn-obj? result)
        (vector result)
        result))))
  
(defn schema-binds-down-aux
  [pn parent-elem elem schema-down]
  (when schema-down
    (swap! +schema-binds+ update-in [(:name schema-down)] conj elem)
    (map #(schema-binds-down-aux pn elem % (:child schema-down))
         (schema-binds-nav-fn pn elem schema-down))))

(defn schema-binds-down
  [pn pn-elem schema-down]
  (map #(schema-binds-down-aux pn pn-elem % schema-down)
       (follow-path pn pn-elem)))

(defn schema-binds-up-aux
  [pn parent-elem elem schema-up]
  (when schema-up
    (swap! +schema-binds+ update-in [(:name schema-up)] conj elem)
    (map #(schema-binds-up-aux pn elem % (schema-node-parent *schema-name* (:name schema-up)))
         (schema-binds-nav-fn pn elem schema-up :dir :search-up))))

(defn schema-binds-up
  [pn pn-elem schema-up]
  (map #(schema-binds-up-aux pn pn-elem % schema-up)
       (follow-path-back pn pn-elem)))

(defn build-patterns
  "Instantiate the schema with all instances found in pn."
  [schema-name pn]
  (binding [*schema-name* schema-name]
    (let [schema (schema-name @+schemas+)
          focus-node (schema-search schema-name #(= :focus (:type %)))
          centers ((:select focus-node) pn)]
      (map (fn [center]
             (reset! +schema-binds+ {(:name focus-node) center})
             (schema-binds-down pn center (:child focus-node))
             (schema-binds-up pn center (schema-node-parent schema-name (:name focus-node))))
           centers))
    @+schema-binds+))

      
  
