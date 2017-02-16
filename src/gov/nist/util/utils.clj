(ns gov.nist.spntools.util.utils
  (:require [clojure.data.xml :as xml :refer (parse-str)]
            [clojure.pprint :refer (cl-format pprint pp)]))


(defn ppp []
  (binding [clojure.pprint/*print-right-margin* 120]
    (pprint *1)))

(defn ppprint [arg]
  (binding [clojure.pprint/*print-right-margin* 120]
    (pprint arg)))

(defn get-id [obj]
  (-> obj :attrs :id keyword))

;;; POD Give arcs names and fix this. 
(defn tid2obj
  [pn tid]
  (some #(when (= (:tid %) tid) %) (:transitions pn)))

(defn pid2obj
  [pn pid]
  (some #(when (= (:pid %) pid) %) (:places pn)))

(defn aid2obj
  [pn aid]
  (some #(when (= (:aid %) aid) %) (:arcs pn)))


(defn arcs-into-trans
  "Return the input arcs to a transition."
  [pn tid]
  (let [tr-name (:name (tid2obj pn tid))]
    (filter #(= (:target %) tr-name) (:arcs pn))))

(defn arcs-outof-trans
  "Return the output arcs of a transition."
  [pn tid]
  (let [tr-name (:name (tid2obj pn tid))]
    (filter #(= (:source %) tr-name) (:arcs pn))))

(declare arcs-out-of-trans arcs-outof-place name2transition name2place)
(defn follow-path
  "Return a sequence of places, transitions, arcs forward of OBJ."
  [pn obj]
  (cond (:tid obj) (arcs-outof-trans pn (:tid obj)),
        (:pid obj) (arcs-outof-place pn (:name obj)),
        (:aid obj) (list (or (name2transition pn (:target obj))
                             (name2place pn (:target obj))))))

(def ^:dynamic *path-to* nil)
(defn paths-to-aux
  [pn here to nsteps & {:keys [so-far] :or {so-far []}}]
  (cond (= nsteps 0)
        (when (= (:name (last so-far)) to)
          (swap! *path-to* conj so-far))
        (> nsteps 0)
        (doseq [p (follow-path pn here)]
          (paths-to-aux pn p to (dec nsteps) :so-far (conj so-far p)))))

(defn paths-to
  "Return a path from FROM to TO (both are places) in exactly 
   STEPS steps (counting places, transitions and arcs)."
  [pn from to nsteps]
  (binding [*path-to* (atom [])]
    (paths-to-aux pn (name2place pn from) to nsteps)
    @*path-to*))
                 
(defn name2place
  [pn name]
  (some #(when (= name (:name %)) %) (:places pn)))

(defn name2transition
  [pn name]
  (some #(when (= name (:name %)) %) (:transitions pn)))

;;; This one uses :name!
(defn arcs-outof-place
  "Return the output arcs of a place."
  [pn pl-name]
  (filter #(= (:source %) pl-name) (:arcs pn)))

(defn arcs-into-place
  "Return the output arcs of a place."
  [pn pl-name]
  (filter #(= (:target %) pl-name) (:arcs pn)))

(defn immediate?
  [pn name]
  (= :immediate (:type (name2transition pn name))))

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

(def +zippy+ (atom nil))

(defn next-aid [pn]
  (if (empty? (:arcs pn))
    1
    (inc (apply max (map :aid (:arcs pn))))))

;;; Naming convention for transitions: who is ahead of you?
(defn strip-name
  [key]
  (str (str (subs (str key) 1))))

(defn new-name
  "Return the string naming the keyword."
  [key suffix]
  (keyword (str (str (subs (str key) 1)) suffix)))

(defn new-name-ahead
  [owner ahead]
  (new-name
   owner
   (str "--"
        (apply str (interpose "&" (map strip-name ahead)))
        "-before")))

(defn make-arc
  [pn source target & {:keys [type aid multiplicity]
                    :or {type :normal aid (next-aid pn) multiplicity 1}}]
  {:aid aid :source source :target target :type type :multiplicity multiplicity})


(defn initial-marking
  "Return a map {:marking-key <vector of place names> :initial-marking <vector of integers>}"
  [pn]
  (let [sorted (sort #(< (:pid %1) (:pid %2)) (:places pn))]
    {:marking-key (vec (map :name sorted))
     :initial-marking
     (vec (map :initial-marking (sort #(< (:pid %1) (:pid %2)) sorted)))}))

(defn reorder-markings
  "Reorder the markings calculated from the reachability graph so to match a textbook example."
  [graph new-order]
  (let [sgraph (set graph)
        sorder (set new-order)
        isect (clojure.set/intersection sgraph sorder)]
    (when (not (= (count graph) (count isect))) 
      (throw (ex-info "new-order invalid (count)"
                      {:diff (clojure.set/difference sgraph sorder)})))
    new-order))
