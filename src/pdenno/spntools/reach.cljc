(ns pdenno.spntools.reach
  "reachability, excluding GSPN calculations."
  (:require [clojure.pprint :refer (cl-format pprint pp)]
            [clojure.set :as set]
            #?(:clj [clojure.spec.alpha :as s])
            [pdenno.spntools.utils :as util]))

(declare next-mark)

;(def +revisited+ "diagnostic" 0)
(defn note-link-visited
  "Links are tracked by :M and :fire because (1) :fire could be a path,
   or (2) :rate might differ, or (3) good for diagnostics."
  [lis link]
  (let [key (vector (:M link) (:fire link))]
    #_(when (visited? list link)
      (alter-var-root #'+revisited+ inc)
      (println "Link already visited:" link)) ; keep
    (assoc lis key link)))

(defn fireable? 
  "Return true if transition is fireable under the argument marking."
  [pn mark tr-name]
  (assert (keyword? tr-name))
  (let [arcs (util/arcs-into pn tr-name)
        arc-groups (group-by :type arcs)
        ^clojure.lang.PersistentVector marking-key (:marking-key pn)]
    (and
     (every? (fn [ar] (>= (nth mark (.indexOf marking-key (:source ar)))
                          (:multiplicity ar)))
             (:normal arc-groups))
     (every? (fn [ar] (<  (nth mark (.indexOf marking-key (:source ar)))
                          (:multiplicity ar)))
             (:inhibitor arc-groups)))))

(defn find-link ; POD xml 2018-02-05 was commented ?!?
  [pn M trn list]
  (get list (vector M trn)))

#?(:clj (s/def ::visited map?))
#?(:clj (s/def ::trn keyword?))
#?(:clj (s/def ::m vector?))
#?(:clj (s/def ::pn ::util/pn))
#?(:clj (s/fdef find-link
        :args (s/cat :pn ::pn :M ::m :trn ::trn :list ::visited)
        :ret  (s/or :map map? :nil nil?)))

;;; The target marking is completely specified by the source (marking at tail) and the transition.
(defn next-links
  "Return nil or a vector of maps [{:M <tail-marking> :trans <transition that fired> :Mp <head-marking>}...]
   which contain the argument state :M and unexplored states, :Mp reachable by firing :trans.
   Returned links have adjusted weights when transitions are immediate."
  ([pn mark] (next-links pn mark false))
  ([pn mark visited]
   (if mark
     (let [trns
           (as-> (map :name (:transitions pn)) ?trns
             (filter #(fireable? pn mark %) ?trns)
             (if (some #(util/immediate? pn %) ?trns) (filter #(util/immediate? pn %) ?trns) ?trns)
             ;; If visited specified, it tracks mark/trans already visited. Remove these.
             (if visited (remove #(find-link pn mark % visited) ?trns) ?trns))
           imm? (and (not-empty trns) (util/immediate? pn (first trns)))
           trs  (map #(util/name2obj pn %) trns)
           sum (when imm? (apply + (map :rate trs)))]
       (not-empty
        (vec
         (map (fn [tr]
                {:M mark
                 :fire (:name tr)
                 :Mp (next-mark pn mark (:name tr))
                 :rate-fn (if imm?
                            (fn [rates]
                              (/ ((:name tr) rates)
                                 (apply + (map (fn [r] (r rates)) trns))))
                            (fn [rates] ((:name tr) rates)))
                 :rate (if imm? (/ (:rate tr) sum) (:rate tr))})
              trs))))
     nil)))


(defn next-mark
  "Return the mark that is at the head of the argument link."
  [pn mark tr-name]
  (assert (keyword? tr-name))
  (as-> mark ?m
    (reduce (fn [mar arc]
              (let [indx (:pid (util/name2obj pn (:source arc)))] 
                (update mar indx #(- % (:multiplicity arc)))))
            ?m
            (filter #(= (:type %) :normal) (util/arcs-into pn tr-name)))
    (reduce (fn [mar arc] 
              (let [indx (:pid (util/name2obj pn (:target arc)))] 
                (update mar indx #(+ % (:multiplicity arc)))))
            ?m ; inhibitors don't exit transitions
            (util/arcs-outof pn tr-name))))

(defn next-marks
  "Return a list of states enabled by the argument state."
  ([pn mark] (next-marks pn mark false))
  ([pn mark clist]
   (let [trns
         (as-> (map :name (:transitions pn)) ?trns
           (filter #(fireable? pn mark %) ?trns)
           (if (some #(util/immediate? pn %) ?trns)
             (filter #(util/immediate? pn %) ?trns)
             ?trns))
         marks (map #(next-mark pn mark %) trns)]
     (remove (fn [m] (some #(= % m)
                           (cond (keyword? clist) (clist pn)
                                 clist clist
                                 :else [])))
             marks))))

(defn renumber-pids
  "Number the pids from 0 so that they can be used as an index into the marker.
   Reduction makes this necessary. ALSO (no really, this is the right way!) set
   the :marking-key and :initial-marking"
  [pn]
  (as-> pn ?pn
    (update ?pn :places
            (fn [places]
              (let [order (vec (sort #(< (:pid %1) (:pid %2)) places))]
                (reduce (fn [order id] (assoc-in order [id :pid] id))
                        order
                        (range (count order))))))
    (let [im (util/initial-marking ?pn)]
      (as-> ?pn ?pn2
        (assoc ?pn2 :marking-key (:marking-key im))
        (assoc ?pn2 :initial-marking (:initial-marking im))))))

(defn k-bounding
  "Filter links, returning only those for which :M and :Mp <= k."
  [links max-marks]
  (if max-marks
    (->> links
         (filterv (fn [link] (every? identity (map #(<= %1 %2) (:M  link) max-marks))))
         (filterv (fn [link] (every? identity (map #(<= %1 %2) (:Mp link) max-marks)))))
    links))

;;;=========================================================================================
;;;================================= Simple Stuff (735% Faster!) ===========================
;;;=========================================================================================
(defn simple-find-link 
  [pn M trn list]
  (get list (vector M trn)))

(defn simple-fireable? 
  "Return true if transition is fireable under the argument marking."
  [pn mark tr-name]
  (let [^clojure.lang.PersistentVector marking-key (:marking-key pn)]
    (and
     (every? (fn [ar] (>= (nth mark (.indexOf marking-key (:source ar)))
                          (:multiplicity ar)))
             (-> pn :arcs-into tr-name :normal))
     (every? (fn [ar] (<  (nth mark (.indexOf marking-key (:source ar)))
                          (:multiplicity ar)))
             (-> pn :arcs-into tr-name :inhibitor)))))

(defn simple-next-mark
  "Return the mark that is at the head of the argument link."
  [pn mark tr-name]
  (as-> mark ?m
    (reduce (fn [mar arc]
              (let [src (:source arc)
                    indx (-> pn :place-map src :pid)]
                (update mar indx #(- % (:multiplicity arc)))))
            ?m
            (-> pn :arcs-into tr-name :normal))
    (reduce (fn [mar arc] 
              (let [tar (:target arc)
                    indx (-> pn :place-map tar :pid)]
                (update mar indx #(+ % (:multiplicity arc)))))
            ?m ; inhibitors don't exit transitions
            (-> pn :arcs-outof tr-name))))

(defn simple-next-links
  "next-links with no rates, no immediate transition checking."
  ([pn mark] (simple-next-links pn mark false))
  ([pn mark visited]
   (if mark
     (let [tr-map (:trans-map pn)
           trns
           (as-> (:trns pn) ?trns
             (filter #(simple-fireable? pn mark %) ?trns)
             ;; If visited specified, it tracks mark/trans already visited. Remove these.
             (if visited (remove #(simple-find-link pn mark % visited) ?trns) ?trns))
           trs (map tr-map trns)]
       (not-empty
        (vec
         (map (fn [tr]
                {:M mark
                 :fire (:name tr)
                 :Mp (simple-next-mark pn mark (:name tr))})
              trs))))
     nil)))

(defn simple-note-link-visited
  "Links are tracked by :M and :fire because (1) :fire could be a path,
   or (2) :rate might differ, or (3) good for diagnostics."
  [lis link]
  (let [key (vector (:M link) (:fire link))]
    (assoc lis key link)))

;;; Reachability Graph (includes vanishing markings).
;;; Much simpler than tangible reachability graph! No paths. 
(defn simple-reach
  "Return {:rgraph ... :k-limited? true/false} where :rgraph is the reachability graph 
   (including non-tangible states) of the argument PN, treating all transitions as timed 
   and bounding k. max-marks is a vector providing the max-k value for each place in the 
   :marking-key."
  ([pn] (simple-reach pn false))
  ([pn max-marks]
   (let [k-limited? (atom false)] ; No with-local-vars in cljs
     (let [pn (as-> pn ?pn
                (assoc ?pn :trns (map :name (:transitions ?pn)))
                (util/follow-path-preprocess ?pn))
           nexts1 (simple-next-links pn (:initial-marking pn))
           nexts2 (k-bounding nexts1 max-marks)]
       (when (not= (count nexts1) (count nexts2))
         (reset! k-limited? true))
       (loop [visited  {}
              to-visit nexts2]
         (if (empty? to-visit)
           {:k-limited? @k-limited? ; done
            :rgraph (reduce (fn [result [[mark trans] link]]
                              (update result mark #(conj % [trans (:Mp link)])))
                            {}
                            visited)}
           (let [nexts1 (simple-next-links pn (-> to-visit first :Mp) visited)
                 nexts2 (k-bounding nexts1 max-marks)]
             (when (not= (count nexts1) (count nexts2))
               (reset! k-limited? true))
             (recur
              (simple-note-link-visited visited (first to-visit))
              (if (empty? nexts2)
                (next to-visit)
                (into nexts2 (rest to-visit)))))))))))

(defn simple-reach-valid?
  "Check a reachability graph for m-mp and mp-m errors."
  [rgraph]
   (let [m  (set (keys rgraph))
         mp (reduce-kv (fn [accum k v]
                         (into accum (map second v)))
                       #{}
                       rgraph)
         m-mp (set/difference m mp)
         mp-m (set/difference mp m)]
     (and (empty? m-mp)
          (empty? mp-m))))

