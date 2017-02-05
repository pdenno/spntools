(ns gov.nist.spntools
  (:require [clojure.data.xml :as xml :refer (parse-str)]
            [clojure.pprint :refer (cl-format pprint)]))

(defn get-id [obj]
  (-> obj :attrs :id keyword))

(defn get-initial-marking [pl]
  (let [str
        (-> (filter #(= :initialMarking (:tag %)) (:content pl))
            first 
            :content
            first 
            :content
            first)]
    (when (string? str)
      (when-let [match (re-matches #"Default,(.\d*)" str)]
        (read-string (nth match 1))))))

(def +pid-cnt+ (atom 0))
(def +tid-cnt+ (atom 0))
(def +aid-cnt+ (atom 0))

(defn essential-place
  [pl]
  (let [mark (get-initial-marking pl)]
    {:id (get-id pl)
     :pid (swap! +pid-cnt+ inc)
     :initial-marking mark
     ;:marking mark
     }))

(defn get-rate [tr]
    (when-let [str (-> (filter #(= :rate (:tag %)) (:content tr)) first :content first :content first)]
      (read-string str)))

(defn essential-transition
  [tr]
  (let [timed? (when-let [str (-> (filter #(= :timed (:tag %)) (:content tr)) first :content first :content first)]
                 (read-string str))]
    {:id (get-id tr)
     :tid (swap! +tid-cnt+ inc)
     :type (if timed? :exponential :immediate)
     :rate (get-rate tr)}))

(defn essential-arc
  [ar]
  {:aid (swap! +aid-cnt+ inc)
   :source (-> ar :attrs :source keyword)
   :target (-> ar :attrs :target keyword)
   :multiplicity 1}) ; POD

(defn read-pnml
  "Return a map providing the useful elements of a PNML file.
  'useful' here means things used in steady-state computation."
  [fname]
  (reset! +pid-cnt+ 0)
  (reset! +tid-cnt+ 0)
  (reset! +aid-cnt+ 0)
  (as-> {:raw (-> fname slurp xml/parse-str :content first :content)} ?m
    (assoc ?m :places (filter #(= :place (:tag %)) (:raw ?m)))
    (assoc ?m :places (vec (map essential-place (:places ?m))))
    (assoc ?m :transitions (filter #(= :transition (:tag %)) (:raw ?m)))
    (assoc ?m :transitions (vec (map essential-transition (:transitions ?m))))
    (assoc ?m :arcs (filter #(= :arc (:tag %)) (:raw ?m)))
    (assoc ?m :arcs (vec (map essential-arc (:arcs ?m))))
    (dissoc ?m :raw)))

(defn initial-marking
  [pn]
  (vec (map :initial-marking (sort #(< (:pid %1) (:pid %2)) (:places pn)))))

#_(defn marking
  [pn]
    (vec (map :marking (sort #(< (:pid %1) (:pid %2)) (:places pn)))))

;;; POD maybe memoize something that doesn't get the pn. 
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
  (let [tr-name (:id (tid2obj pn tid))]
    (filter #(= (:target %) tr-name) (:arcs pn))))

(defn arcs-outof-trans
  "Return the output arcs of a transition."
  [pn tid]
  (let [tr-name (:id (tid2obj pn tid))]
    (filter #(= (:source %) tr-name) (:arcs pn))))

(defn id2place
  [pn id]
  (some #(when (= id (:id %)) %) (:places pn)))

(defn id2transition
  [pn id]
  (some #(when (= id (:id %)) %) (:transitions pn)))

(defn fireable?
  "Return true if transition is fireable under the argument marking."
  [pn mark tid]
  (when-let [arcs (not-empty (arcs-into-trans pn tid))]
    (every? (fn [ar] (>= (nth mark (dec (:pid (id2place pn (:source ar)))))
                         (:multiplicity ar)))
            arcs)))

(defn fireables
  "Return a vector of tids that are fireable under the argument marking."
  [pn mark]
  (filter #(fireable? pn mark %) (map :tid (:transitions pn))))

(defn immediate?
  [tn]
  (= :immediate (:type tn)))

(defn mark-at-link-head
  "Return the mark that is at the head of the argument link."
  [pn [mark tid]]
  (as-> mark ?m
    (reduce (fn [mar arc]
              (let [indx (dec (:pid (id2place pn (:source arc))))] 
                (update mar indx #(- % (:multiplicity arc)))))
            ?m
            (arcs-into-trans pn tid))
    (reduce (fn [mar arc]
              (let [indx (dec (:pid (id2place pn (:target arc))))] 
                (update mar indx #(+ % (:multiplicity arc)))))
            ?m
            (arcs-outof-trans pn tid))))

(def +visited-links+ (atom []))

;;; A links between markings are the *multiple possible* transitions from the source
;;; marking. Therefore, uniqueness of the link is specified as the marking at the tail
;;; and the transition taken. Links look like [marking transition]. 
;;; The target marking is completely specified by the source and the transition. 
(defn pick-link
  "Pick a link that hasn't been visited."
  [pn mark candidate-tids]
  (let [visited @+visited-links+
        candidate-links (map (fn [tid] [mark tid]) candidate-tids)]
    (some (fn [link] (when (not-any? #(= link %) visited) link)) candidate-links)))

(defn next-marking
  "Return a map of {:from <mark argument> :trans <transaction that fired> :to <new marking>}"
  [pn mark]
  (let [tids (fireables pn mark) 
        link (pick-link pn mark tids)]
    (when link
      {:from mark :trans (:id (tid2obj pn (second link))) :to (mark-at-link-head pn link)})))

(defn calc-reachability
  [pn]
  (reset! +visited-links+ [])
  (loop [current-marking (initial-marking pn)
         graph []]
    (if-let [next (next-marking pn current-marking)]
      (do (swap! +visited-links+ conj
                 [(:from next)
                  (:tid (id2transition pn (:trans next)))])
          (recur (:to next) (conj graph next)))
      graph)))

(def machine2-example
  {:places
   [{:id :free-buffer-spots, :initial-marking 3}
    {:id :full-buffer-spots, :initial-marking 0}
    {:id :m1-busy, :initial-marking 0}
    {:id :m1-idle, :initial-marking 1}
    {:id :m2-busy, :initial-marking 0}
    {:id :m2-idle, :initial-marking 1}],
   :transitions
   [{:id :m1-complete-job, :type :exponential, :rate 1.9}
    {:id :m1-start-job, :type :immediate, :rate 1.0}
    {:id :m2-job-complete, :type :exponential, :rate 0.89}
    {:id :m2-start-job, :type :immediate, :rate 1.0}],
   :arcs
   [{:source :free-buffer-spots, :target :m1-complete-job}
    {:source :full-buffer-spots, :target :m2-start-job}
    {:source :m1-busy, :target :m1-complete-job}
    {:source :m1-complete-job, :target :full-buffer-spots}
    {:source :m1-complete-job, :target :m1-idle}
    {:source :m1-idle, :target :m1-start-job}
    {:source :m1-start-job, :target :m1-busy}
    {:source :m2-busy, :target :m2-job-complete}
    {:source :m2-idle, :target :m2-start-job}
    {:source :m2-job-complete, :target :m2-idle}
    {:source :m2-start-job, :target :free-buffer-spots}
    {:source :m2-start-job, :target :m2-busy}]})
