(ns gov.nist.spntools.util.pnml
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
     :initial-marking mark}))

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

(defn reorder-marking
  "Renumber the pids so that the marking is shown in the argument order."
  [pn order]
  (update pn :places
          (fn [places]
            (vec (map #(assoc % :pid (inc (.indexOf order (:id %)))) places)))))

                

                   
