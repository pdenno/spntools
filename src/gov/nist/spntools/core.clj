(ns gov.nist.spntools.core
  (:require [clojure.data.xml :as xml :refer (parse-str)]
            [clojure.pprint :refer (cl-format pprint pp)]
            [gov.nist.spntools.util.reach :as pnr :refer (reachability)]
            [gov.nist.spntools.util.pnml :as pnml :refer (read-pnml reorder-places)]
            [gov.nist.spntools.util.utils :as pnu :refer :all]
            [clojure.core.matrix :as m :refer :all]
            [clojure.core.matrix.linear :as ml :refer (svd)]))

;;; ToDo: 
;;;  * Implement a DSPN algorithm (in your next life).

(m/set-current-implementation :vectorz)

(declare pn-steady-state)
(defn run-all
  [filename]
  "Diagnostic"
  (-> filename
      read-pnml
      pn-steady-state))

(defn run-ready
  [filename]
  "Diagnostic"
  (-> filename
      read-pnml
      pnr/renumber-pids))

;(def m (run-ready "data/weights.xml"))

;;; =========== Steady State Calculation ===============================================
(declare Q-matrix steady-state-props avg-tokens-on-place)
(defn pn-steady-state
  [pn]
  "Calculate and add steady-state properties to the argument PN."
  (pn-ok-> pn
           pnr/reachability
           Q-matrix
           steady-state-props))

;;; The transition rate M --> Mp  (i not= j) is the sum of the firing rates of
;;; the transitions enabled by the markings Mi that generate Mj. 
;;; Where M=Mp, it is negative of the the sum of the firing rates enabled.
(defn calc-rate 
  "Return the transition rate between marking M and Mp."
  [pn m mp]
  (let [graph (:M2Mp pn)]
    (if (= m mp)
      (- (reduce #(+ %1 (:rate %2)) 0.0 (filter #(and (= (:M %) m) (not (= (:Mp %) m))) graph)))
      (reduce #(+ %1 (:rate %2)) 0.0 (filter #(and (= (:M %) m) (= (:Mp %) mp)) graph)))))

(def +max-states+ (atom 200))

(defn Q-matrix 
  "Calculate the infinitesimal generator matrix from the reachability graph"
  [pn & {:keys [force-ordering]}] ; force-ordering is for debugging.
  (let [states (or force-ordering (distinct (map :M (:M2Mp pn))))
        size (count states)]
    (as-pn-ok-> pn ?pn
      (if (> size @+max-states+) (assoc ?pn :failure {:reason :Q-exceeds-max-states :states size}) ?pn)
      (if (< size 2) (assoc ?pn :failure {:error :Q-matrix :reason "Just one state."}) ?pn)
      (assoc ?pn :Q ; POD someday, this will be parametric. 
             (vec (map
                   (fn [irow]
                     (vec (map (fn [icol] (calc-rate ?pn (nth states (dec irow)) (nth states (dec icol))))
                               (range 1 (inc size)))))
                   (range 1 (inc size)))))
      (assoc ?pn :states states))))

(defn zero-pos
  "Return the position of the value closest to zero."
  [v]
  (let [size (count v)]
    (loop [i 1
           mini (abs (first v))
           min-pos 0]
      (cond (= i size) min-pos,
            (< (abs (nth v i)) mini)
            (recur (inc i) (abs (nth v i)) i),
            :else
            (recur (inc i) mini min-pos)))))

(defn steady-state-props
  "Calculate steady-state props for a PN for which the Q matrix has been generated."
  [pn]
  (if (:failure pn)
    pn
    (let [sol (ml/svd (m/array (:Q pn))) ; U makes sense xA=0 --> left null space.
          svec (vec (m/get-column (:U sol) (zero-pos (vec (:S sol)))))
          scale (apply + svec)]
      (as-> pn ?pn
        (assoc ?pn :steady-state (zipmap (:states ?pn) (map #(/ % scale) svec)))
        (assoc ?pn :avg-tokens-on-place (avg-tokens-on-place ?pn))
        (dissoc ?pn :states)))))

(defn avg-tokens-on-place
  "Calculate the average number of tokens on a place."
  [pn]
  (let [steady (:steady-state pn)
        mk (:marking-key pn)]
    (zipmap mk
            (map (fn [place]
                   (let [place-pos (.indexOf mk place)]
                     (reduce (fn [sum [state prob]] (+ sum (* (nth state place-pos) prob)))
                             0.0
                             steady)))
                 mk))))

(defn quick-test []
  (let [result (:avg-tokens-on-place (pn-steady-state (read-pnml "data/qo10.xml")))
        correct  {:P1 0.111111, :P2 0.0, :P3 0.0, :P4 0.0, :P5 0.416667, 
                  :P6 0.333333, :P7 0.083333,  :P8 0.055556}]
        (every? (fn [[key val]]
                  (=* val (get correct key) 0.0001))
                result)))


