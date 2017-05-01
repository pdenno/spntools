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
      pnr/renumber-pids
      pnr/initial-tangible-state))

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

(def +max-states+ (atom 500)) ; 2017-04-29, initial-3.xml is 205 states. ; 2017-05-01 9-token.xml is 715. 

(defn Q-matrix 
  "Calculate the infinitesimal generator matrix from the reachability graph"
  [pn & {:keys [force-ordering]}] ; force-ordering is for debugging.
  (let [states (or force-ordering (:states pn))
        size (count states)
        state2ix (zipmap states (range size))]
    (as-pn-ok-> pn ?pn
      (if (> size @+max-states+) (assoc ?pn :failure {:reason :Q-exceeds-max-states :states size}) ?pn)
      (if (< size 2) (assoc ?pn :failure {:reason :Q-matrix-just-one-state}) ?pn)
      ;; POD someday, this will be parametric.
      (assoc ?pn :Q (as-> (m/mutable (m/zero-matrix size size)) ?Q
                      (reduce (fn [q link]
                                (do (mset! q
                                           (state2ix (:M link))
                                           (state2ix (:Mp link))
                                           (:rate link))
                                    q))
                              ?Q (:M2Mp pn))
                      (reduce (fn [q i] (do
                                          (mset! q i i 0.0)
                                          (mset! q i i (double (- (apply + (m/get-row q i)))))
                                          q))
                              ?Q (range size))
                      (m/sparse-matrix ?Q))))))

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
    (let [sol (ml/svd (:Q pn)) ; U makes sense xA=0 --> left null space. ; m/sparse-matrix was m/array. 
          svec (vec (m/get-column (:U sol) (zero-pos (vec (:S sol)))))
          scale (apply + svec)]
      (as-> pn ?pn
        (assoc ?pn :steady-state (zipmap (:states ?pn) (map #(/ % scale) svec)))
        (assoc ?pn :avg-tokens-on-place (avg-tokens-on-place ?pn))
        (dissoc ?pn :states :M2Mp :Q)))))

(defn avg-tokens-on-place
  "Calculate the average number of tokens on a place."
  [pn]
  (let [steady (:steady-state pn)
        ^clojure.lang.PersistentVector mk (:marking-key pn)]
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


