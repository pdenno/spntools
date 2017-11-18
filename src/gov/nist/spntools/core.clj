(ns gov.nist.spntools.core
  (:require [clojure.data.xml :as xml :refer (parse-str)]
            [clojure.pprint :refer (cl-format pprint pp)]
            [clojure.spec.alpha :as s]
            [gov.nist.spntools.util.reach :as pnr :refer (reachability)]
            [gov.nist.spntools.util.pnml :as pnml :refer (read-pnml reorder-places)]
            [gov.nist.spntools.util.utils :as pnu :refer :all]
            [clojure.core.matrix :as m :refer :all]
            [clojure.core.matrix.linear :as ml :refer (svd)]))

;;; ToDo: 
;;;  * Implement a DSPN algorithm (in your next life).

(m/set-current-implementation :vectorz)

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

(defn classify
  "Classify a net according to the usual descriptive terms."
  [pn]
  (assoc pn :classification
         {:free-choice? (free-choice? pn)}))


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
  "Calculate the infinitesimal generator matrix from the reachability graph.
   The calculation is 'parametric' if a map of rates for the transitions is supplied."
  [pn & {:keys [rates force-ordering]}] ; force-ordering is for debugging.
  (let [states (or force-ordering (:states pn))
        size (count states)
        state2ix (zipmap states (range size))]
    (as-pn-ok-> pn ?pn
      (if (> size @+max-states+) (assoc ?pn :failure {:reason :Q-exceeds-max-states :states size}) ?pn)
      (if (< size 2) (assoc ?pn :failure {:reason :Q-matrix-just-one-state}) ?pn)
      (assoc ?pn :Q (as-> (m/mutable (m/zero-matrix size size)) ?Q
                      (reduce (fn [q link]
                                (do (m/mset! q
                                           (state2ix (:M link))
                                           (state2ix (:Mp link))
                                           (if rates
                                             ((:rate-fn link) rates)
                                             (:rate link)))
                                    q))
                              ?Q (:M2Mp pn))
                      (reduce (fn [q i] (do
                                          (m/mset! q i i 0.0)
                                          (m/mset! q i i (double (- (apply + (m/get-row q i)))))
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
