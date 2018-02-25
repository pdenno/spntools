(ns gov.nist.spntools.pncats
  "Categorical modeling of Petri nets"
  (:require [clojure.spec.alpha :as s]
            [clojure.set :as set]
            [uncomplicate.fluokitten.core :as flc]
            [uncomplicate.fluokitten.jvm :as flm]            
            [gov.nist.spntools.utils :refer (ppprint ppp)]))

(def test-pn
  {:places [{:name :p1 :initial-tokens 0},
            {:name :p2 :initial-tokens 0},
            {:name :p3 :initial-tokens 0},
            {:name :p4 :initial-tokens 0},
            {:name :p5 :initial-tokens 0}]
   :transitions [{:name :t1} {:name :t2} {:name :t3}]
   :arcs [{:name :a1 :source :p1 :target :t1 :multiplicity 2}
          {:name :a2 :source :p2 :target :t1 :multiplicity 1}
          {:name :a3 :source :t1 :target :p3 :multiplicity 1}
          {:name :a4 :source :p3 :target :t2 :multiplicity 1}
          {:name :a5 :source :t2 :target :p4 :multiplicity 1}
          {:name :a6 :source :p4 :target :t3 :multiplicity 1}
          {:name :a7 :source :t3 :target :p5 :multiplicity 1}]})

;;;====================================================================
;;; T[N] from Meseguer and Montanari, "Petri Nets are Monoids" (1990)
;;;====================================================================
(declare M&M-Trule1 M&M-Trule2 M&M-Trule3 M&M-Trule4)

(defn M&M-T [pn]
  (-> (assoc pn :TN {:arcs {} :S-oplus-identities #{} :nodes #{} :S-oplus #{}})
      M&M-Trule1
      M&M-Trule2))

;;; 4 inference rules:

;;;  t : u -> v in N
;;; -------------------
;;;  t : u -> v in T[N]
(defn M&M-Trule1
  "Apply rule1 to PN, adding to :arcs and :s-plus."
  [pn]
  (as-> pn ?pn
      (assoc-in ?pn [:TN :arcs]
                (zipmap (map :name (:transitions pn))
                        (map (fn [t]
                               (vec
                                (flatten
                                 (vector
                                  (interpose :oplus (mapv #(vector (:multiplicity %) (:source %))
                                                     (filter #(= t (:target %)) (:arcs pn))))
                                  :rightA
                                  (interpose :oplus (mapv #(vector (:multiplicity %) (:target %))
                                                     (filter #(= t (:source %)) (:arcs pn))))))))
                             (map :name (:transitions pn)))))
      (assoc-in ?pn [:TN :S-oplus]
                (set (reduce (fn [Sset arc]
                               (let [[lhs _ rhs] (partition-by #{:rightA} arc)]
                                 (-> Sset
                                     (conj (vec lhs))
                                     (conj (vec rhs)))))
                             #{}
                             (vals (-> ?pn :TN :arcs)))))))

;;; u in S^\oplus
;;; -------------------
;;; u : u -> u in T[N]
(defn M&M-Trule2
  "Apply Rule 2 to the PN, adding S^oplus identity arcs."
  [pn]
  (update-in pn [:TN :S-oplus-identities]
             (fn [iarc]
               (set/union iarc (set (map #(vec (flatten (vector % :rightA %)))
                                         (-> pn :TN :S-oplus)))))))
   
;;; alpha : u -> v,  alpha' : u' -> v' in T[N]
;;; --------------------------------------------------------
;;; alpha :oplus alpha' : u :oplus u' -> v \opus v' in T[N]
(defn M&M-Trule3 [])
  

  
;;; alpha : u -> v, beta : v -> w in T[N]
;;; -------------------------------------
;;; alpha ; beta : u -> w in T[N]





