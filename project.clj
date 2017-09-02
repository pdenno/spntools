(defproject gov.nist/spntools "0.1.0-SNAPSHOT"
  :description "Tools for generalized stochastic petri nets (GSPN), colored (CGSPN) and queueing PNs"
  :url "https://www.nist.gov/programs-projects/modeling-methodology-smart-manufacturing-systems"
  :license {:name "Eclipse Public License"
            :url "http://www.eclipse.org/legal/epl-v10.html"}
  ;:global-vars {*warn-on-reflection* true}
  :dependencies [[org.clojure/clojure "1.8.0"]
                 [org.clojure/data.xml "0.0.8"]
                 [org.clojure/math.combinatorics "0.1.4"]
                 [net.mikera/vectorz-clj "0.46.0"]
                 [net.mikera/core.matrix "0.57.0"]])
