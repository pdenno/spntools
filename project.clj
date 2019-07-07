(defproject pdenno/spntools "0.1.0"
  :description "Basic tools for Generalized Stochastic Petri Nets (GSPN), colored (CGSPN) and queueing PNs.
                Excludes steady-state calculation. (See pdenno/gspn for that.)"
  :url "https://www.nist.gov/programs-projects/modeling-methodology-smart-manufacturing-systems"
  :license {:name "Eclipse Public License"
            :url "http://www.eclipse.org/legal/epl-v10.html"}
  #_ #_ :global-vars {*warn-on-reflection* true}
  :dependencies [[org.clojure/clojure "1.9.0"]
                 [org.clojure/data.xml "0.0.8"] ; POD cljs xml problem
                 [uncomplicate/fluokitten "0.6.1"]]
  :repl-options {:init-ns gov.nist.spntools.reach})




