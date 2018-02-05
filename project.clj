(defproject gov.nist/spntools "0.1.0"
  :description "Tools for generalized stochastic petri nets (GSPN), colored (CGSPN) and queueing PNs"
  :url "https://www.nist.gov/programs-projects/modeling-methodology-smart-manufacturing-systems"
  :license {:name "Eclipse Public License"
            :url "http://www.eclipse.org/legal/epl-v10.html"}
  #_ #_ :global-vars {*warn-on-reflection* true}
  :jvm-opts ["--add-modules" "java.xml.bind"] 
  :dependencies [[org.clojure/clojure "1.9.0"]
                 #_[org.clojure/data.xml "0.0.8"] ; POD cljs xml problem
                 [org.clojure/math.combinatorics "0.1.4"]
                 [net.mikera/vectorz-clj "0.47.0"]
                 [net.mikera/core.matrix "0.61.0"]]
  :repl-options {:init-ns gov.nist.spntools.util.reach})
