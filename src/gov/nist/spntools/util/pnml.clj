(ns gov.nist.spntools.util.pnml
  (:require [clojure.data.xml :as xml :refer (parse-str)]
            [clojure.pprint :refer (cl-format pprint)]
            [gov.nist.spntools.util.utils :refer :all]))

;;; To Do:
;;;       - Add label info to positions-from-file.
;;;       - Update IMM :rate (weight) information to be probabilities so that
;;;         these can be used in the on-the-fly state-space generation algorithm.

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

(defn get-multiplicity [ar]
  (let [str
        (-> (filter #(= :inscription (:tag %)) (:content ar))
            first 
            :content
            first 
            :content
            first)]
    (if (string? str)
      (when-let [match (re-matches #"Default,(.\d*)" str)]
        (read-string (nth match 1)))
      1))) ; PIPE doesn't set multiplicity of inhibitory arcs.

(defn get-pos
  "Get the position of the transition or place and its label."
  [elem]
  (let [pos (-> elem :content first :content first :attrs)
        label-pos (as-> elem ?m
                    (:content ?m)
                    (filter #(= :name (:tag %)) ?m)
                    (first ?m)
                    (:content ?m)
                    (filter #(= :graphics (:tag %)) ?m)
                    (first ?m)
                    (:content ?m)
                    (first ?m)
                    (:attrs ?m))]
    (hash-map :x (read-string (:x pos))
              :y (read-string (:y pos))
              :label-x-off (read-string (:x label-pos))
              :label-y-off (read-string (:y label-pos)))))

(defn essential-place
  [pl]
  (let [mark (get-initial-marking pl)]
    {:name (get-id pl)
     :pid (swap! +obj-cnt+ inc)
     :initial-marking mark}))

(defn get-rate [tr]
    (when-let [str (-> (filter #(= :rate (:tag %)) (:content tr)) first :content first :content first)]
      (read-string str)))

(defn essential-transition
  [tr]
  (let [timed? (when-let [str (-> (filter #(= :timed (:tag %)) (:content tr)) first :content first :content first)]
                 (read-string str))]
    {:name (get-id tr)
     :tid (swap! +obj-cnt+ inc)
     :type (if timed? :exponential :immediate)
     :rate (get-rate tr)}))

(defn essential-arc
  [ar]
  {:aid (swap! +obj-cnt+ inc)
   :source (-> ar :attrs :source keyword)
   :target (-> ar :attrs :target keyword)
   :name (keyword (str "aa-" @+obj-cnt+)) ; POD cheezy but validate-pn checks it. 
   :type (as-> ar ?m
           (:content ?m)
           (some #(when (= (:tag %) :type) %) ?m)
           (:attrs ?m)
           (:value ?m)
           (keyword ?m))
   :multiplicity (get-multiplicity ar)})

(defn read-pnml
  "Return a map providing the useful elements of a PNML file.
  'useful' here means things used in steady-state computation."
  [fname]
  (reset! +obj-cnt+ 0)
  (as-> {:raw (-> fname slurp xml/parse-str :content first :content)} ?m
    (assoc ?m :places (filter #(= :place (:tag %)) (:raw ?m)))
    (assoc ?m :places (vec (map essential-place (:places ?m))))
    (assoc ?m :transitions (filter #(= :transition (:tag %)) (:raw ?m)))
    (assoc ?m :transitions (vec (map essential-transition (:transitions ?m))))
    (assoc ?m :arcs (filter #(= :arc (:tag %)) (:raw ?m)))
    (assoc ?m :arcs (vec (map essential-arc (:arcs ?m))))
    (dissoc ?m :raw)))

(defn reorder-places
  "Reorder and renumber the places for easier comparison with textbook models."
  [pn order]
  (as-> pn ?pn
    (update ?pn :places
            (fn [places]
              (vec
               (sort #(< (:pid %1) (:pid %2))
                     (map #(assoc % :pid (inc (.indexOf order (:name %)))) places)))))
    (assoc ?pn :marking-key order)
    (assoc ?pn :initial-marking (vec (map :initial-marking (:places ?pn))))))
    
;;;=================================================
;;;  PN ==> PNML
;;;=================================================
(def +next-trans-pos+ (atom nil))
(def +next-place-pos+ (atom nil))
(def +given-pos+ (atom nil))

(declare pn2xml place2xml transition2xml arc2xml)
(defn write-pnml [pn & {:keys [file positions] :or {file "./data/foo.xml"}}]
  (reset! +next-trans-pos+ {:x 0.0 :y 400.0})
  (reset! +next-place-pos+ {:x 0.0 :y 20.0})
  (reset! +given-pos+ (or positions {}))
  (let [xml (pn2xml pn)] 
    (with-open [writer (java.io.FileWriter. file)]
      (xml/emit xml writer)))
  true)

(defn pn2xml
  [pn]
  (xml/element
   :pnml {}
   (xml/element
    :net {:id "Net-POD" :type "P/T net"}
    (as-> [] ?xml
      (conj ?xml (xml/element :token {:id "Default" :enabled "true" :red "0" :green "0" :blue "0"}))
      (into ?xml (vec (map place2xml (:places pn))))
      (into ?xml (vec (map transition2xml (:transitions pn))))
      (into ?xml (vec (map arc2xml (:arcs pn))))))))

;;; The position of elements can be established by looking at 
;;; a file you want you PN to look like.
(defn pos!-or-given
  "If the position of this element is provided in +given-pos+ return that;
   otherwise update the running position values and return that."
  [name & trans?]
  (if-let [pos (name @+given-pos+)]
    pos
    (if trans?
      (swap! +next-trans-pos+ #(hash-map :x (+ (:x %)  80.0) :y 400))
      (swap! +next-place-pos+ #(hash-map :x (+ (:x %) 110.0) :y 20)))))

(defn update-pos!
  [elem pos]
  (when-not (:status pos)
    (swap! +given-pos+
           #(assoc % (:name elem)
                   (-> pos
                       (assoc :label-x-off 20.0)
                       (assoc :label-y-off 5.0))))))

(defn place2xml
  [pl & {:keys [pos] :or {pos (pos!-or-given (:name pl))}}]
  "Serialize a place. Optional pos is {:x <x-pos> :y <y-pos>}."
  (update-pos! pl pos)
  (xml/element
   :place {:id (name (:name pl))}
   (xml/element :graphics {}
                (xml/element :position {:x (:x pos) :y (:y pos)}))
   (xml/element :name {}
                (xml/element :value {} (str (name (:name pl))))
                (xml/element :graphics {}
                             (xml/element :offset {:x (or (:label-x-off pos) 20.0)
                                                   :y (or (:label-y-off pos) 5.0)})))
   (xml/element :initialMarking {}
                (xml/element :value {} (str "Default," (:initial-marking pl)))
                (xml/element :graphics {}
                             (xml/element :offset {:x 0.0 :y 0.0})))
   (xml/element :capacity {}
                (xml/element :value {} "0"))))

(defn transition2xml
  [tr & {:keys [pos] :or {pos (pos!-or-given (:name tr) :trans? true)}}]
  (update-pos! tr pos)
  (xml/element
   :transition {:id (name (:name tr))}
   (xml/element :graphics {}
                (xml/element :position {:x (:x pos) :y (:y pos)}))
   (xml/element :name {}
                (xml/element :value {} (str (name (:name tr))))
                (xml/element :graphics {}
                             (xml/element :offset {:x (or (:label-x-off pos) 20.0)
                                                   :y (or (:label-y-off pos) 5.0)})))
   (xml/element :orientation {}
                (xml/element :value {} "90"))
   (xml/element :rate {}
                (xml/element :value {} (:rate tr)))
   (xml/element :timed {}
                (xml/element :value {} (if (= (:type tr) :immediate) "false" "true")))
   (xml/element :infiniteServer {}
                (xml/element :value {} "false"))
   (xml/element :priority {}
                (xml/element :value {} 1))))

(defn arc2xml
  [ar]
  (xml/element
   :arc {:id (str (name (:source ar)) " to " (name (:target ar)))
         :source (name (:source ar))
         :target (name (:target ar))}
   (xml/element :graphics {}) ; there are in the Pipe files.
   (xml/element :inscription {}
                (xml/element :value {} (str "Default," (:multiplicity ar)))
                (xml/element :graphics {}))
   (xml/element :tagged {}                
                (xml/element :value {} "false"))
   (xml/element :arcpath {:id "000"
                          :x (int (:x (pos!-or-given (:source ar))))
                          :y (int (:y (pos!-or-given (:source ar))))
                          :curvePoint "false"})
   (xml/element :arcpath {:id "001"
                          :x (int (:x (pos!-or-given (:target ar))))
                          :y (int (:y (pos!-or-given (:target ar))))
                          :curvePoint "false"})
   (xml/element :type {:value (name (:type ar))})))

(defn positions-from-file
  "Read the positions of elements from the argument file, creating a map of them."
  [fname]
  (as-> {:raw (-> fname slurp xml/parse-str :content first :content)} ?m
    (assoc ?m :elems (filter #(or (= (:tag %) :place) (= (:tag %) :transition)) (:raw ?m)))
    (dissoc ?m :raw)
    (reduce (fn [m elem] (assoc m (get-id elem) (get-pos elem)))
            ?m
            (:elems ?m))
    (dissoc ?m :elems)))

