(ns gov.nist.spntools.util.pnml
  (:require [clojure.data.xml :as xml :refer (parse-str)]
            [clojure.pprint :refer (cl-format pprint)]
            [gov.nist.spntools.util.utils :refer :all]))

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

(defn get-pos [elem]
  (let [elem (-> elem :content first :content first :attrs)]
    (hash-map :x (read-string (:x elem))
              :y (read-string (:y elem)))))


(def +pid-cnt+ (atom 0))
(def +tid-cnt+ (atom 0))
(def +aid-cnt+ (atom 0))

(defn essential-place
  [pl]
  (let [mark (get-initial-marking pl)]
    {:name (get-id pl)
     :pid (swap! +pid-cnt+ inc)
     :initial-marking mark}))

(defn get-rate [tr]
    (when-let [str (-> (filter #(= :rate (:tag %)) (:content tr)) first :content first :content first)]
      (read-string str)))

(defn essential-transition
  [tr]
  (let [timed? (when-let [str (-> (filter #(= :timed (:tag %)) (:content tr)) first :content first :content first)]
                 (read-string str))]
    {:name (get-id tr)
     :tid (swap! +tid-cnt+ inc)
     :type (if timed? :exponential :immediate)
     :rate (get-rate tr)}))

(defn essential-arc
  [ar]
  {:aid (swap! +aid-cnt+ inc)
   :source (-> ar :attrs :source keyword)
   :target (-> ar :attrs :target keyword)
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
(def ^:dynamic *place-pos* (atom {:x 0.0 :y 20.0}))
(def ^:dynamic *trans-pos* (atom {:x 0.0 :y 400.0}))
(def ^:dynamic *elem-pos* (atom {}))

(declare position-from-file)
(defn write-pnml [pn & {:keys [file position-file] :or {file "./data/foo.xml"}}]
  ;;(binding [*place-pos* (atom {:x 0.0 :y 20.0})
  ;;          *trans-pos* (atom {:x 0.0 :y 400.0})
  ;;          *elem-pos* (atom {})]
  (when position-file (reset! *elem-pos* (position-from-file position-file)))
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
(defn elem-pos!
  "If the position of this element is already established (perhaps through
   the *elem-pos* map made from reading another file) return that. Otherwise
   use a new position."
  [elem]
  (if-let [pos ((:name elem) @*elem-pos*)]
    pos
    (if (:pid elem)
      (swap! *place-pos* #(hash-map :x (+ (:x %)  80.0) :y (:y %)))
      (swap! *place-pos* #(hash-map :x (+ (:x %) 110.0) :y (:y %))))))

(defn update-pos!
  [elem pos]
  (when-not (:status pos)
    (swap! *elem-pos* #(assoc % (:name elem) pos))))

(defn place2xml
  [pl & {:keys [pos] :or {pos (elem-pos! pl)}}]
  "Serialize a place. Optional pos is {:x <x-pos> :y <y-pos>}."
  (update-pos! pl pos)
  (xml/element
   :place {:id (strip-name (:name pl))}
   (xml/element :graphics {}
                (xml/element :position {:x (:x pos) :y (:y pos)}))
   (xml/element :name {}
                (xml/element :value {} (str (strip-name (:name pl))))
                (xml/element :graphics {}
                             (xml/element :offset {:x 27 :y -9})))
   (xml/element :initialMarking {}
                (xml/element :value {} (str "Default," (:initial-marking pl)))
                (xml/element :graphics {}
                             (xml/element :offset {:x 0.0 :y 0.0})))
   (xml/element :capacity {}
                (xml/element :value {} "0"))))

(defn transition2xml
  [tr & {:keys [pos] :or {pos (elem-pos! tr)}}]
  (update-pos! tr pos)
  (xml/element
   :transition {:id (strip-name (:name tr))}
   (xml/element :graphics {}
                (xml/element :position {:x (:x pos) :y (:y pos)}))
   (xml/element :name {}
                (xml/element :value {} (str (strip-name (:name tr))))
                (xml/element :graphics {}
                             (xml/element :offset {:x 27 :y -9})))
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
   :arc {:id (str (strip-name (:source ar)) " to " (strip-name (:target ar)))
         :source (strip-name (:source ar))
         :target (strip-name (:target ar))}
   (xml/element :graphics {}) ; there are in the Pipe files.
   (xml/element :inscription {}
                (xml/element :value {} (str "Default," (:multiplicity ar)))
                (xml/element :graphics {}))
   (xml/element :tagged {}                
                (xml/element :value {}))
   (xml/element :arcpath {:id "000"
                          :x (:x (get @*elem-pos* (:source ar)))
                          :y (:y (get @*elem-pos* (:source ar)))})
   (xml/element :arcpath {:id "001"
                          :x (:x (get @*elem-pos* (:target ar)))
                          :y (:y (get @*elem-pos* (:target ar)))})
   (xml/element :type {:value (strip-name (:type ar))})))

(defn position-from-file
  "Read the positions of elements from the argument file, creating a map of them."
  [fname]
  (as-> {:raw (-> fname slurp xml/parse-str :content first :content)} ?m
    (assoc ?m :elems (filter #(or (= (:tag %) :place) (= (:tag %) :transition)) (:raw ?m)))
    (dissoc ?m :raw)
    (reduce (fn [m elem] (assoc m (get-id elem) (get-pos elem)))
            ?m
            (:elems ?m))
    (dissoc ?m :elems)))

