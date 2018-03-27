
{:initial-marking [1 0 0 0 0], ; All the :rep here are typed in. Might be okay!
   :transitions
   [{:name :m1-start-job,
     :tid 38,
     :type :exponential,
     :rate 1.0, 
     :rep {:clk 2028.5745 :act :m1-start-job :jt :jobType1 :m :m1 :ends 2030.0781 :mjpact :aj :j 1705 :line 101}
     :visible? true}
    {:name :m1-complete-job,
     :tid 39,
     :type :exponential,
     :rate 1.0,
     :rep {:clk 2030.0781 :act :m1-complete-job :m :m1 :bf :b1 :n 0 :mjpact :bj :j 1705 :line 106}
     :visible? true}
    {:name :m2-start-job,
     :tid 40,
     :type :exponential,
     :rate 1.0,
     :rep {:clk 2031.2184 :act :m2-start-job :m :m2 :bf :b1 :n 2 :mjpact :sm :j 1705 :line 111}
     :visible? true}
    {:name :m2-complete-job,
     :tid 41,
     :type :exponential,
     :rate 1.0,
     :rep {:clk 2032.3884 :act :m2-complete-job :m :m2 :ent 2028.5745 :mjpact :ej :j 1705 :line 112}
     :visible? true}],
   :arcs
   [{:aid 74, :source :place-1, :target :m2-start-job, :name :aa-74, :type :normal, :multiplicity 1, :bind {:jtype :blue}}
    {:aid 75, :source :m1-start-job, :target :place-2, :name :aa-75, :type :normal, :multiplicity 1, :bind {:jtype :blue}, :priority 1}
    {:aid 76, :source :place-2, :target :m1-complete-job, :name :aa-76, :type :normal, :multiplicity 1, :bind {:jtype :blue}}
    {:aid 77, :source :m1-complete-job, :target :place-3, :name :aa-77, :type :normal, :multiplicity 1, :bind {:jtype :blue}, :priority 1}
    {:aid 78, :source :place-3, :target :m1-start-job, :name :aa-78, :type :normal, :multiplicity 1, :bind {:jtype :blue}}
    {:aid 79, :source :m2-start-job, :target :place-4, :name :aa-79, :type :normal, :multiplicity 1, :bind {:jtype :blue}, :priority 1}
    {:aid 80, :source :place-4, :target :m2-complete-job, :name :aa-80, :type :normal, :multiplicity 1, :bind {:jtype :blue}}
    {:aid 81, :source :m2-complete-job, :target :place-1, :name :aa-81, :type :normal, :multiplicity 1, :bind {:jtype :blue}, :priority 1}
    {:aid 205, :source :m1-start-job, :target :Place-103, :name :aa-205, :type :normal, :multiplicity 1, :bind {:jtype :blue} :priority 2}
    {:aid 206, :source :Place-103, :target :m2-start-job, :name :aa-206, :type :normal, :multiplicity 1 :bind {:jtype :blue}, :priority 1}],
   :marking-key [:place-1 :place-2 :place-3 :place-4 :Place-103],
   :places
   [{:name :place-1, :pid 0, :initial-tokens 1, :visible? true}
    {:name :place-2, :pid 1, :initial-tokens 0, :visible? true}
    {:name :place-3, :pid 2, :initial-tokens 0, :visible? true}
    {:name :place-4, :pid 3, :initial-tokens 0, :visible? true}
    {:name :Place-103, :pid 4, :initial-tokens 0}]}
