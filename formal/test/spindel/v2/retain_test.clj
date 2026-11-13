(ns spindel.v2.retain-test
  "Loading spindel.v2.retain kernel-checks every theorem in it. The deftests run the compiled
  `live` / `rule-r-filter` on small and random worlds and compare them with a plain-Clojure
  BFS over the §3.2 edges (written independently below, from the reading documented in the
  retain ns docstring), and check I3 and idempotence of the filter at runtime."
  (:require [clojure.test :refer [deftest is testing]]
            [clojure.set :as set]
            [ansatz.core :as a]
            [spindel.v2.state :as s]
            [spindel.v2.retain :as r]))

(def theorems
  '[reach-frame reach-frame-roots reach-closure-frame reach-run-frame reach-closure-l-eq reach-run-l-eq
    reach-mem-nat-mem keep-find-in keep-find-out guard-keep gather-keep gather-mem scan-keep scan-mem
    any-keep-id keep-keep keep-all-ids gather-id-keep tbl-find-mem
    fw-scopes fw-runs fw-cleanup succ-of-scope succ-of-run succ-of-pub
    scope-contrib-agree run-contrib-agree comp-contrib-agree succ-filter-agree roots-filter
    in-live-iff live-filter-reach in-live-filter cleanup-filter storage-filter admitted-filter
    rule-r-filter-eq keep-of-live keep-filter all-ids-filter filter-filter
    rule-r-i3 rule-r-idem rule-r-live
    ;; P1: the live worklist always converges (live-converged stays a tripwire below)
    unseen-cost-mono unseen-cost-drop reach-closure-l-conv reach-run-l-conv
    gather-absent retain-succ-absent succ-all-length live-converged-all])

(deftest theorems-kernel-checked
  (doseq [t theorems]
    (is (some? (.lookup ^ansatz.kernel.Env @a/ansatz-env (ansatz.kernel.Name/fromString (str t))))
        (str t))))

;; ---------------------------------------------------------------------------
;; Plain-Clojure reference of §3.1/§3.2/§3.4 and the filter

(defn- nz [n] (if (zero? n) [] [n]))
(defn- rows-with [w k x] (filter #(= (:id %) x) (get w k)))
(defn- first-row [w k x] (first (rows-with w k x)))
(defn- alive? [run] (not= (:act run) s/act-done))

(defn ref-succ [w x]
  (concat
   (for [sc (rows-with w :scopes x)
         y (concat (nz (:parent sc))
                   (for [t (:tasks w)
                         :when (and (= (:owner t) x) (not= 0 (:run t))
                                    (some-> (first-row w :runs (:run t)) alive?))]
                     (:id t))
                   (for [f (:forks w) :when (= (:owner f) x)] (:id f)))]
     y)
   (for [c (rows-with w :comps x) :when (not (:idle c))
         y (concat (let [run (first-row w :runs (:run c))]
                     (when (and run (or (= (:epoch run) (:epoch c))
                                        (and (not= (:done-epoch c) (:epoch c)) (alive? run))))
                       [(:run c)]))
                   (for [e (:edges w) :when (and (= (:kind e) s/ek-dep) (= (:creditor e) x))] (:id e))
                   (map :id (:basis c))
                   (map :id (:adopt-basis c))
                   (map :source (:adopt-baselines c)))]
     y)
   (for [t (rows-with w :tasks x) y (nz (:run t))] y)
   (for [run (rows-with w :runs x) :when (alive? run)
         y (concat (nz (:scope run)) (nz (:of run))
                   (for [ac (:acts w) :when (= (:run ac) x)] (:id ac))
                   (:resources run)
                   (for [e (:edges w)
                         :when (and (= (:kind e) s/ek-savepoint)
                                    (some-> (first-row w :acts (:creditor e)) :run (= x)))]
                     (:id e)))]
     y)
   (for [ac (rows-with w :acts x) y (:members ac)] (:edge y))
   (for [e (rows-with w :edges x) y (nz (:debtor e))] y)
   (for [p (rows-with w :pubs x) y (nz (:edge p))] y)))

(defn ref-roots [w]
  (concat (for [sc (:scopes w) :when (= (:kind sc) s/scope-root)] (:id sc))   ; Z#56: also once released
          (:pins w)
          (for [e (:edges w) :when (or (= (:kind e) s/ek-observe)
                                       (and (= (:kind e) s/ek-wait) (= 0 (:creditor e))))] (:id e))
          (for [sc (:scopes w) :when (and (= (:kind sc) s/scope-explicit) (:open sc))] (:id sc))
          (nz (:pending-act w))
          (for [p (:pubs w)
                :when (and (pos? (:handles p)) (not= 0 (:edge p))
                           (some-> (first-row w :edges (:edge p)) :phase (= s/ph-armed)))]
            (:id p))))

(defn ref-live [w]
  (loop [seen #{} work (vec (ref-roots w))]
    (if-let [x (first work)]
      (if (seen x)
        (recur seen (subvec work 1))
        (recur (conj seen x) (into (subvec work 1) (ref-succ w x))))
      seen)))

;; Z#52: every retained row's current ancestors (parent links from the scope rows, cycle-safe;
;; none for an id that is not a scope)
(defn ref-ancestors [w s]
  (loop [x s acc []]
    (let [p (some-> (first-row w :scopes x) :parent)]
      (if (or (nil? p) (zero? p) (some #{p} acc)) acc (recur p (conj acc p))))))

(defn ref-keep [w]
  (let [lv (ref-live w)
        fin-refs (fn [run] (mapcat :refs (:finalizers run)))
        cl (set (for [c (:cleanup w)
                      x (concat [(:run c)] (:rows c)
                                (when-let [run (first-row w :runs (:run c))]
                                  (concat [(:scope run) (:of run)] (:resources run) (fin-refs run))))
                      y (cons x (ref-ancestors w x))]
                  y))
        st (set (for [run (:runs w) :when (lv (:id run)) y (fin-refs run)] y))
        adm (set (concat (for [c (:comps w) :when (and (or (:idle c) (zero? (:done-epoch c))) (pos? (:handles c)))] (:id c))
                         (for [x (:sources w) :when (pos? (:handles x))] (:id x))
                         (for [t (:tasks w) :when (and (not= s/res-none (:tag (:result t))) (pos? (:handles t)))] (:id t))
                         (for [p (:pubs w) :when (pos? (:handles p))] (:id p))))]
    (set/union lv cl st adm)))

(def tables [:scopes :comps :tasks :runs :sources :edges :acts :res :pubs :forks])

(defn ref-filter [w]
  (let [k (ref-keep w)]
    (reduce (fn [w t] (assoc w t (filter #(k (:id %)) (get w t)))) w tables)))

(defn ids [w] (set (mapcat #(map :id (get w %)) tables)))
(defn live-set [w] (set (:visited (r/live w))))
(defn keep-once
  "keep-fn w with live, cleanup rows and storage computed once (keep-fn recomputes them per id)."
  [w]
  (let [lv (r/live-list w) cl (r/cleanup-rows w) st (r/storage w)]
    (fn [y] (r/keep-with w lv cl st y))))
(defn i3? [w] (true? (s/tbl-all (keep-once w) (s/all-ids w))))
(defn same-world? [w1 w2] (every? #(= (seq (get w1 %)) (seq (get w2 %))) (conj tables :cleanup :pins)))

;; ---------------------------------------------------------------------------
;; Row constructors with defaults

(def nores (s/->RunResult s/res-none 0))
(def okres (s/->RunResult s/res-ok 7))
(defn scope [id parent kind open] (s/->ScopeRow id parent kind open))
(defn comp-row [m] (s/map->CompRow (merge {:id 0 :owner 0 :inputs [] :body 0 :run 0 :epoch 1 :done-epoch 0
                                            :pending 0 :rank 0 :version 0 :result nores :idle false
                                            :validity [] :basis [] :adopt-basis [] :adopt-baselines []
                                            :handles 0} m)))
(defn task [id owner run result handles] (s/->TaskRow id owner run result handles []))
(defn run-row [m] (s/map->RunRow (merge {:id 0 :of 0 :stamp 0 :epoch 1 :scope 0 :act s/act-active :mode 0
                                          :slice false :effect-index 0 :finalizers [] :resources []} m)))
(defn source [id owner handles] (s/->SourceRow id owner s/sk-signal 0 0 true handles []))
(defn edge [id kind creditor debtor] (s/->EdgeRow id kind creditor debtor s/cont-restart 0 s/ph-armed false false 0 false 0 0))
(defn act [id run members] (s/->ActRow id run s/am-one (vec (map-indexed (fn [i m] (s/->Member m i)) members)) [] (count members) 0 []))
(defn world [m] (s/map->World (merge {:scopes [] :comps [] :tasks [] :runs [] :sources [] :edges [] :acts []
                                       :res [] :cleanup [] :pubs [] :pins [] :forks [] :pending-act 0
                                       :released false :next-id 100} m)))

;; ---------------------------------------------------------------------------
;; A world with every row of §3.2 and §3.4

(def w1
  (world
   {:scopes [(scope 1 0 s/scope-root true)
             (scope 2 1 s/scope-explicit true)    ; open explicit: a root
             (scope 3 2 s/scope-explicit false)   ; closed: no downward edges, nothing keeps it
             (scope 6 1 s/scope-run true)         ; run scope of run 5
             (scope 20 1 s/scope-run false)]      ; run scope of the cancelled run 18
    :tasks [(task 4 1 5 nores 0)                  ; owned by the root scope, running
            (task 19 1 18 nores 0)]               ; its run 18 is done: not retained by the scope
    :runs [(run-row {:id 5 :of 4 :scope 6 :act s/act-parked
                     :finalizers [(s/->Finalizer 1 0 [34])]})   ; ref 34 (a source): storage only
           (run-row {:id 11 :of 10 :epoch 1 :act s/act-done})   ; current run of comp 10
           (run-row {:id 18 :of 19 :scope 20 :act s/act-done :resources [21]})
           (run-row {:id 23 :of 22 :epoch 1 :act s/act-parked}) ; stale, comp 22 needs a run
           (run-row {:id 26 :of 25 :epoch 1 :act s/act-parked})] ; stale, comp 25 settled
    :acts [(act 7 5 [8])]
    :edges [(edge 8 s/ek-wait 7 9)                ; parked run 5 waits on source 9
            (edge 12 s/ek-dep 10 13)              ; comp 10 tracks source 13
            (edge 15 s/ek-observe 0 10)           ; host observes comp 10: a root
            (edge 30 s/ek-savepoint 31 22)]       ; publication 29's armed edge (activation 31 gone)
    :sources [(source 9 6 0) (source 13 1 0) (source 27 1 1) (source 28 1 0) (source 34 1 0)]
    :comps [(comp-row {:id 10 :owner 1 :run 11 :epoch 1 :done-epoch 1 :result okres
                       :basis [(s/->Created 14 0)]})
            (comp-row {:id 14 :owner 10})                         ; created by comp 10's run
            (comp-row {:id 16 :idle true :done-epoch 1 :result okres :handles 1})
            (comp-row {:id 17 :idle true :done-epoch 1 :result okres :handles 0})
            (comp-row {:id 22 :run 23 :epoch 2 :done-epoch 1 :result okres})
            (comp-row {:id 25 :run 26 :epoch 2 :done-epoch 2 :result okres})]
    :res [(s/->ResRow 21 18 s/rk-timer 0 s/rp-cancelling)]
    :cleanup [(s/->CleanupRow 18 [20])]
    :pubs [(s/->PubRow 29 30 [] 1)]
    :forks [(s/->ForkRow 33 0 2)]
    :pins [22 25]}))

(deftest small-world-live
  (let [lv (live-set w1)]
    (is (true? (r/live-converged w1)))
    (is (= (ref-live w1) lv))
    (testing "roots: root scope, pins, observe edge, open explicit scope, armed publication"
      (is (= #{1 22 25 15 2 29} (set (r/roots w1)))))
    (testing "scope tree upwards only; a running owned task; its run, scope, activation, wait edge, source"
      (is (every? lv [1 2 4 5 6 7 8 9]))
      (is (not (lv 3)) "closed explicit child: no downward scope edges"))
    (testing "a live computation: its current run, dep edge, debtor, basis"
      (is (every? lv [10 11 12 13 14])))
    (testing "stale runs: retained only while the computation needs a run"
      (is (lv 23))
      (is (not (lv 26))))
    (testing "fork marker of a live scope; the armed publication's edge"
      (is (every? lv [33 29 30])))
    (testing "not live: idle comps, the cancelled run and its rows, finalizer ref"
      (is (not-any? lv [16 17 18 19 20 21 27 28 34])))
    (is (= lv (set (filter #(r/in-live w1 %) (range 40)))))))

(deftest small-world-filter
  (let [w' (r/rule-r-filter w1)]
    (is (same-world? (ref-filter w1) w'))
    (is (= (set/difference (ids w1) #{3 17 26 28}) (ids w'))
        "removed: closed scope, idle comp at handles 0, settled comp's stale run, unreferenced source at 0")
    (testing "kept without being live"
      (is (every? (ids w') [16 27]) "admitted (§3.4)")
      (is (every? (ids w') [18 19 20 21]) "cleanup entry: run, rows, body entity, resources")
      (is (contains? (ids w') 34) "a running run's finalizer ref (storage)"))
    (is (true? (r/live-converged w')))
    (is (= (live-set w1) (live-set w')))
    (is (= w' (r/rule-r-filter w')) "idempotent")
    (is (i3? w') "I3")))

(deftest released-world
  (let [w (assoc w1 :released true :pins [] :edges (remove #(= s/ek-observe (:kind %)) (:edges w1)))
        lv (live-set w)]
    (is (= (ref-live w) lv))
    (is (= #{1 2 29} (set (r/roots w))) "Z#56: the root scope stays a root once released")
    (is (lv 1))
    (is (lv 4) "its running task is still owned by a live scope")
    (is (= (ref-filter w) (r/rule-r-filter w)) "filter")))

;; ---------------------------------------------------------------------------
;; v1.5.1 changes (Z#2, Z#4)

(def w2
  (world
   {:scopes [(scope 1 0 s/scope-root true)
             (scope 42 1 s/scope-run true)]       ; run scope of the loop task's run 41
    :tasks [(task 40 1 41 nores 0)                ; a loop task, running
            (task 45 42 46 nores 0)               ; child it awaits (wait edge 44)
            (task 47 42 48 okres 0)               ; finished child, run retired, no handle
            (task 49 42 52 okres 1)               ; finished child the body still holds
            (task 50 42 51 nores 0)               ; running child
            (task 70 0 72 nores 0)]               ; publisher, detached: only its publication keeps it
    :runs [(run-row {:id 41 :of 40 :scope 42 :act s/act-parked})
           (run-row {:id 46 :of 45 :act s/act-parked})
           (run-row {:id 51 :of 50 :act s/act-active})
           (run-row {:id 72 :of 70 :act s/act-parked})]
    :acts [(act 43 41 [44]) (act 73 72 [74])]
    :edges [(edge 44 s/ek-wait 43 45)
            (edge 74 s/ek-savepoint 73 70)]
    :comps [(comp-row {:id 60 :owner 42 :handles 1})                    ; fresh, held by a handle
            (comp-row {:id 61 :owner 42 :handles 0})                    ; fresh, no handle
            (comp-row {:id 62 :owner 42 :done-epoch 1 :result okres :handles 1})] ; settled, undemanded
    :pubs [(s/->PubRow 75 74 [] 1)]}))

(deftest loop-task-children
  (let [lv (live-set w2) w' (r/rule-r-filter w2)]
    (is (= (ref-live w2) lv))
    (is (same-world? (ref-filter w2) w'))
    (is (every? lv [40 41 42 43 44 45 46 50 51]) "the loop, its awaited child, its running child")
    (is (not-any? lv [47 49 60 61 62]) "Z#2: the run keeps no reason for its creations")
    (is (not (contains? (ids w') 47)) "a finished child without a handle goes")
    (is (contains? (ids w') 49) "a finished child with a handle is admitted")
    (is (i3? w'))
    (is (same-world? w' (r/rule-r-filter w')))))

(deftest fresh-computation-with-handle
  (let [w' (r/rule-r-filter w2)]
    (is (contains? (ids w') 60) "fresh, handles > 0: admitted (Z#2)")
    (is (not (contains? (ids w') 61)) "fresh, handles = 0: removed")
    (is (not (contains? (ids w') 62)) "settled, not idle, undemanded: not admitted (demotion is normalization)")
    (is (r/admitted w2 60))
    (is (not (r/admitted w2 62)))))

(deftest armed-publication-keeps-publisher
  (let [lv (live-set w2)]
    (is (contains? (set (r/roots w2)) 75) "Z#4: handles > 0 and an armed edge")
    (is (every? lv [75 74 70 72 73]) "publication -> edge -> debtor (the publisher) -> its run")
    (testing "fired edge: not a root; the publication is only admitted"
      (let [w (update w2 :edges (fn [es] (map #(if (= 74 (:id %)) (assoc % :phase s/ph-fired) %) es)))
            lv (live-set w) w' (r/rule-r-filter w)]
        (is (= (ref-live w) lv))
        (is (not (contains? (set (r/roots w)) 75)))
        (is (not-any? lv [75 74 70 72 73]))
        (is (contains? (ids w') 75))
        (is (not (contains? (ids w') 72)))
        (is (same-world? (ref-filter w) w'))))
    (testing "no handle: not a root"
      (let [w (assoc w2 :pubs [(s/->PubRow 75 74 [] 0)])]
        (is (not (contains? (set (r/roots w)) 75)))
        (is (not ((live-set w) 72)))))))

;; ---------------------------------------------------------------------------
;; Random worlds

(defn- random-world [^java.util.Random rng]
  (let [n (+ 4 (.nextInt rng 30))
        pick (fn [] (inc (.nextInt rng (+ n 2))))        ; occasionally dangling
        pick0 (fn [] (if (zero? (.nextInt rng 4)) 0 (pick)))
        pickb (fn [] (zero? (.nextInt rng 2)))
        some-ids (fn [] (vec (repeatedly (.nextInt rng 3) pick)))
        rows (group-by first (for [id (range 1 (inc n))] [(.nextInt rng 10) id]))
        ids-of (fn [k] (map second (get rows k)))]
    (world
     {:scopes (for [id (ids-of 0)] (scope id (pick0) (.nextInt rng 3) (pickb)))
      :comps (for [id (ids-of 1)]
               (comp-row {:id id :owner (pick0) :run (pick0) :epoch (inc (.nextInt rng 2))
                          :done-epoch (.nextInt rng 3) :idle (pickb) :handles (.nextInt rng 2)
                          :basis (mapv #(s/->Created % 0) (some-ids))
                          :adopt-basis (mapv #(s/->Created % 0) (some-ids))
                          :adopt-baselines (mapv #(s/->AdoptBase 0 % 0 0) (some-ids))}))
      :tasks (for [id (ids-of 2)]
               (task id (pick0) (pick0) (if (pickb) nores okres) (.nextInt rng 2)))
      :runs (for [id (ids-of 3)]
              (run-row {:id id :of (pick0) :scope (pick0) :epoch (inc (.nextInt rng 2)) :act (.nextInt rng 3)
                        :resources (some-ids)
                        :finalizers (if (pickb) [] [(s/->Finalizer 1 0 (some-ids))])}))
      :sources (for [id (ids-of 4)] (source id (pick0) (.nextInt rng 2)))
      :edges (for [id (ids-of 5)] (assoc (edge id (.nextInt rng 4) (pick0) (pick0)) :phase (.nextInt rng 2)))
      :acts (for [id (ids-of 6)] (act id (pick0) (some-ids)))
      :res (for [id (ids-of 7)] (s/->ResRow id (pick0) s/rk-timer 0 s/rp-armed))
      :pubs (for [id (ids-of 8)] (s/->PubRow id (pick0) [] (.nextInt rng 2)))
      :forks (for [id (ids-of 9)] (s/->ForkRow id 0 (pick0)))
      :cleanup (for [run (take (.nextInt rng 2) (shuffle (ids-of 3)))] (s/->CleanupRow run (some-ids)))
      :pins (some-ids)
      :pending-act (pick0)
      :released (zero? (.nextInt rng 5))
      :next-id (+ n 1)})))

(deftest random-worlds
  (let [rng (java.util.Random. 20261103)]
    (dotimes [i 150]
      (let [w (random-world rng)
            w' (r/rule-r-filter w)]
        (is (true? (r/live-converged w)) (str "converged " i))
        (is (= (ref-live w) (live-set w)) (str "live " i))
        (is (same-world? (ref-filter w) w') (str "filter " i))
        (is (true? (r/live-converged w')) (str "converged after filter " i))
        (is (= (live-set w) (live-set w')) (str "live stable " i))
        (is (i3? w') (str "I3 " i))
        (is (same-world? w' (r/rule-r-filter w')) (str "idempotent " i))))))
