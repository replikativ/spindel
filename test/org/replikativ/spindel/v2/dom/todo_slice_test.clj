(ns org.replikativ.spindel.v2.dom.todo-slice-test
  "The todo vertical slice on the JVM (phase-d design §6, acceptance
   A1-A8): a todo app rendered with `render!` into the mock discharge, on an
   inline world and on `{:inline? false :budget 8}`, in verify mode with the
   Rule R hook and check-writes.

   Steps: s0 mount; s1 add 1; s2 add 2; s3 toggle 1; s4 mode :active; s5
   mode :all; s6 reverse; s6b insert 3 at the head (A7's extra step); s7
   remove 2; s8 unmount. Each step waits until the committed vdom is the
   root's value (§5.3).

   A2 runs the same steps on the old engine (old namespaces, its
   MockDischarge) and compares the normalized operation logs step by step."
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.v2.core :as v2 :refer [spin track]]
            [org.replikativ.spindel.v2.rows :as rw]
            [org.replikativ.spindel.incremental.interval :as iv]
            [org.replikativ.spindel.v2.incremental :as ic]
            [org.replikativ.spindel.v2.dom.elements :as el]
            [org.replikativ.spindel.v2.dom.foreach :refer [ifor-each]]
            [org.replikativ.spindel.v2.dom.render :as render]
            [org.replikativ.spindel.v2.dom.mock :as mock]
            [org.replikativ.spindel.v2.dom.render-fixture :as fx]
            [org.replikativ.spindel.dom.ssr :as ssr]
            ;; the old engine, for the differential (A2)
            [org.replikativ.spindel.dom.elements :as oel]
            [org.replikativ.spindel.dom.foreach :as ofe]
            [org.replikativ.spindel.dom.render :as orender]
            [org.replikativ.spindel.dom.discharge :as disch]
            [org.replikativ.spindel.incremental.combinators :as oic]
            [org.replikativ.spindel.signal :as osig]
            [org.replikativ.spindel.effects.track :as otrack]
            [org.replikativ.spindel.spin.cps :as ocps]
            [org.replikativ.spindel.test-helpers :refer [with-ctx]]
            [org.replikativ.spindel.test-async :refer [await-drain]]))

;; ---------------------------------------------------------------------------
;; The app, v2

(defn todo-item [t]
  (el/li {:class (if (:done t) "done" "pending")}
         (el/span {:class "text"} (:text t))
         (el/button {:class "toggle"} (if (:done t) "Undo" "Done"))))

(defn app
  "`runs`, `item-runs`: clojure.core atoms counting root and item runs."
  [todos mode runs item-runs]
  (spin (let [tiv (track todos)
              m (iv/get-new (track mode))
              _ (swap! runs inc)                ; after the tracks: a T11 resume re-executes it
              all (iv/get-new tiv)
              visible (if (= m :active) (ic/ifilter (complement :done) tiv) tiv)]
          (el/div {:class "todo-app"}
                  (el/h1 "Todos")
                  (el/span {:class "count"} (str (count (remove :done all)) " left"))
                  (el/ul {:class "list"}
                         (ifor-each :id visible
                                    (fn [t] (swap! item-runs update (:id t) (fnil inc 0)) (todo-item t))))))))

;; ---------------------------------------------------------------------------
;; The app, old engine: the item root carries the :key the old ifor-each needs

(defn old-todo-item [t]
  (oel/li {:key (:id t) :class (if (:done t) "done" "pending")}
          (oel/span {:class "text"} (:text t))
          (oel/button {:class "toggle"} (if (:done t) "Undo" "Done"))))

(defn old-app [todos mode]
  (ocps/spin (let [tiv (otrack/track todos)
                   m (iv/get-new (otrack/track mode))
                   all (iv/get-new tiv)
                   visible (if (= m :active) (oic/ifilter (complement :done) tiv) tiv)]
               (oel/div {:class "todo-app"}
                        (oel/h1 "Todos")
                        (oel/span {:class "count"} (str (count (remove :done all)) " left"))
                        (oel/ul {:class "list"}
                                (ofe/ifor-each :id visible (fn [t] (old-todo-item t))))))))

;; ---------------------------------------------------------------------------
;; Steps

(def ^:private todo-a {:id 1 :text "a" :done false})
(def ^:private todo-b {:id 2 :text "b" :done false})
(def ^:private todo-c {:id 3 :text "c" :done false})

(def ^:private steps
  "[step [kind arg]]: a write to the todos or the mode, or the unmount."
  [[:s1 [:todos #(conj % todo-a)]]
   [:s2 [:todos #(conj % todo-b)]]
   [:s3 [:todos (fn [ts] (mapv #(if (= 1 (:id %)) (update % :done not) %) ts))]]
   [:s4 [:mode :active]]
   [:s5 [:mode :all]]
   [:s6 [:todos #(vec (rseq %))]]
   [:s6b [:todos #(into [todo-c] %)]]
   [:s7 [:todos (fn [ts] (filterv #(not= 2 (:id %)) ts))]]])

;; ---------------------------------------------------------------------------
;; Operation logs, normalized for the differential

(defn- normalize
  "Element and text ids renamed to first-seen ordinals (`ids` an atom map,
   shared across the steps of one run), function values as :fn; the v2
   mock's address fields and the operations on the container (the old
   render with no container makes none) dropped."
  [ids ops]
  (let [id (fn [x] (if (symbol? x)
                     (or (get @ids x) (get (swap! ids assoc x [:n (count @ids)]) x))
                     x))]
    (into []
          (comp (remove #(or (= :clear-container (:op %)) (= :container (:parent %))))
                (map #(dissoc % :addr :child-addr :child-tag))
                (map (fn [op] (into {} (map (fn [[k v]]
                                              [k (cond (symbol? v) (id v)
                                                       (or (fn? v) (= ::mock/fn v)) :fn
                                                       :else v)]))
                                    op))))
          ops)))

(defn- take-ops!
  "The operations logged since the last take, and empties the log."
  [log]
  (let [[old _] (reset-vals! log [])] old))

;; ---------------------------------------------------------------------------
;; The v2 run

(defn- step!
  "Settles, then checks that the committed vdom is the root's value."
  [env root state]
  (fx/settle! env)
  (let [v (fx/read! env root)]
    (is (identical? v (render/committed state)) "the step's commit is the root's value")
    v))

(defn- census
  "Row counts by type, after collection (the census gate)."
  [env]
  (dotimes [_ 3] (System/gc) (Thread/sleep 20))
  (fx/call! env #(v2/call-in! (:w env) (fn [] nil)))
  (Thread/sleep 20)
  (fx/call! env #(v2/call-in! (:w env) (fn [] (frequencies (map (fn [r] (aget ^objects r rw/TYPE))
                                                                (vals (aget ^objects (:w env) rw/W-REG))))))))

(defn- v2-run
  "Runs every step; returns {:steps [{:step :ops :ssr :runs :item-runs}] ...}
   with the control object, the census after unmount and the leftovers."
  [env]
  (let [w (:w env)
        log (:log (:mock env))
        todos (v2/signal [])
        mode (v2/signal :all)
        runs (atom 0)
        item-runs (atom {})
        root (atom (app todos mode runs item-runs))
        ctl (fx/render! env @root)
        state (:state ctl)
        record (fn [step]
                 {:step step
                  :ops (take-ops! log)
                  :ssr (ssr/render-to-string (step! env @root state))
                  :runs @runs
                  :item-runs @item-runs})
        recorded (loop [out [(record :s0)] vs {:todos [] :mode :all} [[step [k f]] & more] steps]
                   (if-not step
                     out
                     (let [v (if (= k :todos) (f (:todos vs)) f)]
                       (fx/write! env (if (= k :todos) todos mode) v)
                       (recur (conj out (record step)) (assoc vs k v) more))))]
    (fx/unmount! env ctl)
    (let [s8-ops (take-ops! log)]
      (reset! root nil)
      {:steps recorded
       :s8-ops s8-ops
       :ctl ctl
       :sources [todos mode]                ; the host holds them through the census
       :census (census env)
       :idle? (fx/call! env #(v2/idle? w))
       :leftovers (fx/leftovers env state)
       :violations (fx/violations)})))

;; ---------------------------------------------------------------------------
;; The old run

(defn- old-run
  "The old engine's normalized operation log per step (s0-s7)."
  []
  (with-ctx [rt]
    (let [{:keys [discharge log]} (disch/make-mock-discharge)
          ids (atom {})
          todos (osig/signal [])
          mode (osig/signal :all)
          app-spin (old-app todos mode)
          _ (orender/render-spin! nil app-spin discharge)
          _ @app-spin
          _ (await-drain rt)
          s0 {:step :s0 :ops (normalize ids (take-ops! log))}]
      (loop [out [s0] [[step [k f]] & more] steps]
        (if-not step
          out
          (do (if (= k :todos) (swap! todos f) (reset! mode f))
              (await-drain rt)
              (recur (conj out {:step step :ops (normalize ids (take-ops! log))}) more)))))))

;; ---------------------------------------------------------------------------
;; Facts

(defn- by-step [run] (into {} (map (juxt :step identity)) (:steps run)))

(defn- created-tags [ops] (into [] (comp (filter #(= :create-element (:op %))) (map :tag)) ops))

(defn- ops-of [ops kind] (filterv #(= kind (:op %)) ops))

(defn- ul-id
  "The id of the list element, from the mount's operations."
  [s0-ops]
  (:id (first (filter #(and (= :create-element (:op %)) (= :ul (:tag %))) s0-ops))))

(defn- li-id-of-item
  "The id of the li created for the first item (s1)."
  [s1-ops]
  (:id (first (filter #(and (= :create-element (:op %)) (= :li (:tag %))) s1-ops))))

(defn- run-delta [st prev]
  {:root (- (:runs st) (:runs prev))
   :items (into {} (keep (fn [[k n]] (let [d (- n (get (:item-runs prev) k 0))] (when (pos? d) [k d]))))
                (:item-runs st))})

(deftest the-todo-slice
  (fx/each-world
   (fn [env]
     (let [run (v2-run env)
           st (by-step run)
           s0-ops (:ops (st :s0))
           ul (ul-id s0-ops)]
       (testing "A1 SSR"
         (is (= "<div class=\"todo-app\"><h1>Todos</h1><span class=\"count\">0 left</span><ul class=\"list\"></ul></div>"
                (:ssr (st :s0))))
         (is (= (str "<div class=\"todo-app\"><h1>Todos</h1><span class=\"count\">1 left</span>"
                     "<ul class=\"list\"><li class=\"pending\"><span class=\"text\">a</span>"
                     "<button class=\"toggle\">Done</button></li></ul></div>")
                (:ssr (st :s1)))))
       (testing "A3 op facts"
         (let [s1 (:ops (st :s1))]
           (is (= 1 (count (filter #(= ul (:parent %)) (ops-of s1 :insert-child)))) "s1: one insert into the ul")
           (is (= [:li :span :button] (created-tags s1)) "s1: the created tags"))
         (let [s3 (:ops (st :s3))
               li (li-id-of-item (:ops (st :s1)))]
           (is (empty? (ops-of s3 :create-element)) "s3: nothing created")
           (is (some #(and (= li (:el %)) (= :class (:attr %)) (= "done" (:value %))) (ops-of s3 :set-attr))
               "s3: the li gets class done"))
         (let [s4 (:ops (st :s4))]
           (is (= 1 (count (filter #(= ul (:parent %)) (ops-of s4 :remove-child)))) "s4: one remove from the ul"))
         (let [s6 (:ops (st :s6))]
           (is (empty? (ops-of s6 :create-element)) "s6: nothing created")
           (is (empty? (ops-of s6 :remove-child)) "s6: nothing removed")))
       (testing "A4 rows after unmount and dropping the root"
         (let [c (:census run)]
           (is (zero? (get c rw/T-RUN 0)) (str "runs " c))
           (is (zero? (get c rw/T-EDGE 0)) (str "edges " c))
           (is (zero? (get c rw/T-COMP 0)) (str "computations " c))
           (is (= 2 (get c rw/T-SOURCE 0)) "todos and mode, held by the host"))
         (is (true? (:idle? run))))
       (testing "A5 host state, the control object kept"
         (let [state (:state (:ctl run))]
           (is (= :unmounted (render/phase state)))
           (is (nil? (render/committed state)))
           (is (= [:clear-container] (mapv :op (:s8-ops run))) "s8: the unmount clears the container")
           (is (empty? (:leftovers run)) (str (:leftovers run)))
           (is (= [] (:violations run)))))
       (testing "A7 render counts"
         (is (= {:root 1 :items {1 1}} (run-delta (st :s3) (st :s2))) "s3: root +1, item 1 +1, item 2 +0")
         (is (= {} (:items (run-delta (st :s6) (st :s5)))) "s6 reverse: no item runs")
         (is (= {3 1} (:items (run-delta (st :s6b) (st :s6)))) "insert at the head: one new item run"))))))

;; ---------------------------------------------------------------------------
;; A2: the differential against the old engine. s0-s7 are compared; s8 is
;; not: the old render has no unmount (its stop! cancels the spin and
;; writes nothing), so only the v2 side has operations there (A5).

(deftest a2-the-op-logs-match-the-old-engine
  (let [old-ops (into {} (map (juxt :step :ops)) (old-run))]
    (fx/each-world
     (fn [env]
       (let [ids (atom {})
             v2-ops (into {} (map (fn [s] [(:step s) (normalize ids (:ops s))])) (:steps (v2-run env)))]
         (doseq [step (into [:s0] (map first) steps)]
           (testing (name step)
             (is (= (old-ops step) (v2-ops step))))))))))

;; ---------------------------------------------------------------------------
;; A8: SSR from a fork of a warm world

(deftest a8-fork-ssr
  (fx/each-world
   (fn [env]
     (let [todos (v2/signal [])
           mode (v2/signal :all)
           root (app todos mode (atom 0) (atom {}))
           u (v2/observe! root (fn [_ _]))]
       (fx/write! env todos [todo-a])
       (fx/write! env todos [todo-a todo-b])
       (fx/read! env root)
       (let [before (census env)
             f (fx/call! env #(v2/fork! (:w env)))
             s (ssr/render-to-string (fx/read! env (v2/in-world f root)))]
         (fx/call! env #(v2/release-world! f))
         (is (fx/call! env #(v2/await-complete f fx/wait-ms false)) "the fork completes")
         (is (= (str "<div class=\"todo-app\"><h1>Todos</h1><span class=\"count\">2 left</span>"
                     "<ul class=\"list\">"
                     "<li class=\"pending\"><span class=\"text\">a</span><button class=\"toggle\">Done</button></li>"
                     "<li class=\"pending\"><span class=\"text\">b</span><button class=\"toggle\">Done</button></li>"
                     "</ul></div>")
                s))
         (is (= before (census env)) "the parent's census is unchanged"))
       (u)))))
