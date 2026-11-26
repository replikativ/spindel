(ns org.replikativ.spindel.v2.dom.budget-render-test
  "R-CLJS (sol T6, phase-d design §5.4): a render whose work exceeds the
   turn budget. With `{:budget 8}` a 100-item list does not finish within
   the operation that starts it: the rest is handed off, and the commit
   arrives in a later macrotask (on the JVM: once the test runs the handed
   off work). The revision waiter sees it, and nothing is stranded: the
   committed tree is complete and the world is idle afterwards."
  (:refer-clojure :exclude [await])
  (:require #?(:clj [clojure.test :refer [deftest is testing]]
               :cljs [cljs.test :refer-macros [deftest is testing async]])
            [org.replikativ.spindel.v2.core :as v2 :refer [spin track]]
            [org.replikativ.spindel.v2.dom.elements :as el]
            [org.replikativ.spindel.v2.dom.foreach :refer [ifor-each]]
            [org.replikativ.spindel.v2.dom.render :as render]
            [org.replikativ.spindel.v2.dom.mock :as mock]
            [org.replikativ.spindel.v2.dom.render-fixture :as fx]))

(defn- in-world
  "Calls `(f env done)` with a fresh world made with `opts` bound. JVM: a
   manual executor, so handed off work runs only when `(:settle! env)`
   runs it. The test ends at `(done)` or at the deadline; either way the
   fns the test put in `(:cleanups env)` run (an unmount), then the world
   is released."
  [opts f]
  #?(:clj (let [[ex q] (fx/manual-executor)
                w (v2/world (assoc opts :executor ex))
                cleanups (atom [])
                p (promise)]
            (try (binding [v2/*world* w] (f {:w w :settle! #(fx/pump! q) :cleanups cleanups} #(deliver p true)))
                 (is (true? (deref p fx/wait-ms false)) "the test completes")
                 (finally
                   (doseq [c @cleanups] (c))
                   (v2/release-world! w)
                   (fx/pump! q))))
     :cljs (async done*
                  (let [w (v2/world opts)
                        cleanups (atom [])
                        done (fx/guard-done (fn []
                                              (doseq [c @cleanups] (c))
                                              (v2/release-world! w)
                                              (js/setTimeout done* 0)))]
                    (binding [v2/*world* w]
                      (f {:w w :settle! (constantly 0) :cleanups cleanups} done))))))

(defn- on-revision
  "Calls `(k x)` once the mount's revision reaches `n`, `x` the waiter's
   answer. JVM: runs the handed off work first."
  [env state n k]
  #?(:clj ((:settle! env)))
  (render/on-revision state n k))

(defn- later
  "Runs `f` after the current macrotask (JVM: at once, the work is run)."
  [f]
  #?(:clj (f) :cljs (js/setTimeout f 0)))

(defn- items [n] (mapv (fn [i] {:id i :v (str "item " i)}) (range n)))

(defn- lis [m] (mock/children (:discharge m) (first (mock/children (:discharge m) :container))))

(deftest r-cljs-a-commit-past-the-budget-arrives-later
  (in-world {:budget 8}
            (fn [env done]
              (let [m (mock/make-mock)
                    xs (v2/signal (items 100))
                    root (spin (el/ul (ifor-each :id (track xs) (fn [x] (el/li (:v x))))))
                    {:keys [state unmount!]} (render/render! :container root (:discharge m))]
                (swap! (:cleanups env) conj unmount!)
                (is (= 0 (render/revision state)) "100 items do not fit 8 units: no commit yet")
                (on-revision env state 1
                             (fn [x]
                               (is (= :ok x))
                               (later
                                (fn []
                                  (is (= 100 (count (lis m))) "the whole list is committed")
                                  (v2/write! xs (vec (reverse (items 100))))
                                  (is (= 1 (render/revision state)) "the reversal does not fit either")
                                  (on-revision env state 2
                                               (fn [x]
                                                 (is (= :ok x))
                                                 (later
                                                  (fn []
                                                    (is (= [:li {} "item 99"] (first (mock/dom (:discharge m) (first (mock/children (:discharge m) :container))))))
                                                    (is (= 100 (count (lis m))))
                                                    (is (= 2 (render/revision state)) "one commit for the write")
                                                    (is (empty? (:waiters @(:rev @state))) "no waiter left")
                                                    (is (v2/idle? (:w env)) "nothing stranded: the world is idle")
                                                    (unmount!)
                                                    #?(:clj ((:settle! env)))
                                                    (is (= :unmounted (render/phase state)))
                                                    (done)))))))))))))
