(ns org.replikativ.spindel.v2.dom.commit-effects-test
  "Commit effects (C1, phase-d addendum §3.8.2-§3.8.6, tests CE1-CE24):
   `:ref` is the lifetime hook (read only when its element is created),
   `:on-commit` runs synchronously after the commit's refs, and
   `:on-commit-deferred` in a later flush the discharge defers (the mock
   runs it on `run-deferred!`). Each may return a cleanup. Cleanups run in
   passes, newest first by setup history: one pass per removed subtree, in
   walk order, while it is attached; one for the hooks that re-run. A hook
   re-runs when the fn committed at its address is not identical to the
   last one. A stop or unmount asked for by a setup or cleanup waits until
   that call returns; an unmount stops the remaining setups.

   On the JVM every case runs on an inline and on a non-inline world
   (render-fixture); on CLJS on an inline world."
  (:refer-clojure :exclude [await])
  (:require #?(:clj [clojure.test :refer [deftest is testing]]
               :cljs [cljs.test :refer-macros [deftest is testing]])
            [org.replikativ.spindel.v2.core :as v2 :refer [spin track await]]
            [org.replikativ.spindel.incremental.interval :as iv]
            [org.replikativ.spindel.v2.dom.elements :as el]
            [org.replikativ.spindel.v2.dom.render :as render]
            [org.replikativ.spindel.v2.dom.mock :as mock]
            [org.replikativ.spindel.v2.dom.render-fixture :as fx]
            [org.replikativ.spindel.dom.fragment :as frag]))

(def ^:private kinds [:ref :on-commit :on-commit-deferred])

(def ^:private short-kind {:ref :ref :on-commit :oc :on-commit-deferred :def})

(defn- ctx [env]
  {:log (atom []) :detached (atom []) :d (:discharge (:mock env))})

(defn- hooks
  "Attrs with the three hooks of element `tag`, fresh closures: a setup
   logs [kind tag :setup] and returns a cleanup that logs [kind tag
   :cleanup] and records itself in :detached when its element is no longer
   attached. `extra` maps a kind (or [kind :cleanup]) to a fn the setup
   (cleanup) calls after logging."
  ([c tag] (hooks c tag {}))
  ([{:keys [log detached d]} tag extra]
   (into {} (for [k kinds]
              [k (fn [el]
                   (swap! log conj [(short-kind k) tag :setup])
                   (when-let [f (get extra k)] (f el))
                   (fn []
                     (swap! log conj [(short-kind k) tag :cleanup])
                     (when-not (mock/attached? d :container el)
                       (swap! detached conj [(short-kind k) tag]))
                     (when-let [f (get extra [k :cleanup])] (f))))]))))

;; Element macros take only a literal map as attrs, so the trees below write
;; {:ref (:ref h) :on-commit (:on-commit h) :on-commit-deferred
;; (:on-commit-deferred h)} for a hooks map `h`.

(defn- tree
  "The fixture of §3.8.12: a section W (no hooks) holding, while `show` is
   true (always without it), P with children A and B. B is its own
   computation; its hooks (tag :B<x>) are built after it reads `sb`. With
   `gate`, the root first awaits it, so the test holds the control map
   before the first commit. `extra` maps a tag (:P :A :B) to `hooks`'s
   extra."
  [c {:keys [sb show gate extra]}]
  (spin (when gate (await gate))
        (el/section
         (when (if show (iv/get-new (track show)) true)
           (let [hp (hooks c :P (:P extra))
                 ha (hooks c :A (:A extra))]
             (el/div {:ref (:ref hp) :on-commit (:on-commit hp) :on-commit-deferred (:on-commit-deferred hp)}
                     (el/div {:ref (:ref ha) :on-commit (:on-commit ha) :on-commit-deferred (:on-commit-deferred ha)} "a")
                     (await (spin (let [x (iv/get-new (track sb))
                                        hb (hooks c (keyword (str "B" x)) (:B extra))]
                                    (el/div {:ref (:ref hb) :on-commit (:on-commit hb) :on-commit-deferred (:on-commit-deferred hb)} (str x)))))))))))

(defn- mark [c] (count @(:log c)))
(defn- since [c n] (subvec @(:log c) n))

(defn- balanced?
  "The closing check: every logged setup has exactly one logged cleanup,
   except the setups in `failed` (they threw), and no cleanup ran on a
   detached element."
  ([c] (balanced? c #{}))
  ([c failed]
   (let [l @(:log c)
         count-of (fn [phase] (frequencies (map #(subvec % 0 2) (filter #(= phase (nth % 2)) l))))]
     (and (= (apply dissoc (count-of :setup) failed) (count-of :cleanup))
          (empty? @(:detached c))))))

(defn- errors
  "The kinds of the integrity violations collected since the last drain."
  []
  (mapv :kind (fx/violations)))

(defn- mount
  "Renders `(tree c opts)` and returns [c state ctl]; with a :gate, opens it
   after storing the control map in (:ctl opts), a volatile."
  [env opts]
  (let [c (or (:c opts) (ctx env))
        {:keys [state] :as ctl} (fx/render! env (tree c opts))]
    (when-let [v (:ctl opts)] (vreset! v ctl))
    (when-let [g (:gate opts)] (v2/deliver! g true) (fx/settle! env))
    [c state ctl]))

(def ^:private initial-sync
  [[:ref :A :setup] [:ref :B0 :setup] [:ref :P :setup]
   [:oc :A :setup] [:oc :B0 :setup] [:oc :P :setup]])

(def ^:private initial-deferred
  [[:def :A :setup] [:def :B0 :setup] [:def :P :setup]])

;; ---------------------------------------------------------------------------
;; CE1-CE4

(deftest ce1-initial-mount
  (fx/each-world
   (fn [env]
     (let [sb (v2/signal 0)
           [c state ctl] (mount env {:sb sb})]
       (is (= initial-sync @(:log c)) "refs, then on-commit, post-order")
       (is (= 1 (mock/deferred-count (:d c))) "one deferred flush is scheduled")
       (let [n (mark c)]
         (fx/run-deferred! env)
         (is (= initial-deferred (since c n))))
       (fx/unmount! env ctl)
       (is (balanced? c))
       (is (empty? (fx/leftovers env state)))))))

(deftest ce2-a-rerun-of-b
  (fx/each-world
   (fn [env]
     (let [sb (v2/signal 0)
           [c state ctl] (mount env {:sb sb})
           _ (fx/run-deferred! env)
           n (mark c)
           m (count @(:log (:mock env)))]
       (fx/write! env sb 1)
       (is (= [[:def :B0 :cleanup] [:oc :B0 :cleanup] [:oc :B1 :setup]] (since c n))
           "the cleanups newest first, then the new setup; no ref; nothing for A or P")
       (is (= #{:create-text :replace-child} (set (map :op (subvec @(:log (:mock env)) m))))
           "the DOM writes replace the text only")
       (let [n (mark c)]
         (fx/run-deferred! env)
         (is (= [[:def :B1 :setup]] (since c n))))
       (fx/unmount! env ctl)
       (is (balanced? c))
       (is (empty? (fx/leftovers env state)))))))

(deftest ce3-an-unrelated-rerun-runs-no-effect
  (fx/each-world
   (fn [env]
     (let [sb (v2/signal 0)
           u (v2/signal 0)
           other (spin (inc (iv/get-new (track u))))
           _ (v2/observe! other (fn [_ _]))
           [c state ctl] (mount env {:sb sb})
           _ (fx/run-deferred! env)
           n (mark c)]
       (fx/write! env u 1)
       (fx/run-deferred! env)
       (is (= [] (since c n)))
       (is (= 1 (render/revision state)))
       (fx/unmount! env ctl)
       (is (balanced? c))))))

(deftest ce4-a-removed-subtree-is-one-pass-newest-first
  (fx/each-world
   (fn [env]
     (let [sb (v2/signal 0)
           show (v2/signal true)
           [c state ctl] (mount env {:sb sb :show show})
           _ (fx/run-deferred! env)
           n (mark c)]
       (fx/write! env show false)
       (is (= [[:def :P :cleanup] [:def :B0 :cleanup] [:def :A :cleanup]
               [:oc :P :cleanup] [:oc :B0 :cleanup] [:oc :A :cleanup]
               [:ref :P :cleanup] [:ref :B0 :cleanup] [:ref :A :cleanup]]
              (since c n)))
       (is (empty? @(:detached c)) "each cleanup ran while its element was attached")
       (is (empty? (render/ledger state)))
       (fx/unmount! env ctl)
       (is (balanced? c))))))

;; ---------------------------------------------------------------------------
;; CE5, CE6: element replacement and :ref cleanups

(deftest ce5-a-tag-change-at-one-address
  (fx/each-world
   (fn [env]
     (let [c (ctx env)
           tag (v2/signal :div)
           root (spin (let [t (iv/get-new (track tag))]
                        (let [h (hooks c t)]
                          (el/section (el/element t {:ref (:ref h) :on-commit (:on-commit h) :on-commit-deferred (:on-commit-deferred h)} "x")))))
           {:keys [state] :as ctl} (fx/render! env root)
           _ (fx/run-deferred! env)
           addr (:addr (first (:children (render/committed state))))
           n (mark c)]
       (fx/write! env tag :span)
       (is (= addr (:addr (first (:children (render/committed state))))) "the same address")
       (is (= [[:def :div :cleanup] [:oc :div :cleanup] [:ref :div :cleanup]
               [:ref :span :setup] [:oc :span :setup]]
              (since c n))
           "every old claim before any new setup")
       (fx/run-deferred! env)
       (fx/unmount! env ctl)
       (is (balanced? c))))))

(deftest ce6-ref-cleanups
  (fx/each-world
   (fn [env]
     (let [s (v2/signal 1)
           show (v2/signal true)
           seen (atom [])
           root (spin (let [v (iv/get-new (track s))
                            sh (iv/get-new (track show))]
                        (el/section
                         (when sh (el/div {:ref (fn [el] (swap! seen conj [:plain v (some? el)]))} "n"))
                         (when sh (el/p {:ref (fn [_] (swap! seen conj [:returns v])
                                                #(swap! seen conj [:cleanup v]))}
                                        "r")))))
           {:keys [state] :as ctl} (fx/render! env root)]
       (fx/write! env s 2)
       (is (= [[:plain 1 true] [:returns 1]] @seen) "a surviving element's ref is not re-run")
       (fx/write! env show false)
       (is (= [[:plain 1 true] [:returns 1] [:plain 1 false] [:cleanup 1]] @seen)
           "(f nil) with the f that ran; a returned cleanup replaces it")
       (fx/unmount! env ctl)
       (is (empty? (fx/leftovers env state)))))))

;; ---------------------------------------------------------------------------
;; CE7, CE8: requests from on-commit setups

(deftest ce7-unmount-from-an-on-commit-setup
  (fx/each-world
   (fn [env]
     (let [ctl (volatile! nil)
           [c state] (mount env {:sb (v2/signal 0) :gate (v2/deferred) :ctl ctl
                                 :extra {:A {:on-commit (fn [_] ((:unmount! @ctl)))}}})]
       (fx/run-deferred! env)
       (is (= :unmounted (render/phase state)))
       (is (= [[:ref :A :setup] [:ref :B0 :setup] [:ref :P :setup] [:oc :A :setup]
               [:oc :A :cleanup] [:ref :P :cleanup] [:ref :B0 :cleanup] [:ref :A :cleanup]]
              @(:log c))
           "B's and P's on-commit and every deferred setup never run; the teardown claims the rest")
       (is (balanced? c))
       (is (empty? (fx/leftovers env state)))))))

(deftest ce8-stop-from-an-on-commit-setup
  (fx/each-world
   (fn [env]
     (let [ctl (volatile! nil)
           sb (v2/signal 0)
           [c state] (mount env {:sb sb :gate (v2/deferred) :ctl ctl
                                 :extra {:A {:on-commit (fn [_] ((:stop! @ctl)))}}})]
       (is (= initial-sync @(:log c)) "everything runs")
       (is (= :stopped (render/phase state)))
       (fx/run-deferred! env)
       (is (= (into initial-sync initial-deferred) @(:log c)) "the pending deferred flush still runs")
       (fx/write! env sb 1)
       (is (= 1 (render/revision state)) "no later commit")
       (fx/unmount! env @ctl)
       (is (balanced? c))
       (is (empty? (fx/leftovers env state)))))))

;; ---------------------------------------------------------------------------
;; CE9: a DOM failure in a commit that also removes a subtree

(deftest ce9-a-dom-failure
  (fx/each-world
   (fn [env]
     (let [c (ctx env)
           ph (v2/signal 1)
           root (spin (let [p (iv/get-new (track ph))]
                        (let [hx (hooks c :X) hq (hooks c :Q) hy (hooks c :Y)]
                          (el/section (when (= p 1) (el/div {:ref (:ref hx) :on-commit (:on-commit hx) :on-commit-deferred (:on-commit-deferred hx)} "x"))
                                      (el/div {:ref (:ref hq) :on-commit (:on-commit hq) :on-commit-deferred (:on-commit-deferred hq)} "q")
                                      (when (= p 2) (el/article {:ref (:ref hy) :on-commit (:on-commit hy) :on-commit-deferred (:on-commit-deferred hy)} "y"))))))
           {:keys [state] :as ctl} (fx/render! env root)
           _ (fx/run-deferred! env)
           n (mark c)]
       (mock/fail-when! (:d c) (fn [op] (and (= :insert-child (:op op)) (= :article (:child-tag op)))))
       (fx/write! env ph 2)
       (is (= :failed (render/phase state)))
       (is (= [[:def :X :cleanup] [:oc :X :cleanup] [:ref :X :cleanup]
               [:def :Q :cleanup] [:oc :Q :cleanup] [:ref :Q :cleanup]]
              (since c n))
           "X's pass ran before the throw; no new setup; the failure pass claims the rest once")
       (is (empty? (render/ledger state)))
       (fx/run-deferred! env)
       (is (not-any? #(= :Y (second %)) @(:log c)) "no setup of the failed commit ran")
       (mock/fail-when! (:d c) nil)
       (fx/write! env ph 3)
       (is (= :mounted (render/phase state)) "the next delivery remounts")
       (is (= [[:ref :Q :setup] [:oc :Q :setup]] (subvec (since c n) 6)))
       (fx/run-deferred! env)
       (fx/unmount! env ctl)
       (is (balanced? c))
       (is (empty? (fx/leftovers env state)))))))

;; ---------------------------------------------------------------------------
;; CE10: effects that throw

(deftest ce10-throwing-setups-and-cleanups
  (fx/each-world
   (fn [env]
     (let [_ (fx/violations)
           [c state ctl] (mount env {:sb (v2/signal 0)
                                     :extra {:A {:on-commit (fn [_] (throw (ex-info "setup" {})))}
                                             :B {[:ref :cleanup] (fn [] (throw (ex-info "cleanup" {})))}}})]
       (is (= [:effect-error] (errors)) "one effect error")
       (is (= initial-sync @(:log c)) "the other setups ran")
       (is (= :mounted (render/phase state)))
       (is (nil? (get-in (render/ledger state) [(-> (render/committed state) :children first :children first :addr) :on-commit]))
           "no claim for the throwing setup")
       (fx/run-deferred! env)
       (fx/unmount! env ctl)
       (is (= [:effect-error] (errors)) "the throwing cleanup is reported")
       (is (balanced? c #{[:oc :A]}) "the rest of the pass ran")
       (is (empty? (fx/leftovers env state)))))))

;; ---------------------------------------------------------------------------
;; CE11, CE12: effects that write

(deftest ce11-an-effect-write-gives-one-follow-up-commit
  (doseq [kind [:on-commit :on-commit-deferred]]
    (testing kind
      (fx/each-world
       (fn [env]
         (let [s (v2/signal 0)
               gate (v2/deferred)
               state (volatile! nil)
               nested (atom [])
               wrote (atom false)
               root (spin (await gate)
                          (let [x (iv/get-new (track s))]
                            (el/div {kind (fn [_]
                                            (when (compare-and-set! wrote false true)
                                              (let [r (render/revision @state)]
                                                (v2/write! s 1)
                                                (swap! nested conj (not= r (render/revision @state))))))}
                                    (str x))))
               ctl (fx/render! env root)]
           (vreset! state (:state ctl))
           (v2/deliver! gate true)
           (fx/settle! env)
           (when (= kind :on-commit-deferred)
             (is (= 1 (render/revision @state)))
             (fx/run-deferred! env))
           (is (= 2 (render/revision @state)) "exactly one follow-up commit")
           (is (= [false] @nested) "never nested in the effect")
           (is (= [[:div {} "1"]] (mock/dom (:discharge (:mock env)) :container)))
           (fx/run-deferred! env)
           (fx/unmount! env ctl)))))))

#?(:clj
   (deftest ce12-a-cross-world-write
     (fx/each-world
      (fn [env]
        (let [w2 (v2/world {})
              o (v2/signal w2 0)
              _ (fx/violations)
              root (spin (el/div {:on-commit (fn [_]
                                               (v2/send-world! w2 #(v2/write! o 5))
                                               (swap! o inc))}
                                 "x"))
              ctl (fx/render! env root)]
          (is (= [:effect-error] (errors)) "swap! on another world inside the gate is reported (B7)")
          (is (loop [i 0] (cond (= 5 (v2/value o 1000 ::t)) true
                                (< i 200) (do (Thread/sleep 5) (recur (inc i)))
                                :else false))
              "send-world! works")
          (fx/unmount! env ctl)
          (v2/release-world! w2))))))

;; ---------------------------------------------------------------------------
;; CE13-CE14b: the deferred queue

(deftest ce13-a-superseded-deferred-setup-never-runs
  (fx/each-world
   (fn [env]
     (let [sb (v2/signal 0)
           show (v2/signal true)
           [c state ctl] (mount env {:sb sb :show show})
           _ (fx/run-deferred! env)
           n (mark c)]
       (fx/write! env sb 1)
       (fx/write! env sb 2)
       (fx/run-deferred! env)
       (is (= [[:def :B2 :setup]] (filterv #(= [:def :setup] [(first %) (nth % 2)]) (since c n)))
           "only the newest runs")
       (let [n (mark c)]
         (fx/write! env sb 3)
         (fx/write! env show false)
         (fx/run-deferred! env)
         (is (not-any? #(= [:def :setup] [(first %) (nth % 2)]) (since c n)) "removed before: none runs"))
       (fx/unmount! env ctl)
       (is (balanced? c))))))

(deftest ce14-deferred-setups-after-unmount
  (fx/each-world
   (fn [env]
     (let [[c state ctl] (mount env {:sb (v2/signal 0)})]
       (fx/unmount! env ctl)
       (fx/run-deferred! env)
       (is (not-any? #(= :def (first %)) @(:log c)) "nothing runs")
       (is (balanced? c))
       (is (empty? (fx/leftovers env state)))))))

(deftest ce14b-a-replaced-deferred-entry-moves-to-the-end
  (fx/each-world
   (fn [env]
     (let [sb (v2/signal 0)
           [c state ctl] (mount env {:sb sb})
           n (mark c)]
       (fx/write! env sb 1)
       (let [n (+ n 2)]
         (fx/run-deferred! env)
         (is (= [[:def :A :setup] [:def :P :setup] [:def :B1 :setup]] (since c n))))
       (fx/unmount! env ctl)
       (is (balanced? c))))))

;; ---------------------------------------------------------------------------
;; CE15-CE17: requests during deferred flushes, cleanups and throwing setups

(deftest ce15-unmount-during-a-deferred-setup
  (fx/each-world
   (fn [env]
     (let [ctl (volatile! nil)
           [c state] (mount env {:sb (v2/signal 0) :gate (v2/deferred) :ctl ctl
                                 :extra {:A {:on-commit-deferred (fn [_] ((:unmount! @ctl)))}}})
           n (mark c)]
       (fx/run-deferred! env)
       (is (= [[:def :A :setup]
               [:def :A :cleanup] [:oc :P :cleanup] [:oc :B0 :cleanup] [:oc :A :cleanup]
               [:ref :P :cleanup] [:ref :B0 :cleanup] [:ref :A :cleanup]]
              (since c n))
           "its cleanup is registered and claimed by the teardown; later deferred setups do not run")
       (is (= :unmounted (render/phase state)))
       (is (balanced? c))))))

(defn- deferred-requests
  "A mount whose deferred setups of A, B and P call the given requests."
  [env reqs]
  (let [ctl (volatile! nil)
        call (fn [req] (fn [_] (doseq [r req] ((get @ctl r)))))
        [c state] (mount env {:sb (v2/signal 0) :gate (v2/deferred) :ctl ctl
                              :extra (into {} (map (fn [[tag req]] [tag {:on-commit-deferred (call req)}])) reqs)})]
    (fx/run-deferred! env)
    [c state @ctl]))

(deftest ce16-the-deferred-flush-epilogue-takes-the-request
  (fx/each-world
   (fn [env]
     (testing "(a) the last deferred setup stops the mount"
       (let [[c state ctl] (deferred-requests env {:P [:stop!]})]
         (is (= :stopped (render/phase state)))
         (is (nil? (:request @state)) "the slot is empty")
         (fx/unmount! env ctl)
         (is (balanced? c))))
     (testing "(b) a stop, then a later unmount: the unmount wins"
       (let [[c state] (deferred-requests env {:A [:stop!] :B [:unmount!]})]
         (is (= :unmounted (render/phase state)))
         (is (not-any? #(= [:def :P :setup] %) @(:log c)))
         (is (balanced? c))))
     (testing "(c) an unmount, then a stop: unmounted"
       (let [[c state] (deferred-requests env {:A [:unmount! :stop!]})]
         (is (= :unmounted (render/phase state)))
         (is (balanced? c))))
     (testing "(d) a flush whose queue was emptied by a removal"
       (let [show (v2/signal true)
             [c state ctl] (mount env {:sb (v2/signal 0) :show show})
             d0 (render/deferred-revision state)]
         (fx/write! env show false)
         (fx/run-deferred! env)
         (is (= (inc d0) (render/deferred-revision state)) "the flush ran and ended")
         (is (= :mounted (render/phase state)) "the phase is unchanged")
         (is (nil? (:request @state)))
         (fx/unmount! env ctl)
         (is (balanced? c)))))))

(deftest ce17-requests-from-cleanups-and-throwing-setups
  (fx/each-world
   (fn [env]
     (testing "a removal cleanup asks for an unmount: the commit finishes, then the teardown"
       (let [ctl (volatile! nil)
             show (v2/signal true)
             [c state] (mount env {:sb (v2/signal 0) :show show :gate (v2/deferred) :ctl ctl
                                   :extra {:A {[:on-commit :cleanup] #((:unmount! @ctl))}}})]
         (fx/write! env show false)
         (is (= :unmounted (render/phase state)))
         (is (= 2 (render/revision state)) "the commit finished")
         (is (balanced? c))
         (is (empty? (fx/leftovers env state)))))
     (testing "a teardown cleanup asks for an unmount: nothing to do"
       (let [ctl (volatile! nil)
             [c state] (mount env {:sb (v2/signal 0) :gate (v2/deferred) :ctl ctl
                                   :extra {:A {[:ref :cleanup] #((:unmount! @ctl))}}})]
         (fx/unmount! env @ctl)
         (is (= :unmounted (render/phase state)))
         (is (balanced? c))))
     (doseq [[req ph] [[:unmount! :unmounted] [:stop! :stopped]]]
       (testing (str "the last deferred setup asks for " req " and throws")
         (let [ctl (volatile! nil)
               [c state] (mount env {:sb (v2/signal 0) :gate (v2/deferred) :ctl ctl
                                     :extra {:P {:on-commit-deferred (fn [_] ((get @ctl req))
                                                                       (throw (ex-info "after the request" {})))}}})]
           (fx/run-deferred! env)
           (is (= ph (render/phase state)))
           (is (nil? (:request @state)) "the slot is empty")
           (is (nil? (get-in (render/ledger state) [(:addr (first (:children (render/committed state)))) :on-commit-deferred])))
           (when (= ph :stopped) (fx/unmount! env @ctl))
           (is (balanced? c #{[:def :P]}) "no claim for the throwing setup")
           (fx/violations)))))))

;; ---------------------------------------------------------------------------
;; CE18-CE21b: identity

(deftest ce18-hook-presence
  (fx/each-world
   (fn [env]
     (let [c (ctx env)
           has (v2/signal false)
           refd (v2/signal true)
           show (v2/signal true)
           root (spin (let [h (iv/get-new (track has))
                            r (iv/get-new (track refd))
                            sh (iv/get-new (track show))
                            hh (when h (hooks c :H))
                            hr (when r (hooks c :R))]
                        (el/section
                         (el/div {:on-commit (:on-commit hh) :on-commit-deferred (:on-commit-deferred hh)} "h")
                         (when sh (el/div {:ref (:ref hr)} "r")))))
           {:keys [state] :as ctl} (fx/render! env root)
           n (mark c)]
       (fx/write! env has true)
       (fx/run-deferred! env)
       (is (= [[:oc :H :setup] [:def :H :setup]] (since c n)) "an added hook runs")
       (let [n (mark c)]
         (fx/write! env has false)
         (is (= [[:def :H :cleanup] [:oc :H :cleanup]] (since c n)) "a removed hook is claimed"))
       (let [n (mark c)]
         (fx/write! env refd false)
         (is (= [] (since c n)) "a :ref removed from a surviving element keeps its entry")
         (fx/write! env show false)
         (is (= [[:ref :R :cleanup]] (since c n)) "claimed when the element goes"))
       (let [n (mark c)]
         (fx/write! env show true)
         (fx/write! env refd true)
         (is (= [] (since c n)) "a :ref added to a surviving element is ignored")
         (fx/write! env show false)
         (fx/write! env show true)
         (is (= [[:ref :R :setup]] (since c n)) "until the element is re-created"))
       (fx/unmount! env ctl)
       (is (balanced? c))))))

(deftest ce19-a-fn-in-the-kept-prefix-does-not-rerun
  (fx/each-world
   (fn [env]
     (let [s (v2/signal 1)
           runs (atom 0)
           root (spin (el/div {:on-commit (fn [_] (swap! runs inc) nil)} (str (iv/get-new (track s)))))
           ctl (fx/render! env root)]
       (fx/write! env s 2)
       (is (= [[:div {} "2"]] (mock/dom (:discharge (:mock env)) :container)) "the text changed")
       (is (= 1 @runs) "the hook did not re-run")
       (fx/unmount! env ctl)))))

(deftest ce20-a-fn-after-the-read-reruns-on-an-equal-write
  (fx/each-world
   (fn [env]
     (let [s (v2/signal 1)
           runs (atom 0)
           root (spin (let [t (iv/get-new (track s))]
                        (el/div {:on-commit (fn [_] (swap! runs inc) nil)} (str t))))
           {:keys [state] :as ctl} (fx/render! env root)
           m (count @(:log (:mock env)))]
       (fx/write! env s 1)
       (is (= 2 @runs) "an equal write still resumes the suffix, so the hook re-runs")
       (is (= 2 (render/revision state)))
       (is (= [] (subvec @(:log (:mock env)) m)) "an effect-only change writes nothing to the DOM")
       (fx/unmount! env ctl)))))

(def ^:private stable-runs (atom 0))

(defn- stable-hook [_] (swap! stable-runs inc) nil)

(deftest ce21-stable-hooks
  (fx/each-world
   (fn [env]
     (reset! stable-runs 0)
     (let [c (ctx env)
           s (v2/signal 1)
           t (v2/signal 1)
           root (spin (let [x (iv/get-new (track s))
                            y (iv/get-new (track t))]
                        (el/div {:id (str y) :on-commit stable-hook}
                                (str x)
                                (await (spin (let [h (hooks c :K)] (el/span {:ref (:ref h) :on-commit (:on-commit h) :on-commit-deferred (:on-commit-deferred h)} "k")))))))
           ctl (fx/render! env root)
           n (mark c)]
       (fx/run-deferred! env)
       (fx/write! env s 2)
       (fx/write! env t 2)
       (fx/run-deferred! env)
       (is (= 1 @stable-runs) "a defn hook never re-runs")
       (is (= [[:def :K :setup]] (since c n)) "an adopted child computation's hooks never re-run")
       (fx/unmount! env ctl)
       (is (balanced? c))))))

(deftest ce21b-a-failed-setup-is-retried-only-for-a-new-fn
  (fx/each-world
   (fn [env]
     (let [s (v2/signal 1)
           tries (atom 0)
           hook (atom (fn [_] (swap! tries inc) (throw (ex-info "no" {}))))
           root (spin (let [x (iv/get-new (track s))]
                        (el/div {:on-commit @hook} (str x))))
           ctl (fx/render! env root)]
       (is (= 1 @tries))
       (fx/write! env s 2)
       (is (= 1 @tries) "the identical fn is not retried")
       (reset! hook (fn [_] (swap! tries inc) nil))
       (fx/write! env s 3)
       (is (= 2 @tries) "a new fn is")
       (fx/violations)
       (fx/unmount! env ctl)))))

;; ---------------------------------------------------------------------------
;; CE22, CE23: pass order

(deftest ce22-removed-siblings-are-cleaned-in-walk-order
  (fx/each-world
   (fn [env]
     (let [c (ctx env)
           show (v2/signal true)
           root (spin (let [sh (iv/get-new (track show))]
                        (let [ha (hooks c :A) hb (hooks c :B)]
                          (el/section (when sh (el/div {:ref (:ref ha) :on-commit (:on-commit ha) :on-commit-deferred (:on-commit-deferred ha)} "a"))
                                      (when sh (el/div {:ref (:ref hb) :on-commit (:on-commit hb) :on-commit-deferred (:on-commit-deferred hb)} "b"))))))
           ctl (fx/render! env root)
           _ (fx/run-deferred! env)
           n (mark c)]
       (fx/write! env show false)
       (is (= [[:def :A :cleanup] [:oc :A :cleanup] [:ref :A :cleanup]
               [:def :B :cleanup] [:oc :B :cleanup] [:ref :B :cleanup]]
              (since c n))
           "A's pass, then B's pass")
       (fx/unmount! env ctl)
       (is (balanced? c))))))

(deftest ce23-history-over-tree-order
  (fx/each-world
   (fn [env]
     (let [sb (v2/signal 0)
           show (v2/signal true)
           [c state ctl] (mount env {:sb sb :show show})]
       (fx/run-deferred! env)
       (fx/write! env sb 1)
       (fx/run-deferred! env)
       (let [n (mark c)]
         (fx/write! env show false)
         (is (= [[:def :B1 :cleanup] [:oc :B1 :cleanup] [:def :P :cleanup] [:def :A :cleanup]
                 [:oc :P :cleanup] [:oc :A :cleanup]
                 [:ref :P :cleanup] [:ref :B0 :cleanup] [:ref :A :cleanup]]
                (since c n))
             "B's re-run on-commit is newer than P's, so it is claimed first"))
       (fx/unmount! env ctl)
       (is (balanced? c))))))

;; ---------------------------------------------------------------------------
;; CE24: an effect chain makes progress across turns

#?(:clj
   (deftest ce24-an-effect-chain-crosses-turns
     (fx/with-world
       {:inline? false :budget 8}
       (fn [env]
         (let [n 24
               v (v2/signal nil)
               node (fn node [i]
                      (el/div {:on-commit (fn [_] (when (< i n) (v2/write! v (node (inc i)))) nil)} (str i)))
               _ (v2/write! v (node 0))
               ctl (render/render! :container v (:discharge (:mock env)))
               turns (fx/pump! (:q env))]
           (is (= [[:div {} (str n)]] (mock/dom (:discharge (:mock env)) :container)) "the chain completes")
           (is (<= 3 turns) (str "it took " turns " turns"))
           (fx/unmount! env ctl))))))

;; ---------------------------------------------------------------------------
;; Mixed siblings (sol's P4 review): an element reconciled in place, a created
;; one and a keyed fragment with a surviving and a new item, in one commit

(deftest mixed-siblings-in-one-commit
  (fx/each-world
   (fn [env]
     (let [c (ctx env)
           step (v2/signal 0)
           item (fn [k] (let [h (hooks c k)] (el/li {:key k :ref (:ref h) :on-commit (:on-commit h)} (name k))))
           root (spin (let [s (iv/get-new (track step))
                            hp (hooks c :P) ha (hooks c :A) hc (hooks c :C)
                            ks (if (zero? s) [:K1] [:K1 :K2])]
                        (el/div {:ref (:ref hp) :on-commit (:on-commit hp)}
                                (el/div {:ref (:ref ha) :on-commit (:on-commit ha)} "a")
                                (when (pos? s) (el/p {:ref (:ref hc) :on-commit (:on-commit hc)} "c"))
                                (assoc (frag/keyed-fragment (mapv item ks) nil) :addr :frag-mixed :keys ks))))
           {:keys [state] :as ctl} (fx/render! env root)
           n (mark c)]
       (fx/write! env step 1)
       (is (= [[:oc :P :cleanup] [:oc :K1 :cleanup] [:oc :A :cleanup]
               [:ref :C :setup] [:ref :K2 :setup]
               [:oc :A :setup] [:oc :C :setup] [:oc :K2 :setup] [:oc :K1 :setup] [:oc :P :setup]]
              (since c n))
           (str "the re-run pass newest first; the refs of the created elements in creation order;"
                " on-commit as the walk leaves each element, slot by slot (a keyed slot's new items"
                " are created by its diff, before its surviving items are visited), the parent last"))
       (is (= [[:div {} [:div {} "a"] [:p {} "c"] [:li {} "K1"] [:li {} "K2"]]]
              (mock/dom (:d c) :container)))
       (fx/unmount! env ctl)
       (is (balanced? c))
       (is (empty? (fx/leftovers env state)))))))

;; ---------------------------------------------------------------------------
;; An unexpected exception of the deferred flush itself (not of a setup)

#?(:clj
   (deftest an-unexpected-deferred-flush-exception-still-takes-the-request
     (fx/each-world
      (fn [env]
        (let [ctl (volatile! nil)
              orig @#'render/register!
              [c state] (mount env {:sb (v2/signal 0) :gate (v2/deferred) :ctl ctl
                                    :extra {:A {:on-commit-deferred (fn [_] ((:unmount! @ctl)))}}})]
          (with-redefs-fn {#'render/register! (fn [m addr kind cleanup]
                                                (if (= kind :on-commit-deferred)
                                                  (throw (ex-info "an internal failure of the flush" {}))
                                                  (orig m addr kind cleanup)))}
            #(fx/run-deferred! env))
          (is (= :unmounted (render/phase state)) "the epilogue still tears down")
          (is (not (:busy @state)))
          (is (nil? (:request @state)))
          (is (balanced? c #{[:def :A]}))
          (fx/violations))))))
