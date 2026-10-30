(ns org.replikativ.spindel.engine.public-computation-test
  (:refer-clojure :exclude [await])
  (:require #?(:clj [clojure.test :refer [deftest is testing]]
               :cljs [cljs.test :refer-macros [deftest is testing]])
            [org.replikativ.spindel.engine.context :as context]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.protocols :as rtp]
            [org.replikativ.spindel.engine.impl.owned :as owned]
            [org.replikativ.spindel.engine.addressing :as address]
            [org.replikativ.spindel.engine.bindings :as bindings]
            [org.replikativ.spindel.engine.owned-runtime-test :refer [verify-boundaries!]]
            [org.replikativ.spindel.spin.core :as spin-core]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.effects.await :refer [await]]))

(defn- runtime [engine]
  (context/create-execution-context {:engine engine :audit? true}))

(defn- verify! [engine ctx]
  (if (= :owned engine)
    (verify-boundaries! ctx)
    (context/stop-context! ctx)))

(deftest public-spin-construction-invocation-and-cache-use-the-selected-engine
  (doseq [engine [:simple :owned]]
    (let [ctx (runtime engine) calls (atom 0) delivered (atom [])]
      (binding [ec/*execution-context* ctx]
        (let [task (spin (swap! calls inc) 42)]
          (is (zero? @calls) "Construction stays lazy")
          (is (= 42 (task #(swap! delivered conj %) #(throw %))))
          (is (= 42 (task #(swap! delivered conj %) #(throw %))))
          (is (= [42 42] @delivered))
          (is (= 1 @calls))
          (is (false? (spin-core/spin-failed? task)))
          (is (= {:variant :ok :payload 42 :clean? true}
                 (rtp/computation-result ctx task (spin-core/spin-id task))))))
      (verify! engine ctx))))

(deftest nil-and-false-remain-values-through-cold-and-cached-public-invocation
  (doseq [engine [:simple :owned] value [nil false]]
    (let [ctx (runtime engine) values (atom [])]
      (binding [ec/*execution-context* ctx]
        (let [task (spin value)]
          (is (= value (task #(swap! values conj %) #(throw %))))
          (is (= value (task #(swap! values conj %) #(throw %))))
          (is (= [value value] @values))))
      (verify! engine ctx))))

(deftest public-body-errors-preserve-rejection-identity-and-cached-error-convention
  (doseq [engine [:simple :owned]]
    (let [ctx (runtime engine) error (ex-info "body rejected" {}) errors (atom [])]
      (binding [ec/*execution-context* ctx]
        (let [task (spin (throw error))]
          (task (fn [_] (is false "A thrown body must reject")) #(swap! errors conj %))
          (is (identical? error (first @errors)))
          (is (true? (spin-core/spin-failed? task)))
          (is (identical? error
                          (try (task (fn [_]) #(swap! errors conj %)) nil
                               (catch #?(:clj Throwable :cljs :default) caught caught))))
          (is (= 2 (count @errors)))))
      (verify! engine ctx))))

(deftest real-public-parent-awaits-a-real-public-child
  (doseq [engine [:simple :owned] cached? [false true]]
    (let [ctx (runtime engine) calls (atom []) values (atom [])]
      (binding [ec/*execution-context* ctx]
        (let [child (spin (swap! calls conj :child) 7)
              parent (spin (swap! calls conj :parent) (+ 1 (await child)))]
          (when cached? (child (fn [_]) #(throw %)))
          (parent #(swap! values conj %) #(throw %))
          (is (= [8] @values))
          (is (= 1 (count (filter #{:child} @calls))))
          (is (= 1 (count (filter #{:parent} @calls))))))
      (verify! engine ctx))))

(deftest nested-public-construction-and-recur-await-stay-stack-safe
  (doseq [engine [:simple :owned]]
    (let [ctx (context/create-execution-context {:engine engine}) values (atom [])]
      (binding [ec/*execution-context* ctx]
        (let [parent (spin
                      (let [child (spin 2)]
                        (loop [i 0 total 0]
                          (if (= i 1000)
                            total
                            (recur (inc i) (+ total (await child)))))))]
          (parent #(swap! values conj %) #(throw %))
          (is (= [2000] @values))))
      (when (= :simple engine) (context/stop-context! ctx)))))

(defn- captured-public-spin [id value calls]
  (spin-core/make-spin (fn [resolve _]
                         (swap! calls inc)
                         (resolve value))
                       id {'value value}))

(deftest changed-public-constructor-captures-invalidate-lazily
  (doseq [engine [:simple :owned]]
    (let [ctx (runtime engine) calls (atom 0) values (atom [])]
      (binding [ec/*execution-context* ctx]
        (let [first-spin (captured-public-spin :same-template 1 calls)]
          (first-spin (fn [_]) #(throw %))
          (let [changed (captured-public-spin :same-template 2 calls)]
            (is (= 1 @calls) "New captures do not execute during construction")
            (changed #(swap! values conj %) #(throw %))
            (is (= [2] @values))
            (is (= 2 @calls)))))
      (verify! engine ctx))))

(deftest native-factory-rejects-legacy-storage-and-scheduler-options
  (doseq [option [{:executor nil} {:initial-state {}}]]
    (is (thrown? #?(:clj Exception :cljs js/Error)
                 (context/create-execution-context (assoc option :engine :owned)))))
  (is (thrown? #?(:clj Exception :cljs js/Error)
               (context/create-execution-context {:engine :unknown}))))

#?(:clj
   (deftest public-blocking-deref-uses-the-selected-engine
     (doseq [engine [:simple :owned]]
       (let [ctx (runtime engine)]
         (binding [ec/*execution-context* ctx]
           (is (= 42 @(spin 42)))
           (is (nil? @(spin nil)))
           (is (false? @(spin false))))
         (verify! engine ctx)))))

(bindings/register-spin-scope-key! :public-test/scope)

(defn- public-native-gate [id callbacks]
  ;; A public computation whose already-CPS body uses the native host adapter.
  ;; This does not claim Deferred/Mailbox migration or async resource joining.
  (spin-core/make-spin
   (fn [resolve reject]
     (owned/await-host-effect!
      (fn [resume fail] (reset! callbacks [resume fail]) nil)
      resolve reject))
   id {'callbacks callbacks}))

(deftest public-await-restores-constructor-and-suspension-scopes-on-the-selected-world
  (let [ctx (context/create-execution-context
             {:engine :owned :audit? true :bindings {:public-test/scope :base}})
        other (context/create-execution-context {:engine :owned})
        callbacks (atom nil) values (atom [])
        world (rtp/world-identity ctx)
        parent
        (binding [ec/*execution-context* (assoc ctx :bindings {:public-test/scope :construction})]
          (let [child (public-native-gate :delayed callbacks)]
            (spin
             [(get-in (ec/current-execution-context) [:bindings :public-test/scope])
              (address/with-key :during
                (let [value (await child)]
                  [value (address/current-key (ec/current-execution-context))
                   (get-in (ec/current-execution-context) [:bindings :public-test/scope])
                   (identical? world (rtp/world-identity (ec/current-execution-context)))]))
              (address/current-key (ec/current-execution-context))
              (get-in (ec/current-execution-context) [:bindings :public-test/scope])])))]
    (binding [ec/*execution-context* (assoc ctx :bindings {:public-test/scope :caller})]
      (is (= spin-core/incomplete (parent #(swap! values conj %) #(throw %)))))
    (is (empty? @values))
    (is (fn? (first @callbacks)))
    (binding [ec/*execution-context* other]
      ((first @callbacks) 9)
      (is (identical? other (ec/current-execution-context))))
    (is (= [[:construction [9 :during :construction true] nil :construction]] @values))
    (verify-boundaries! ctx)))

(deftest public-child-rejection-resumes-parent-catch-with-original-error
  (let [ctx (runtime :owned) callbacks (atom nil) values (atom [])
        error (ex-info "external failure" {})]
    (binding [ec/*execution-context* ctx]
      (let [child (public-native-gate :child callbacks)
            parent (spin (try (await child)
                              (catch #?(:clj Throwable :cljs :default) caught
                                (if (identical? error caught) :caught :wrong-error))))]
        (parent #(swap! values conj %) #(throw %))
        ((second @callbacks) error)
        (is (= [:caught] @values))
        (is (false? (spin-core/spin-failed? parent)))
        (is (true? (spin-core/spin-failed? child)))))
    (verify-boundaries! ctx)))

#?(:clj
   (do
     (defn- register-proxy-and-drop! [ctx child]
       (let [proxy (spin-core/with-causal-descendant-egress child)]
         ;; Typed root registration changes the descriptor baseline without
         ;; giving an awaiting parent ownership of the child's lifetime.
         (rtp/register-computation! ctx proxy (spin-core/spin-id proxy) (spin-core/spin-body proxy))
         (java.lang.ref.WeakReference. proxy)))

     (deftest collecting-an-egress-proxy-cannot-invalidate-a-retained-public-task
       (let [ctx (context/create-execution-context {:engine :owned}) calls (atom 0)]
         (binding [ec/*execution-context* ctx]
           (let [child (spin (swap! calls inc) 7)
                 _ (is (= 7 @child))
                 dropped (register-proxy-and-drop! ctx child)]
             (is (loop [remaining 100]
                   (cond
                     (nil? (.get ^java.lang.ref.WeakReference dropped)) true
                     (zero? remaining) false
                     :else (do (System/gc) (Thread/sleep 5) (recur (dec remaining)))))
                 "The proxy is no longer retained")
             (is (= 7 @child))
             (is (= 1 @calls) "GC must not turn a live unchanged cache into a body rerun")
             (java.lang.ref.Reference/reachabilityFence child)))
         (java.lang.ref.Reference/reachabilityFence ctx)))))

(deftest public-native-context-scope-survives-suspended-loop-recur-bounces
  (let [ctx (context/create-execution-context
             {:engine :owned :audit? true :bindings {:public-test/scope :base}})
        other (runtime :owned) callbacks (atom nil) values (atom [])
        world (rtp/world-identity ctx)
        parent
        (binding [ec/*execution-context* (assoc ctx :bindings {:public-test/scope :construction})]
          (spin
           [(address/with-key :loop-scope
              (loop [i 0 seen []]
                (if (= i 3)
                  seen
                  (let [child (public-native-gate (keyword (str "loop-child-" i)) callbacks)
                        value (await child)]
                    (recur (inc i)
                           (conj seen [i value
                                       (address/current-key (ec/current-execution-context))
                                       (get-in (ec/current-execution-context) [:bindings :public-test/scope])
                                       (identical? world (rtp/world-identity (ec/current-execution-context)))]))))))
            (address/current-key (ec/current-execution-context))
            (get-in (ec/current-execution-context) [:bindings :public-test/scope])]))]
    (binding [ec/*execution-context* (assoc ctx :bindings {:public-test/scope :caller})]
      (is (= spin-core/incomplete (parent #(swap! values conj %) #(throw %)))))
    (doseq [value [10 20 30]]
      (is (empty? @values))
      (binding [ec/*execution-context* other]
        ((first @callbacks) value)
        (is (identical? other (ec/current-execution-context)))))
    (is (= [[[[0 10 :loop-scope :construction true]
              [1 20 :loop-scope :construction true]
              [2 30 :loop-scope :construction true]]
             nil :construction]]
           @values))
    (verify-boundaries! ctx)))
