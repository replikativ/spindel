(ns org.replikativ.spindel.engine.native-computation-test
  (:require #?(:clj [clojure.test :refer [deftest is testing]]
               :cljs [cljs.test :refer-macros [deftest is testing]])
            [is.simm.partial-cps.async :as cps]
            [is.simm.partial-cps.runtime :as cps-runtime]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.protocols :as rtp]
            [org.replikativ.spindel.engine.impl.owned :as owned #?@(:cljs [:include-macros true])]
            [org.replikativ.spindel.engine.owned-runtime-test :refer [verify-boundaries!]]))

(defn- target [] #?(:clj (Object.) :cljs (js-obj)))
(defn- described [body captures & [scope kind]]
  (with-meta body {::rtp/computation {:captured-locals captures :spin-scope scope
                                      :kind (or kind :computation)}}))
(defn- invoke! [rt target id body values]
  (rtp/invoke-computation! rt target id body #(swap! values conj %) #(throw %) :callback))

(deftest native-world-identities-remain-distinct-for-equal-model-coordinates
  (let [a (owned/runtime {:bindings nil :metadata nil})
        b (owned/runtime {:bindings nil :metadata nil})
        decorated (assoc a :bindings {:scope :lexical})
        identity-a (rtp/world-identity a)
        identity-b (rtp/world-identity b)]
    (is (= [:root owned/w] (:id identity-a)))
    (is (= (:id identity-a) (:id identity-b)) "Symbolic owner projection stays unchanged")
    (is (not (identical? identity-a identity-b)))
    (is (not= identity-a identity-b))
    (is (= 2 (count #{identity-a identity-b})))
    (is (= 2 (count (assoc {} identity-a :a identity-b :b))))
    (is (identical? identity-a (rtp/world-identity decorated)))
    (is (true? (ec/same-world? a decorated)))
    (is (false? (ec/same-world? a b)))
    (is (= [:root owned/w] (get identity-a :id :missing)))
    (is (= :missing (get identity-a :absent :missing)))
    (is (nil? (get identity-a :absent)))))

(deftest constructors-are-lazy-and-capture-changes-select-a-cold-generation
  (let [rt (owned/runtime {:audit? true}) calls (atom []) values (atom [])
        a (target) b (target)
        make-body (fn [value] (described (fn [r _] (swap! calls conj value) (r value)) {'value value}))
        body-a (make-body 1000) body-a2 (make-body 1000) body-b (make-body 2000)]
    (rtp/register-computation! rt a :public body-a)
    (is (empty? @calls))
    (is (= 1000 (invoke! rt a :public body-a values)))
    (rtp/register-computation! (assoc rt :bindings {:lexical true}) b :public body-a2)
    (is (= 1000 (invoke! rt b :public body-a2 values)))
    (is (= [1000] @calls) "Equal scalar captures retain the clean cache")
    (rtp/register-computation! rt b :public body-b)
    (is (= [1000] @calls) "Invalidation does not execute a replacement")
    (is (false? (:clean? (rtp/computation-result rt b :public))))
    (is (= 2000 (invoke! rt b :public body-b values)))
    (is (= [1000 2000] @calls))
    ;; Invoking an older handle also prepares its own descriptor baseline.
    (is (= 1000 (invoke! rt a :public body-a values)))
    (is (= [1000 2000 1000] @calls))
    (is (= {:variant :ok :payload 1000 :clean? true} (rtp/computation-result rt a :public)))
    (verify-boundaries! rt)))

(deftest resource-registration-invalidates-without-deep-collection-comparison
  (let [rt (owned/runtime {:audit? true}) a (target) values (atom []) runs (atom 0)
        body (described (fn [r _] (r (swap! runs inc))) {} nil :resource)]
    (rtp/register-computation! rt a :resource body)
    (is (= 1 (invoke! rt a :resource body values)))
    (rtp/register-computation! rt a :resource body)
    (is (= 1 @runs))
    (is (= 2 (invoke! rt a :resource body values)))
    (verify-boundaries! rt)))

(deftest changed-parked-body-preserves-incoming-observers-and-refuses-old-delivery
  (let [rt (owned/runtime {:audit? true}) a (target) b (target)
        values (atom []) gate (owned/ticket :old)
        old (described (fn [r j] (owned/park-effect! gate (fn [_] (r :old)) j)) {'value :old})
        new (described (fn [r _] (r :new)) {'value :new})]
    (rtp/register-computation! rt a :public old)
    (is (= :org.replikativ.spindel.spin/incomplete (invoke! rt a :public old values)))
    (let [obsolete (owned/pending-ticket rt gate)]
      (rtp/register-computation! rt b :public new)
      (is (empty? @values))
      (is (= :parked (get-in (owned/snapshot rt) [:runs [:public 1] :status])))
      (is (= :new (invoke! rt b :public new values)))
      (is (= [:new :new] @values) "Both incoming observers see the successor")
      (owned/resume-ticket! rt obsolete :late)
      (is (= [:new :new] @values)))
    (verify-boundaries! rt)))

(deftest typed-runner-seats-world-generation-and-cold-construction-scope
  (let [rt (owned/runtime {:audit? true :bindings {:base true} :metadata {:name :native}})
        other (owned/runtime) a (target) values (atom [])
        body (described
              (fn [r _]
                (r [(ec/same-world? rt ec/*execution-context*)
                    ec/*spin-id* ec/*run-gen* ec/*lifetime-run* ec/*owner-scope*
                    (:bindings ec/*execution-context*) (:metadata ec/*execution-context*)]))
              {} {:constructor true})]
    (binding [ec/*execution-context* other ec/*spin-id* :foreign ec/*run-gen* [:foreign 999]]
      (invoke! (assoc rt :bindings {:ignored-decoration true}) a :public body values)
      (is (identical? other ec/*execution-context*)))
    (is (= [[true :public [:public 1] 1 [:run owned/w :public 1]
             {:base true :constructor true} {:name :native}]] @values))
    (verify-boundaries! rt)))

(deftest typed-await-uses-the-native-suspension-and-preserves-caller-scope
  (let [rt (owned/runtime {:audit? true :bindings {:base true}}) a (target) b (target)
        gate (owned/ticket :child) values (atom [])
        child (described (fn [r j] (owned/park-effect! gate (fn [_] (r 42)) j)) {})
        parent (described
                (fn [r j]
                  (rtp/await-computation!
                   ec/*execution-context* b :child child :parent nil
                   (fn [value] (r [value ec/*spin-id* (:bindings ec/*execution-context*)])) j))
                {} {:parent-scope true})]
    (rtp/register-computation! rt a :parent parent)
    (is (= :org.replikativ.spindel.spin/incomplete (invoke! rt a :parent parent values)))
    (owned/resume-ticket! rt (owned/pending-ticket rt gate) :ready)
    (is (= [[42 :parent {:base true :parent-scope true}]] @values))
    (verify-boundaries! rt)))

(deftest cached-errors-and-callback-failures-retain-their-ownership
  (let [rt (owned/runtime {:audit? true}) a (target) failures (atom [])
        error (ex-info "body failure" {})
        body (described (fn [_ j] (j error)) {})]
    (is (nil? (rtp/invoke-computation! rt a :error body (fn [_]) #(swap! failures conj %) :callback)))
    (is (identical? error (try (rtp/invoke-computation! rt a :error body (fn [_]) #(swap! failures conj %) :callback)
                               nil (catch #?(:clj Throwable :cljs :default) caught caught))))
    (is (= [error error] @failures))
    (is (= :error (:variant (rtp/computation-result rt a :error))))
    (let [b (target) callback-error (ex-info "callback failure" {})
          success (described (fn [r _] (r false)) {})]
      (is (identical? callback-error
                      (try (rtp/invoke-computation! rt b :success success (fn [_] (throw callback-error)) (fn [_]) :callback)
                           nil (catch #?(:clj Throwable :cljs :default) caught caught))))
      (is (= {:variant :ok :payload false :clean? true} (rtp/computation-result rt b :success))))
    (verify-boundaries! rt)))

(deftest inline-callback-thunks-are-returned-to-the-callers-trampoline
  (let [rt (owned/runtime) a (target) ran (atom false)
        body (described (fn [r _] (r nil)) {})
        ret (cps-runtime/call-in-trampoline
             (fn [token]
               (binding [cps/*in-trampoline* token]
                 (rtp/invoke-computation! rt a :thunk body
                                          (fn [_] (cps-runtime/->thunk #(reset! ran true))) (fn [_]) :callback))))]
    (is (cps-runtime/thunk? ret))
    (is (false? @ran))
    (cps-runtime/force-thunk ret)
    (is (true? @ran))))

(deftest unsupported-resource-await-does-not-fall-back
  (let [rt (owned/runtime) a (target)]
    (is (= :unsupported-operation
           (try (rtp/await-computation! rt a nil nil nil nil (fn [_]) (fn [_]))
                nil
                (catch #?(:clj Exception :cljs :default) error
                  (:error (ex-data error))))))))

#?(:clj
   (deftest native-host-deref-is-one-shot-and-preserves-values-errors-and-timeouts
     (let [rt (owned/runtime {:audit? true}) a (target)]
       (doseq [[id value] [[:nil nil] [:false false]]]
         (let [body (described (fn [r _] (r value)) {'value value})]
           (is (= value (rtp/deref-computation! rt (target) id body 0 nil)))))
       (let [error (ex-info "deref failure" {}) body (described (fn [_ j] (j error)) {})]
         (is (identical? error (try (rtp/deref-computation! rt (target) :error body 0 nil)
                                    nil (catch Throwable caught caught)))))
       (let [body (described (fn [r j] (owned/park-effect! (owned/ticket :never) r j)) {})]
         (is (= :timeout (rtp/deref-computation! rt (target) :timeout body 1 :timeout)))
         (is (not-any? #(= :deref (:kind %)) (vals (:obligations (owned/snapshot rt))))))
       (verify-boundaries! rt))))

(deftest equal-collections-with-distinct-identities-invalidate-captures
  (let [rt (owned/runtime {:audit? true}) a (target) b (target) runs (atom 0) values (atom [])
        first-value (vec (range 3)) second-value (vec (range 3))
        make-body (fn [value] (described (fn [r _] (swap! runs inc) (r value)) {'value value}))
        first-body (make-body first-value) second-body (make-body second-value)]
    (is (= first-value second-value))
    (is (not (identical? first-value second-value)))
    (rtp/register-computation! rt a :collection first-body)
    (invoke! rt a :collection first-body values)
    (rtp/register-computation! rt b :collection second-body)
    (is (identical? second-value (invoke! rt b :collection second-body values)))
    (is (= 2 @runs))
    (verify-boundaries! rt)))

(deftest cold-await-checkpoint-seats-its-own-descriptor-with-the-selected-body
  (let [rt (owned/runtime {:audit? true}) a (target) b (target) parent (target)
        calls (atom []) values (atom []) parent-values (atom [])
        make-body (fn [value]
                    (described (fn [r _] (swap! calls conj value) (r value)) {'version value}))
        body-a (make-body 1) body-b (make-body 2)
        checkpoint (described
                    (fn [r j] (owned/await-computation-effect! a :child body-a r j)) {})]
    (rtp/register-computation! rt a :child body-a)
    (is (= 1 (invoke! rt a :child body-a values)))
    (rtp/register-computation! rt b :child body-b)
    (is (= [1] @calls) "Registering B invalidates lazily")
    (invoke! rt parent :checkpoint checkpoint parent-values)
    (is (= [1 1] @calls) "The old checkpoint deliberately cold-starts its saved A template")
    (is (= [1] @parent-values))
    (is (= 2 (invoke! rt b :child body-b values))
        "B cannot certify the result produced by a cold A restart")
    (is (= [1 1 2] @calls))
    (is (= [1 2] @parent-values)
        "Ordinary reactive delivery reads the latest clean B result without flipping back to A")
    (verify-boundaries! rt)))

(deftest await-checkpoint-cannot-replace-an-already-queued-public-body
  (let [rt (owned/runtime {:audit? true}) a (target) b (target) parent (target)
        calls (atom []) values (atom []) b-values (atom []) parent-values (atom [])
        make-body (fn [value]
                    (described (fn [r _] (swap! calls conj value) (r value)) {'version value}))
        body-a (make-body 1) body-b (make-body 2)
        checkpoint
        (described
         (fn [r j]
           ;; The native drain already owns this parent slice: B is queued,
           ;; so the checkpoint's join occurs before B's cold body executes.
           (invoke! rt b :child body-b b-values)
           (owned/await-computation-effect! a :child body-a r j)) {})]
    (rtp/register-computation! rt a :child body-a)
    (invoke! rt a :child body-a values)
    (rtp/register-computation! rt b :child body-b)
    (invoke! rt parent :checkpoint checkpoint parent-values)
    (is (= [1 2] @calls))
    (is (= [2] @b-values))
    (is (= [2] @parent-values))
    (verify-boundaries! rt)))

#?(:clj
   (deftest scalar-capture-equality-runs-outside-the-family-gate
     (let [rt (owned/runtime) a (target) b (target) values (atom [])
           entered (promise) release (promise)
           old (described (fn [r _] (r 42)) {'value 42})
           scalar (proxy [Number] []
                    (intValue [] 42) (longValue [] 42) (floatValue [] 42.0) (doubleValue [] 42.0)
                    (equals [_]
                      (deliver entered true)
                      (when-not (= true (deref release 5000 ::timeout))
                        (throw (ex-info "Capture equality timed out" {})))
                      false))
           new (described (fn [r _] (r scalar)) {'value scalar})]
       (rtp/register-computation! rt a :scalar old)
       (invoke! rt a :scalar old values)
       (let [registration (future (rtp/register-computation! rt b :scalar new))]
         (try
           (is (= true (deref entered 5000 ::timeout)))
           (let [write (future (rtp/swap-state! rt [:probe] (constantly :admitted)))]
             (is (= :admitted (deref write 1000 ::timeout))
                 "User scalar equality must not hold the native family gate"))
           (finally (deliver release true)))
         (is (nil? (deref registration 5000 ::timeout)))))))
