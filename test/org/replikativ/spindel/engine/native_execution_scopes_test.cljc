(ns org.replikativ.spindel.engine.native-execution-scopes-test
  (:require #?(:clj [clojure.test :refer [deftest is]]
               :cljs [cljs.test :refer-macros [deftest is]])
            [org.replikativ.spindel.effects.track :refer [track]]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.impl.owned :as c #?@(:cljs [:include-macros true])]
            [org.replikativ.spindel.engine.lifetime :as lifetime #?@(:cljs [:include-macros true])]
            [org.replikativ.spindel.engine.protocols :as rtp]
            [org.replikativ.spindel.engine.owned-runtime-test :refer [verify-boundaries!]]
            [org.replikativ.spindel.incremental.interval :as iv]
            [org.replikativ.spindel.signal :as signal]
            [org.replikativ.spindel.spin.core :as spin-core]
            [org.replikativ.spindel.spin.cps :refer [spin]]))

(deftest reactive-prefix-keeps-nested-scope-ownership-and-closes-old-suffix
  (let [rt (c/runtime {:audit? true}) driver (c/signal rt :driver 0)
        caps (atom nil) outcomes (atom []) errors (atom [])
        task (c/cspin rt :parent
                      (let [prefix (lifetime/open-scope! rt :explicit)
                            nested (lifetime/open-scope! rt :nested prefix)]
                        (reset! caps {:prefix prefix :nested nested})
                        (binding [ec/*owner-scope* nested]
                          (c/signal rt :scoped-source :kept))
                        (let [value (iv/get-new (c/track driver))]
                          (lifetime/open-scope! rt :suffix)
                          value)))]
    (binding [ec/*execution-context* rt]
      (c/observe! rt task #(swap! outcomes conj %) #(swap! errors conj %))
      (let [before (c/snapshot rt)]
        (is (= 3 (:scope-balance before)))
        (is (= [:scope :id 0] (get-in before [:scopes [:scope :id 1] :parent])))
        (is (= [:scope :id 1] (get-in before [:entities :scoped-source :owner]))))
      (c/set-signal! rt driver 1)
      (let [after (c/snapshot rt)]
        (is (= [0 1] @outcomes))
        (is (empty? @errors))
        (is (= 4 (:next-scope after)))
        (is (= 3 (:scope-balance after)))
        (is (= [:parent 2] (get-in after [:scopes [:scope :id 0] :parent])))
        (is (= [:scope :id 0] (get-in after [:scopes [:scope :id 1] :parent])))
        (is (nil? (get-in after [:scopes [:scope :id 2]])))
        (is (= [:parent 2] (get-in after [:scopes [:scope :id 3] :parent])))
        (is (= [:scope :id 1] (get-in after [:entities :scoped-source :owner])))
        (is (empty? (get-in after [:runs [:parent 2] :creations]))))
      (is (nil? (lifetime/close-scope! rt (:prefix @caps))))
      (let [after (c/snapshot rt)]
        (is (= 1 (:scope-balance after)))
        (is (nil? (get-in after [:entities :scoped-source])))
        (is (true? (rtp/execution-owner-joined? rt (:prefix @caps))))))
    (verify-boundaries! rt)))

(deftest following-copy-rebinds-captured-scopes-without-sharing-mutable-owners
  (let [rt (c/runtime {:audit? true}) first-ticket (c/ticket :first)
        second-ticket (c/ticket :second) caps (atom nil) errors (atom [])
        task (c/cspin rt :parent
                      (let [prefix (lifetime/open-scope! rt :explicit)
                            nested (lifetime/open-scope! rt :nested prefix)]
                        (reset! caps {:prefix prefix :nested nested})
                        (binding [ec/*owner-scope* nested]
                          (c/signal rt :before :before)
                          (c/park first-ticket)
                          (c/signal rt :after :after)
                          (c/park second-ticket))))]
    (binding [ec/*execution-context* rt]
      (c/observe! rt task (fn [_]) #(swap! errors conj %)))
    (let [child (c/fork-parked! rt [:w 1])
          before (c/snapshot child)]
      (is (= :inherited (get-in before [:runs [:parent 1] :status])))
      (is (= 2 (:scope-balance before)))
      (is (= 2 (:next-scope before)))
      (is (= [:parent 1] (get-in before [:scopes [:scope :id 0] :parent])))
      (is (= [:scope :id 0] (get-in before [:scopes [:scope :id 1] :parent])))
      (is (= [:scope :id 1] (get-in before [:entities :before :owner])))
      (is (thrown? #?(:clj Exception :cljs js/Error)
                   (lifetime/bindable-scope child (:nested @caps))))
      (is (= before (c/snapshot child)))
      (c/resume-ticket! child (c/pending-ticket child first-ticket) :continue)
      (is (empty? @errors))
      (let [after (c/snapshot child)]
        (is (= :parked (get-in after [:runs [:parent 1] :status])))
        (is (= [:scope :id 1] (get-in after [:entities :after :owner])))
        (is (nil? (get-in (c/snapshot rt) [:entities :after]))))
      (let [scoped-child (binding [ec/*owner-scope* (:nested @caps)]
                           (c/fork-parked! rt [:w 2]))]
        (is (= [:scope :id 1] (get-in (c/snapshot rt) [:entities [:fork [:w 2]] :owner])))
        (is (= :live (:status (c/snapshot scoped-child))))
        (lifetime/close-scope! rt (:prefix @caps))
        (is (= :released (:status (c/snapshot scoped-child)))))
      (is (zero? (:scope-balance (c/snapshot rt))))
      (is (= 2 (:scope-balance (c/snapshot child))))
      (is (= [:scope :id 1] (get-in (c/snapshot child) [:entities :after :owner])))
      (verify-boundaries! rt))))

(deftest dirty-cold-body-replacement-closes-all-predecessor-scopes
  (let [rt (c/runtime {:audit? true}) driver (c/signal rt :driver 0)
        target #?(:clj (Object.) :cljs (js-obj)) errors (atom [])
        body (fn [version]
               (with-meta
                 (fn [succeed fail]
                   (let [scope (lifetime/open-scope! rt :explicit)]
                     (binding [ec/*owner-scope* scope]
                       (c/signal rt (keyword (str "dirty-source-" version)) version))
                     (c/track-effect! driver #(succeed [version (iv/get-new %)]) fail)))
                 {::rtp/computation {:captured-locals {:version version}}}))
        first-body (body 1) second-body (body 2)]
    (binding [ec/*execution-context* rt]
      (rtp/register-computation! rt target :parent first-body)
      (rtp/invoke-computation! rt target :parent first-body (fn [_]) #(swap! errors conj %) :callback)
      (is (= [:scope :id 0] (get-in (c/snapshot rt) [:entities :dirty-source-1 :owner])))
      (rtp/register-computation! rt target :parent second-body)
      (rtp/invoke-computation! rt target :parent second-body (fn [_]) #(swap! errors conj %) :callback)
      (let [after (c/snapshot rt)]
        (is (empty? @errors))
        (is (= [2 0] (get-in after [:entities :parent :result])))
        (is (= 2 (:next-scope after)))
        (is (= 1 (:scope-balance after)))
        (is (nil? (get-in after [:scopes [:scope :id 0]])))
        (is (nil? (get-in after [:entities :dirty-source-1])))
        (is (= [:parent 2] (get-in after [:scopes [:scope :id 1] :parent])))
        (is (= [:scope :id 1] (get-in after [:entities :dirty-source-2 :owner])))))
    (verify-boundaries! rt)))

(defn- bindable? [rt owner]
  (try (lifetime/bindable-scope rt owner) true
       (catch #?(:clj Throwable :cljs :default) _ false)))

(deftest explicit-target-construction-honors-the-targets-authenticated-scope
  (let [caller (c/runtime {:audit? true}) target (c/runtime {:audit? true})
        scope (lifetime/open-scope! target :explicit)
        created (atom nil) values (atom []) errors (atom [])]
    (binding [ec/*execution-context* caller]
      (let [task (spin
                  (let [implicit-cell (rtp/allocate-runtime-cell! target :implicit {})
                        implicit-signal (signal/signal target :implicit)]
                    (binding [ec/*execution-context* target]
                      (lifetime/with-owner scope
                        (reset! created
                                {:implicit-cell implicit-cell
                                 :implicit-signal implicit-signal
                                 :scoped-cell (rtp/allocate-runtime-cell! target :scoped {})
                                 :scoped-signal (signal/signal target :scoped)})))
                    :done))]
        (task #(swap! values conj %) #(swap! errors conj %))))
    (is (empty? @errors))
    (is (= [:done] @values))
    (let [after (c/snapshot target)]
      (doseq [key [:implicit-cell :implicit-signal]]
        (is (= c/root (get-in after [:entities (:id (get @created key)) :owner]))))
      (doseq [key [:scoped-cell :scoped-signal]]
        (is (= [:scope :id 0] (get-in after [:entities (:id (get @created key)) :owner])))))
    (verify-boundaries! caller)
    (verify-boundaries! target)))

(deftest nested-ambient-context-does-not-reclassify-the-actual-runners-owner
  (let [caller (c/runtime {:audit? true}) ambient (c/runtime {:audit? true})
        scope (lifetime/open-scope! ambient :explicit)
        task-id (atom nil) values (atom []) errors (atom [])]
    (binding [ec/*execution-context* caller]
      (let [driver (signal/signal 0)
            task (spin
                  (let [owner (lifetime/current-scope caller)]
                    (lifetime/with-owner owner
                      (let [value (binding [ec/*execution-context* ambient]
                                     ;; Entry saves outer RunA while the ambient
                                     ;; context names B; the actual runner is A.
                                    (lifetime/with-owner scope
                                      (binding [ec/*execution-context* caller]
                                        (iv/get-new (track driver)))))]
                         ;; This allocation is still inside the outer Run owner
                         ;; binding, after the inner Scope and context have exited.
                        (signal/register-signal! caller (signal/->SignalRef [:after-ambient value] value))
                        value))))]
        (reset! task-id (spin-core/spin-id task))
        (task #(swap! values conj %) #(swap! errors conj %))
        (reset! driver 1)))
    (is (empty? @errors))
    (is (= [0 1] @values))
    (let [after (c/snapshot caller)]
      (is (= [@task-id 2] (get-in after [:entities [:after-ambient 1] :owner])))
      (is (nil? (get-in (c/snapshot ambient) [:entities [:after-ambient 1]]))))
    (verify-boundaries! caller)
    (verify-boundaries! ambient)))

(deftest restored-current-run-owner-advances-across-repeated-reactive-reentry
  (let [rt (c/runtime {:audit? true}) driver (c/signal rt :driver 0)
        saved (atom nil) authorizations (atom []) restored-owners (atom []) values (atom []) errors (atom [])
        task (c/cspin rt :reader
                      (let [owner (lifetime/current-scope rt)]
                        (reset! saved owner)
                        (lifetime/with-owner owner
                          (let [value (iv/get-new (c/track driver))]
                            (swap! restored-owners conj [value (identical? owner ec/*owner-scope*)
                                                         (and (vector? ec/*owner-scope*) (= :run (first ec/*owner-scope*)))])
                            (swap! authorizations conj [value (bindable? rt owner)])
                            (c/signal rt :restored-source value)
                            value))))]
    (binding [ec/*execution-context* rt]
      (c/observe! rt task #(swap! values conj %) #(swap! errors conj %))
      (c/set-signal! rt driver 1)
      (c/set-signal! rt driver 2))
    (is (empty? @errors))
    (is (= [0 1 2] @values))
    (is (= [[0 false true] [1 false true] [2 false true]] @restored-owners))
    (is (= [[0 true] [1 false] [2 false]] @authorizations)
        "Restoring a dynamic binding grants no fresh stale-cap binding authority")
    (let [after (c/snapshot rt)]
      (is (= [:reader 3] (get-in after [:entities :restored-source :owner])))
      (is (nil? (get-in after [:runs [:reader 1]])))
      (is (not (contains? (get-in after [:runs [:reader 3] :ancestors]) [:reader 1])))
      (is (false? (bindable? rt @saved)))
      (is (thrown? #?(:clj Exception :cljs js/Error) (lifetime/open-scope! rt :stale-parent @saved)))
      (is (= after (c/snapshot rt))))
    (verify-boundaries! rt)))

(deftest restored-copied-run-owner-does-not-authorize-fresh-foreign-owner-arguments
  (let [rt (c/runtime {:audit? true}) first-ticket (c/ticket :first-run-owner)
        second-ticket (c/ticket :second-run-owner) saved (atom nil) attempts (atom [])
        authorizations (atom []) restored-owners (atom []) errors (atom [])
        task (c/cspin rt :reader
                      (let [owner (lifetime/current-scope rt)]
                        (reset! saved owner)
                        (lifetime/with-owner owner
                          (c/park first-ticket)
                          (swap! attempts conj :resumed)
                          (swap! restored-owners conj [(identical? owner ec/*owner-scope*)
                                                       (and (vector? ec/*owner-scope*) (= :run (first ec/*owner-scope*)))])
                          (swap! authorizations conj (bindable? (ec/current-execution-context) owner))
                          (c/signal rt :copied-run-source :copied)
                          (c/park second-ticket))))]
    (binding [ec/*execution-context* rt]
      (c/observe! rt task (fn [_]) #(swap! errors conj %)))
    (let [child (c/fork-parked! rt [:w 1])]
      (c/resume-ticket! child (c/pending-ticket child first-ticket) :continue)
      (is (= [:resumed] @attempts))
      (is (= [[false true]] @restored-owners))
      (is (= [false] @authorizations))
      (is (empty? @errors))
      (let [after (c/snapshot child)]
        (is (= :parked (get-in after [:runs [:reader 1] :status])))
        (is (= [:reader 1] (get-in after [:entities :copied-run-source :owner])))
        (is (zero? (:scope-balance after)))
        (is (false? (bindable? child @saved)))
        (is (thrown? #?(:clj Exception :cljs js/Error) (lifetime/open-scope! child :foreign-parent @saved)))
        (is (= after (c/snapshot child))))
      (verify-boundaries! rt))))

(deftest public-with-owner-scope-survives-the-reactive-breakpoint
  (let [rt (c/runtime {:audit? true}) driver (c/signal rt :driver 0)
        scope (lifetime/open-scope! rt :explicit) bindings (atom []) values (atom []) errors (atom [])
        task (c/cspin rt :reader
                      (lifetime/with-owner scope
                        (let [value (iv/get-new (c/track driver))]
                          (swap! bindings conj [value (identical? scope ec/*owner-scope*)])
                          ;; Each generation must allocate a fresh source: reusing
                          ;; one ID could conceal a dropped binding behind its old owner.
                          (c/signal rt [:scoped-after value] value)
                          value)))]
    (binding [ec/*execution-context* rt]
      (c/observe! rt task #(swap! values conj %) #(swap! errors conj %))
      (c/set-signal! rt driver 1))
    (is (empty? @errors))
    (is (= [0 1] @values))
    (is (= [[0 true] [1 true]] @bindings))
    (let [after (c/snapshot rt)]
      (is (= [:scope :id 0] (get-in after [:entities [:scoped-after 0] :owner])))
      (is (= [:scope :id 0] (get-in after [:entities [:scoped-after 1] :owner]))))
    (verify-boundaries! rt)))

(deftest nested-owner-exit-restores-entry-qualified-outer-owners
  (let [rt (c/runtime {:audit? true}) driver (c/signal rt :driver 0)
        outer (lifetime/open-scope! rt :outer) inner (lifetime/open-scope! rt :inner)
        bindings (atom []) values (atom []) errors (atom [])
        task (c/cspin rt :reader
                      (let [value (lifetime/with-owner outer
                                    (let [value (lifetime/with-owner inner
                                                  (iv/get-new (c/track driver)))]
                                      (swap! bindings conj [value (identical? outer ec/*owner-scope*)])
                                      (c/signal rt [:after-inner value] value)
                                      value))]
                        (c/signal rt [:after-outer value] value)
                        value))]
    (binding [ec/*execution-context* rt]
      (c/observe! rt task #(swap! values conj %) #(swap! errors conj %))
      (c/set-signal! rt driver 1)
      (c/set-signal! rt driver 2))
    (is (empty? @errors))
    (is (= [0 1 2] @values))
    (is (= [[0 true] [1 true] [2 true]] @bindings))
    (let [after (c/snapshot rt)]
      (is (= [:scope :id 0] (get-in after [:entities [:after-inner 2] :owner])))
      (is (= [:reader 3] (get-in after [:entities [:after-outer 2] :owner]))))
    (verify-boundaries! rt)))

(deftest nested-scope-exit-does-not-launder-a-foreign-future-run-cap
  (let [rt (c/runtime {:audit? true})
        first-ticket (c/ticket :before-foreign-binding)
        second-ticket (c/ticket :inside-local-scope)
        third-ticket (c/ticket :after-foreign-binding)
        foreign (atom nil) attempts (atom []) errors (atom [])
        task (c/cspin rt :reader
                      (reset! foreign (lifetime/current-scope (ec/current-execution-context)))
                      (c/park first-ticket)
                      (let [actual (ec/current-execution-context)
                            local (lifetime/open-scope! actual :local)]
                          ;; This raw foreign binding is not admission. Capturing
                          ;; it at nested binding entry must keep it literal.
                        (binding [ec/*owner-scope* @foreign]
                          (lifetime/with-owner local (c/park second-ticket))
                          (swap! attempts conj
                                 [(identical? @foreign ec/*owner-scope*)
                                  (try (c/signal actual :must-refuse :value) :accepted
                                       (catch #?(:clj Throwable :cljs :default) _ :refused))]))
                        (c/signal actual :after-foreign-exit :value)
                        (c/park third-ticket)))]
    (binding [ec/*execution-context* rt]
      (c/observe! rt task (fn [_]) #(swap! errors conj %)))
    (let [child (c/fork-parked! rt [:w 1])]
      ;; Parent Run2 was never copied into the child. Its RootOwner is nevertheless
      ;; in the child's actual copy provenance, so provenance alone is insufficient.
      (binding [ec/*execution-context* rt]
        (c/cancel-spin! rt task)
        (is (= 1 (count @errors)))
        (reset! errors [])
        (c/observe! rt task (fn [_]) #(swap! errors conj %)))
      (is (= :parked (get-in (c/snapshot rt) [:runs [:reader 2] :status])))
      (c/resume-ticket! child (c/pending-ticket child first-ticket) :continue)
      (is (= :parked (get-in (c/snapshot child) [:runs [:reader 1] :status])))
      (c/resume-ticket! child (c/pending-ticket child second-ticket) :continue)
      (is (= :parked (get-in (c/snapshot child) [:runs [:reader 1] :status])))
      (is (empty? @errors))
      (is (= [[true :refused]] @attempts))
      (let [after (c/snapshot child)]
        (is (nil? (get-in after [:entities :must-refuse])))
        (is (= [:reader 1] (get-in after [:entities :after-foreign-exit :owner]))))
      (verify-boundaries! rt))))
