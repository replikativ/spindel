(ns org.replikativ.spindel.yggdrasil.construction-test
  (:require #?(:clj [clojure.test :refer [deftest is]]
               :cljs [cljs.test :refer-macros [deftest is]])
            [org.replikativ.spindel.yggdrasil.construction :as c]
            [yggdrasil.protocols :as p]))

(def sync-opts {:sync? true})
(defn- error-type [f]
  (try (f) nil (catch #?(:clj Throwable :cljs :default) error (:type (ex-data error)))))

(defrecord NativeOverlay [parent local-writes mode id live calls fail?]
  p/Overlayable
  (advance! [this] this)
  (advance! [this _] this)
  (peek-parent [_] parent)
  (peek-parent [_ _] parent)
  (base-ref [_] "basis")
  (overlay-writes [_] {})
  (merge-down! [_] parent)
  (merge-down! [_ _] parent)
  (discard! [this] (p/discard! this {}))
  (discard! [_ opts]
    (let [effect (fn []
                   (swap! calls conj id)
                   (when @fail? (throw (ex-info "Injected native cleanup failure" {})))
                   (swap! live disj id)
                   parent)]
      (if (= false (:sync? opts))
        (fn [resolve reject] (try (resolve (effect)) (catch #?(:clj Throwable :cljs :default) e (reject e))))
        (effect)))))

(defn- acquire! [owner signal id live calls fail?]
  (let [source {:parent signal}]
    (c/observe! owner {:phase :before :signal signal :source source})
    (swap! live conj id)
    (let [native (->NativeOverlay source (atom source) :frozen id live calls fail?)]
      (c/observe! owner {:phase :value :signal signal :source source :value native})
      native)))

(deftest acknowledged-resources-unwind-in-reverse-order-exactly-once
  (let [owner (c/create {1 "first" 2 "second"}) live (atom #{}) calls (atom []) fail? (atom false)]
    (acquire! owner 1 :first live calls fail?)
    (acquire! owner 2 :second live calls fail?)
    (c/failed! owner (ex-info "Later pure initialization failed" {}))
    (c/dispose! owner sync-opts)
    (c/dispose! owner sync-opts)
    (is (= [:second :first] @calls))
    (is (empty? @live))
    (is (= :closed (:status (c/info owner))))
    (is (every? #(= #{:id :system :kind :phase} (set (keys %))) (:receipts (c/info owner))))))

(deftest shared-values-are-never-native-cleanup-acquisitions
  (let [source {:shared true} owner (c/create {1 "shared"})]
    (c/observe! owner {:phase :before :signal 1 :source source})
    (c/observe! owner {:phase :value :signal 1 :source source :value source})
    (c/failed! owner (ex-info "Pure component refused" {}))
    (c/dispose! owner sync-opts)
    (is (= :empty (:phase (first (:receipts (c/info owner))))))
    (is (= {:shared true} source))))

(deftest an-unacknowledged-native-attempt-is-not-assumed-absent
  (let [owner (c/create {1 "native"})]
    (c/observe! owner {:phase :before :signal 1 :source {:native :source}})
    (c/failed! owner (ex-info "Allocator reply lost" {}))
    (is (= ::c/incomplete (error-type #(c/dispose! owner sync-opts))))
    (let [receipt (first (:receipts (c/info owner)))]
      (is (= :uncertain (:phase receipt)))
      ;; Only this fixture knows its injected constructor never allocated.
      (c/resolve-uncertain! owner (:id receipt) :not-acquired))
    (c/dispose! owner sync-opts)
    (is (= :closed (:status (c/info owner))))))

(deftest cleanup-failure-holds-until-authoritative-retry-reconciliation
  (let [owner (c/create {1 "native"}) live (atom #{}) calls (atom []) fail? (atom true)]
    (acquire! owner 1 :native live calls fail?)
    (c/failed! owner (ex-info "Descriptor failed" {}))
    (is (= ::c/incomplete (error-type #(c/dispose! owner sync-opts))))
    (is (= ::c/incomplete (error-type #(c/dispose! owner sync-opts))))
    (is (= [:native] @calls) "An ambiguous cleanup is not blindly replayed")
    (is (= #{:native} @live))
    (reset! fail? false)
    ;; The test adapter proves its injected failure occurred before the effect.
    (c/resolve-uncertain! owner (:id (first (:receipts (c/info owner)))) :retry-safe)
    (c/dispose! owner sync-opts)
    (is (= [:native :native] @calls))
    (is (empty? @live))))

(deftest ownership-handoff-is-acknowledged-and-invalidates-the-old-capability
  (let [owner (c/create {1 "native"}) live (atom #{}) calls (atom []) fail? (atom false)
        claimed (atom nil)]
    (acquire! owner 1 :native live calls fail?)
    (c/failed! owner (ex-info "Failed construction" {}))
    (is (= {:claimed? true}
           (c/offer! owner (fn [candidate]
                             (reset! claimed candidate)
                             (is (= ::c/transferred (error-type #(c/dispose! candidate sync-opts))))
                             true))))
    (is (= ::c/transferred (error-type #(c/dispose! owner sync-opts))))
    (c/dispose! @claimed sync-opts)
    (is (= [:native] @calls))
    (is (empty? @live))))

(deftest rejected-or-throwing-receivers-do-not-consume-the-original-owner
  (doseq [throws? [false true]]
    (let [owner (c/create {1 "native"}) live (atom #{}) calls (atom []) fail? (atom false)
          offered (atom nil) failure (ex-info "Receiver could not register ownership" {})]
      (acquire! owner 1 :native live calls fail?)
      (c/failed! owner (ex-info "Failed construction" {}))
      (let [outcome (c/offer! owner (fn [candidate]
                                      (reset! offered candidate)
                                      (if throws? (throw failure) false)))]
        (is (false? (:claimed? outcome)))
        (is (identical? owner (:owner outcome)))
        (when throws? (is (identical? failure (:error outcome)))))
      (is (= ::c/transferred (error-type #(c/dispose! @offered sync-opts))))
      (c/dispose! owner sync-opts)
      (is (= [:native] @calls))
      (is (empty? @live)))))

(deftest asynchronous-cleanup-is-inert-until-driven-and-joins-native-completion
  (let [owner (c/create {1 "native"}) live (atom #{}) calls (atom []) fail? (atom false)
        result (atom :pending)]
    (acquire! owner 1 :native live calls fail?)
    (c/failed! owner (ex-info "Failed construction" {}))
    (let [operation (c/dispose! owner {:sync? false})]
      (is (fn? operation))
      (is (empty? @calls))
      (operation #(reset! result [:ok %]) #(reset! result [:error %]))
      (is (= [:ok nil] @result))
      (is (= [:native] @calls))
      (is (empty? @live)))))

(deftest async-cleanup-failure-releases-the-owner-guard-and-keeps-the-receipt
  (let [owner (c/create {1 "native"}) live (atom #{}) calls (atom []) fail? (atom true)
        result (atom nil)]
    (acquire! owner 1 :native live calls fail?)
    (c/failed! owner (ex-info "Descriptor failed" {}))
    ((c/dispose! owner {:sync? false})
     #(reset! result [:ok %])
     #(reset! result [:error (:type (ex-data %))]))
    (is (= [:error ::c/incomplete] @result))
    (is (false? (:busy? (c/info owner))))
    (is (= :cleanup-uncertain (:phase (first (:receipts (c/info owner))))))
    (is (= [:native] @calls))
    (is (= #{:native} @live))
    ;; Native fixture attests that its injected failure happened before removal.
    (reset! fail? false)
    (c/resolve-uncertain! owner (:id (first (:receipts (c/info owner)))) :retry-safe)
    (c/dispose! owner sync-opts)
    (is (empty? @live))))

(defrecord HeldOverlay [parent local-writes mode finish calls]
  p/Overlayable
  (advance! [this] this)
  (advance! [this _] this)
  (peek-parent [_] parent)
  (peek-parent [_ _] parent)
  (base-ref [_] "basis")
  (overlay-writes [_] {})
  (merge-down! [_] parent)
  (merge-down! [_ _] parent)
  (discard! [this] (p/discard! this {}))
  (discard! [_ _]
    (fn [resolve _]
      (swap! calls inc)
      (reset! finish #(resolve parent)))))

(deftest an-in-flight-disposal-cannot-be-reentered-or-handed-off
  (let [owner (c/create {1 "native"}) finish (atom nil) calls (atom 0)
        native (->HeldOverlay :source (atom nil) :frozen finish calls)
        first-result (atom :pending) second-result (atom :pending)]
    (c/observe! owner {:phase :before :signal 1 :source :source})
    (c/observe! owner {:phase :value :signal 1 :source :source :value native})
    (c/failed! owner (ex-info "Descriptor failed" {}))
    ((c/dispose! owner {:sync? false})
     #(reset! first-result [:ok %]) #(reset! first-result [:error %]))
    (is (= :pending @first-result))
    (is (true? (:busy? (c/info owner))))
    ((c/dispose! owner {:sync? false})
     #(reset! second-result [:ok %]) #(reset! second-result [:error (:type (ex-data %))]))
    (is (= [:error ::c/busy] @second-result))
    (is (= ::c/busy (error-type #(c/offer! owner (constantly true)))))
    (is (= 1 @calls))
    (@finish)
    (is (= [:ok nil] @first-result))
    (is (= :closed (:status (c/info owner))))
    (is (false? (:busy? (c/info owner))))))
