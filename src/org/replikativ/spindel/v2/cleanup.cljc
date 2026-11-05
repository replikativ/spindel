(ns org.replikativ.spindel.v2.cleanup
  "One-shot declared external closes. No engine scheduling or world references.
   core owns admission; this module owns shared settlement and subscriptions."
  (:require [replikativ.logging :as log]))

(deftype Resource [origin owner ancestors identity state dispatch])
(deftype Operation [origin target state dispatch])

(defn resource? [x] (instance? Resource x))
(defn operation? [x] (instance? Operation x))
(defn resource-origin [^Resource r] (.-origin r))
(defn resource-owner [^Resource r] (.-owner r))
(defn origin [^Operation o] (.-origin o))
(defn target [^Operation o] (.-target o))

(defn resource
  "Declares a resource already owned by [origin owner]. Registration starts its
   close, has finite nonblocking execution, and returns an optional detachable
   subscription control. Declaration itself neither starts nor auto-closes it."
  [origin owner ancestors register dispatch]
  (Resource. origin owner ancestors #?(:clj (Object.) :cljs (js-obj))
             (atom {:phase :new :register register :subscribers {} :next 0}) dispatch))

(defn operation [origin ^Resource r]
  (Operation. origin {:kind :resource :origin (.-origin r) :owner (.-owner r)
                      :ancestors (.-ancestors r) :identity (.-identity r)} (.-state r) (.-dispatch r)))

(defn observation-state
  "An externally driven observation. No registration callback can manufacture
   settlement: only its owning world publishes a milestone."
  []
  (atom {:phase :pending :subscribers {} :next 0}))

(defn observation [origin target state dispatch]
  (Operation. origin target state dispatch))

(defn- safely! [f]
  (when f
    (try (f)
         (catch #?(:clj Throwable :cljs :default) t
           (log/error :engine/cleanup-callback-failed {:error t})))))

(defn settle-observation! [state dispatch outcome]
  (loop []
    (let [old @state]
      (when-not (= :settled (:phase old))
        (if (compare-and-set! state old (cond-> {:phase :settled :outcome outcome}
                                    (:diagnostics old) (assoc :diagnostics (:diagnostics old))))
          (dispatch
           #(do (safely! (:detach old))
                (doseq [[_ cb] (:subscribers old)]
                  (safely! (fn [] (cb outcome))))))
          (recur)))))
  nil)

(defn- register! [state dispatch register]
  (let [complete (fn complete
                   ([value] (complete value false))
                   ([value failed?] (settle-observation! state dispatch [value (boolean failed?)])))
        detach (try (register complete)
                    (catch #?(:clj Throwable :cljs :default) t
                      (complete t true)
                      nil))]
    (when (fn? detach)
      (loop []
        (let [old @state]
          (if (= :settled (:phase old))
            (dispatch #(safely! detach))
            (when-not (compare-and-set! state old (assoc old :detach detach))
              (recur))))))))

(defn subscribe!
  "After the world gate: subscribe to a shared close; the first subscription
   registers it once. Returns observer withdrawal, which never cancels close.
   Terminal callbacks and callback-then-throw are first-terminal-wins."
  [^Operation op cb]
  (let [state (.-state op) dispatch (.-dispatch op)]
    (loop []
      (let [old @state]
        (if (= :settled (:phase old))
          (do (dispatch #(safely! (fn [] (cb (:outcome old))))) (fn [] nil))
          (let [id (:next old)
                register (:register old)
                next-state (-> old (assoc :phase :pending :register nil)
                               (update :next inc) (assoc-in [:subscribers id] cb))]
            (if (compare-and-set! state old next-state)
              (do (when register (register! state dispatch register))
                  (fn [] (swap! state (fn [s]
                                        (if (= :settled (:phase s)) s
                                            (update s :subscribers dissoc id)))) nil))
              (recur))))))))

(defn status
  "Data-only current state; never exposes registration, controllers or callbacks."
  [^Operation op]
  (let [s @(.-state op)]
    (cond-> {:phase (:phase s) :subscribers (count (:subscribers s))}
      (= :settled (:phase s)) (assoc :outcome (:outcome s)))))
