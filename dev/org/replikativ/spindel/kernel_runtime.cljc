(ns org.replikativ.spindel.kernel-runtime
  "Experimental CPS bridge for the lifetime kernel. Explicit spin IDs keep
  this experiment independent of source addressing and the public Spin type."
  (:refer-clojure :exclude [await])
  (:require [is.simm.partial-cps.async :as cps]
            [org.replikativ.spindel.engine.kernel :as kernel]
            [org.replikativ.spindel.incremental.interval :as iv]
            #?(:clj [org.replikativ.spindel.spin.cps :as compiler])))

(def ^:dynamic *runtime* nil)
(def ^:dynamic *world* [:w 0])
(def ^:dynamic *run* nil)
(def ^:dynamic *order* nil)

(defn- compare-entry [a b]
  (let [c (compare (nth a 0) (nth b 0))]
    (if (zero? c) (compare (nth a 1) (nth b 1)) c)))

(defrecord KernelRuntime [kernel bodies callbacks ready sequence draining ranks gate pending])
(defrecord Failure [error])

(defn- failed? [value] (instance? Failure value))

(defn- deliver-continuation [cont value]
  (cond
    (failed? value) (cps/invoke-continuation (:reject cont) (:error value))
    (= ::kernel/cancelled value)
    (cps/invoke-continuation (:reject cont) (ex-info "Cancelled" {:error :cancelled}))
    :else (cps/invoke-continuation (:resolve cont) value)))

(defn runtime
  ([] (runtime {}))
  ([options]
   (->KernelRuntime (kernel/create-kernel options) (atom {}) (atom {})
                    #?(:clj (java.util.PriorityQueue. 11 (reify java.util.Comparator
                                                           (compare [_ a b] (compare-entry a b))))
                       :cljs (array))
                    (volatile! 0) (atom false) (atom {}) #?(:clj (Object.) :cljs nil) (volatile! {}))))

(defn- with-gate [rt f]
  #?(:clj (locking (:gate rt) (f)) :cljs (f)))

(defn- submit! [rt commands]
  (with-gate
    rt
    (fn []
      (doseq [command commands]
        (let [schedulable? (#{:start :reactive-resume} (:op command))
              key [(:world command) (first (:run command))]
              previous (when schedulable? (get @(:pending rt) key))
              merged (if previous
                       (assoc (cond
                                (= :start (:op previous)) previous
                                (= :start (:op command)) command
                                (<= (get-in previous [:obligation :order])
                                    (get-in command [:obligation :order])) previous
                                :else command)
                              :run (:run command))
                       command)
              _ (when schedulable? (vswap! (:pending rt) assoc key merged))
              rank (case (:op command)
                     :host 1000000000
                     :release-obligation 1000000001
                     (get @(:ranks rt) (first (:run command)) 0))
              entry [rank (vswap! (:sequence rt) inc)
                     (if schedulable? {:op :scheduled :key key} command)]]
          (when-not previous
            #?(:clj (.add ^java.util.PriorityQueue (:ready rt) entry)
               :cljs (.push (:ready rt) entry))))))))

(defn- poll! [rt]
  (with-gate rt
    (fn []
      (when-let [entry #?(:clj (.poll ^java.util.PriorityQueue (:ready rt))
                          :cljs (when (pos? (.-length (:ready rt)))
                                  (.sort (:ready rt) compare-entry)
                                  (.shift (:ready rt))))]
        (let [command (nth entry 2)]
          (if (= :scheduled (:op command))
            (let [pending (get @(:pending rt) (:key command))]
              (vswap! (:pending rt) dissoc (:key command))
              pending)
            command))))))

(defn- pending? [rt]
  (with-gate rt #(pos? #?(:clj (.size ^java.util.PriorityQueue (:ready rt))
                          :cljs (.-length (:ready rt))))))

(defn- accept! [rt action install!]
  ;; Publish executable state and scheduler commands together. Polling holds
  ;; this gate too; user code is invoked only after the gate is released.
  (with-gate rt
    (fn []
      (let [result (kernel/step! (:kernel rt) action)
            commands (:commands result)]
        (doseq [{:keys [op world e]} commands :when (= :release-entity op)]
          (swap! (:bodies rt) dissoc [world e])
          (swap! (:ranks rt) dissoc e))
        (when install! (install! (:result result)))
        (submit! rt (remove #(= :release-entity (:op %)) commands))
        (:result result)))))

(defn- step! [rt action] (accept! rt action nil))

(defn- query [rt w table id] (kernel/query-row (:kernel rt) w table id))
(defn- field [rt w table id key] (kernel/query-field (:kernel rt) w table id key))
(defn- queued? [rt] (seq (:queue (query rt [:w 0] :header :world))))

(declare drain! execute! track-effect! await-effect!)

(defn signal [rt id value]
  (step! rt (cond-> {:t :t02 :w *world* :e id :value value}
              *run* (assoc :r *run* :order (vswap! *order* inc))))
  {:id id :world *world*})

(defn make-spin [rt id body]
  (let [token [:handle (random-uuid)]]
    (step! rt (cond-> {:t :t01 :w *world* :e id :tok token}
                *run* (assoc :r *run* :order (vswap! *order* inc))))
    {:id id :token token :world *world* :body body}))

(defn track [& _] (throw (ex-info "track requires kspin" {})))
(defn await [& _] (throw (ex-info "await requires kspin" {})))

#?(:clj
   (do
     (defn bp-track [_ r e]
       (fn [args] `(track-effect! ~@args ~r ~e)))
     (defn bp-await [_ r e]
       (fn [args] `(await-effect! ~@args ~r ~e)))
     (defmacro kspin [rt id & body]
       `(make-spin ~rt ~id
                   ~(compiler/build-cps-fn
                     body
                     (merge cps/breakpoints
                            {'org.replikativ.spindel.kernel-runtime/track
                             'org.replikativ.spindel.kernel-runtime/bp-track
                             'org.replikativ.spindel.kernel-runtime/await
                             'org.replikativ.spindel.kernel-runtime/bp-await})
                     &env)))))

(defn- rank-dependency! [rt spin debtor]
  (let [rank (inc (get @(:ranks rt) debtor 0))]
    (swap! (:ranks rt) update spin #(max (or % 0) rank))))

(defn track-effect! [source resolve reject]
  (let [rt *runtime*
        order (vswap! *order* inc)
        value (field rt (:world source) :entities (:id source) :result)
        cont {:resolve resolve :reject reject :kind :track :source source
              :order order :last value}]
    (rank-dependency! rt (first *run*) (:id source))
    (step! rt {:t :t05 :w *world* :r *run* :kind :track
               :debtor [:entity (:world source) (:id source)] :order order :cont cont})
    (cps/invoke-continuation resolve (iv/->Interval value value nil))))

(defn await-effect! [source resolve reject]
  (let [rt *runtime*
        world (:world source)
        child (:id source)
        ;; Public Spin handles expose reactive identity even before their
        ;; first body runs. Deferred/mailbox one-shot support comes separately.
        kind :await-reactive
        order (vswap! *order* inc)
        cont {:resolve resolve :reject reject :kind kind :source source :order order}
        result (accept! rt {:t :await :w *world* :r *run* :kind kind
                            :debtor [:entity world child] :tok (:token source)
                            :order order :cont cont}
                        (fn [_] (swap! (:bodies rt) assoc [world child] (:body source))))]
    (rank-dependency! rt (first *run*) child)
    (if (:inline? result) (deliver-continuation cont (:value result)) ::parked)))

(defn- invoke-slice! [rt world run order f]
  (binding [*runtime* rt *world* world *run* run *order* (volatile! order)
            cps/*in-trampoline* false]
    (f)))

(defn- execute! [rt {:keys [op world run spin o value cont obligation] :as command}]
  (case op
    :host (when-let [{:keys [success failure]}
                     (with-gate rt
                       (fn []
                         (let [callback (get @(:callbacks rt) [world o])]
                           (when-not (query rt world :obligations o)
                             (swap! (:callbacks rt) dissoc [world o]))
                           callback)))]
            (cond
              (= ::kernel/cancelled value) (failure (ex-info "Cancelled" {:error :cancelled}))
              (failed? value) (failure (:error value))
              :else (success value)))
    :release-obligation (swap! (:callbacks rt) dissoc [world o])
    (:start :resume :reactive-resume)
    (when (= :running (field rt world :runs run :status))
      (case op
        :start
        (invoke-slice!
         rt world run -1
         #((get @(:bodies rt) [world spin])
           (fn [value] (step! rt {:t :t07 :w *world* :r *run* :value value}))
           (fn [error] (step! rt {:t :t07 :w *world* :r *run* :value (->Failure error)}))))
        :resume
        (do
          (when-let [source (:source cont)]
            (rank-dependency! rt (first run) (:id source)))
          (invoke-slice! rt world run (:order cont)
                         #(deliver-continuation cont value)))
        :reactive-resume
        (let [cont (:cont obligation)
              source (:source cont)
              value (field rt (:world source) :entities (:id source) :result)
              moved? (= [:run world run] (field rt world :obligations o :creditor))]
          (rank-dependency! rt (first run) (:id source))
          (invoke-slice!
           rt world run (:order cont)
           (fn []
             (if (= :track (:kind obligation))
               (do
                 (when-not moved?
                   (step! rt {:t :t05 :w world :r run :kind :track
                              :debtor (:debtor obligation) :order (:order cont)
                              :cont (assoc cont :last value)}))
                 (cps/invoke-continuation (:resolve cont) (iv/->Interval (:last cont) value nil)))
               (let [result (step! rt {:t :await :w world :r run :kind (:kind obligation)
                                       :debtor (:debtor obligation) :order (:order cont) :cont cont})]
                 (when (:inline? result) (deliver-continuation cont (:value result))))))))))))

(defn drain! [rt]
  (when (compare-and-set! (:draining rt) false true)
    (try
      (loop []
        (cond
          (queued? rt) (do (step! rt {:t :queued :w [:w 0]}) (recur))
          :else (when-let [command (poll! rt)]
                  (execute! rt command)
                  (recur))))
      (finally (reset! (:draining rt) false)))
    (when (or (pending? rt) (queued? rt)) (drain! rt))))

(defn observe! [rt spin success failure]
  (let [{:keys [world o]} (accept!
                           rt {:t :t04 :w (:world spin) :e (:id spin)
                               :tok (:token spin) :mode :callback}
                           (fn [{:keys [world o]}]
                             (swap! (:bodies rt) assoc [world (:id spin)] (:body spin))
                             (swap! (:callbacks rt) assoc [world o]
                                    {:success success :failure failure})))]
    (drain! rt)
    (fn [] (step! rt {:t :unsubscribe :w world :o o}) (drain! rt))))

(defn release-idle! [rt]
  (step! rt {:t :t18 :w [:w 0]})
  (drain! rt))

(defn set-signal! [rt source value]
  (step! rt {:t :signal-write :w (:world source) :e (:id source) :value value})
  (drain! rt))
