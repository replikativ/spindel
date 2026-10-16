(ns org.replikativ.spindel.statemachine.model
  "Data-driven, acyclic spin programs. Templates keep every effect lexical.
   Traces contain public values only, never runtime addresses or registrations."
  (:refer-clojure :exclude [await])
  (:require [is.simm.partial-cps.async :as cps]
            [org.replikativ.spindel.effects.await :refer [await]]
            [org.replikativ.spindel.effects.track :refer [track]]
            [org.replikativ.spindel.engine.context :as ctx]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.executor :as ex]
            [org.replikativ.spindel.engine.impl.simple :as simple]
            [org.replikativ.spindel.engine.protocols :as rtp]
            [org.replikativ.spindel.incremental.interval :as iv]
            [org.replikativ.spindel.signal :as sig]
            [org.replikativ.spindel.spin.core :as sc]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.test-async :refer [await-drain]]))

(defn plain [v] (if (sequential? v) (mapv plain v) v))

(defn observe! [trace site interval]
  (swap! trace conj {:site site :old (plain (:old interval))
                     :new (plain (:new interval)) :deltas (:deltas interval)})
  (plain (iv/get-new interval)))

(defn emit! [log site value]
  (swap! log conj [site value])
  value)

(defn build-spin [signals spins trace log id {:keys [kind a b dep] :as _description}]
  (let [sa (nth signals (or a 0))
        sb (nth signals (or b 1))
        sv (nth signals 2)
        child (when (some? dep) (nth spins dep))]
    (case kind
      :track (spin (emit! log id (observe! trace [id :a] (track sa))))
      :pair (spin (let [ia (track sa)
                        va (observe! trace [id :a] ia)
                        vb (observe! trace [id :b] (track sb))]
                    (emit! log id [va vb])))
      :repeat (spin (let [va (observe! trace [id :a] (track sa))
                          vb (observe! trace [id :again] (track sa))]
                      (emit! log id [va vb])))
      :branch (spin (let [v (observe! trace [id :a] (track sa))]
                      (emit! log id (if (even? v)
                                      (observe! trace [id :b] (track sb)) v))))
      :throw (spin (let [v (observe! trace [id :a] (track sa))]
                     (when (neg? v) (throw (ex-info (str "generated negative " v) {:value v})))
                     (emit! log id [v (observe! trace [id :b] (track sb))])))
      :await (spin (emit! log id (await child)))
      :vector-await (spin (let [v (observe! trace [id :vector] (track sv))]
                            (emit! log id [v (await child)])))
      :child (spin (let [v (observe! trace [id :vector] (track sv))
                         c (spin (observe! trace [id :child] (track sb)))]
                     (emit! log id [v (await c)])))
      :reentrant (spin (let [v (observe! trace [id :a] (track sa))]
                         ;; Idempotent target: no self-triggering infinite loop.
                         (when (= v 7) (reset! sb 11))
                         (emit! log id v))))))

(defn start! [s]
  (binding [cps/*in-trampoline* false]
    (try @s (catch clojure.lang.ExceptionInfo _ nil))))

(defn cached [rt s]
  (let [r (rtp/get-state rt [:nodes (sc/spin-id s) :result])]
    (cond
      (nil? r) [:missing]
      (sc/ok? r) [:ok (plain (:payload r))]
      :else [:error (.getMessage ^Throwable (:payload r))])))

(defn mutate! [signals [op n v]]
  (case op
    :set (reset! (nth signals n) v)
    :conj (swap! (nth signals 2) conj v)
    :assoc (swap! (nth signals 2) #(assoc % (if (seq %) (mod n (count %)) 0) v))
    :pop (swap! (nth signals 2) #(if (seq %) (pop %) %))))

(defn queued! [rt f]
  ;; Queue real FIFO events without letting the inline executor drain each swap.
  ;; All callers have quiesced first; this test-only var redefinition is serial.
  (with-redefs [simple/trigger-drain! (fn [& _])]
    (f))
  (simple/trigger-drain! rt (:executor rt))
  (await-drain rt))

(defn run-program
  ([program schedule] (run-program program schedule :sync [0 0 []]))
  ([program schedule executor initial]
   (let [rt (ctx/create-execution-context
             :executor (if (= executor :sync) (ex/synchronous-executor) (ex/default-executor)))
         trace (atom []) log (atom []) steps (atom [])]
     (try
       (binding [ec/*execution-context* rt]
         (let [signals (mapv (fn [v] (sig/signal v)) initial)
               spins (reduce (fn [ss [id d]]
                               (conj ss (build-spin signals ss trace log id d)))
                             [] (map-indexed vector program))]
           ;; Start in reverse order: awaits see both uncached and cached children.
           (doseq [s (reverse spins)] (start! s))
           (await-drain rt)
           (let [active
                 (reduce
                  (fn [current [op arg :as operation]]
                    (let [before (count @log)
                          next-context
                          (binding [ec/*execution-context* current]
                            (if (= op :fork)
                              ;; Continue only this branch. The parent stays quiescent;
                              ;; external log atoms intentionally record the branch taken.
                              (ctx/fork-context current :mode arg)
                              (do
                                (case op
                                  :drain (await-drain current)
                                  :queue (queued! current #(doseq [mutation arg]
                                                             (mutate! signals mutation)))
                                  :cancel (let [i (mod arg (count spins))]
                                            (sc/cancel-spin! (nth spins i))
                                            (await-drain current))
                                  (do (mutate! signals operation) (await-drain current)))
                                current)))]
                      (swap! steps conj {:operation operation :emits (subvec @log before)})
                      next-context))
                  rt schedule)]
             (binding [ec/*execution-context* active]
               (await-drain active)
               {:values (mapv #(cached active %) spins)
                :cancelled (into #{}
                                 (keep-indexed (fn [i s] (when (sc/spin-cancelled? s) i)) spins))
                :signals (mapv #(plain @%) signals)
                :trace @trace :log @log :steps @steps}))))
       (finally (ctx/close-context! rt))))))

(defn consistent? [program result]
  (let [fresh (run-program program [] :sync (:signals result))]
    (every? (fn [i] (or (contains? (:cancelled result) i)
                        (= (nth (:values result) i) (nth (:values fresh) i))))
            (range (count program)))))

(defn apply-delta [v {:keys [delta path value old-value]}]
  (let [i (first path)]
    (case delta
      :add (do (assert (= i (count v)) "duplicate or out-of-order add") (conj v value))
      :update (do (assert (= old-value (nth v i)) "update baseline mismatch") (assoc v i value))
      :remove (do (assert (= i (dec (count v))) "remove index mismatch")
                  (assert (= old-value (peek v)) "remove baseline mismatch") (pop v)))))

(defn delta-integrity? [trace]
  (every?
   (fn [events]
     (if-not (vector? (:new (first events)))
       true
       (try
         (loop [v (:new (first events)), events (next events)]
           (if-let [e (first events)]
             (let [v' (reduce apply-delta v (:deltas e))]
               (and (= v' (:new e)) (recur v' (next events))))
             true))
         (catch Throwable _ false))))
   (vals (group-by :site trace))))
