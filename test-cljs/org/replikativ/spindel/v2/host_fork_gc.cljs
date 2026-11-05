(ns org.replikativ.spindel.v2.host-fork-gc
  (:require [org.replikativ.spindel.v2.core :as v2]
            [org.replikativ.spindel.v2.host :as hs]
            [org.replikativ.spindel.v2.rows :as rw]
            [org.replikativ.spindel.v2.lifetime :as lt]))
(defn- pump! [jobs]
  (with-redefs [hs/execute! (fn [_ f] (swap! jobs conj f))]
    (loop [n 10000] (when-let [f (first @jobs)] (assert (pos? n)) (swap! jobs subvec 1) (f) (recur (dec n))))))
(defn- until [label ready next]
  (letfn [(check [n]
            (js/gc)
            (cond (ready) (do (println "PASS" label) (next))
                  (= n 200) (throw (ex-info "host fork GC failed" {:probe label}))
                  :else (js/setTimeout #(check (inc n)) 10)))]
    (js/setTimeout #(check 0) 0)))
(defn- canceled-fixture [kind]
  (let [p (v2/world {:inline? (= kind :preclaim) :budget 1}) jobs (atom []) weak (atom nil) held (atom nil)
        turn-error (ex-info "preclaim turn error" {})
        original v2/prepare-host-entry! rank @v2/world-order epoch (aget p rw/W-EPOCH) next-id (v2/peek-id p)]
    (with-redefs [hs/execute! (fn [_ f] (swap! jobs conj f))
                  v2/prepare-host-entry! (fn [entry f reject intent]
                                           (reset! weak (hs/weak f)) (reset! held entry)
                                           (original entry f reject intent))]
      (when (= kind :preclaim) (v2/send-world! p #(throw turn-error)))
      (try (v2/fork! p) (throw (ex-info "expected control refusal" {}))
           (catch :default error
             (assert (if (= kind :preclaim) (identical? turn-error error)
                         (= :world-control (:spindel/invalid (ex-data error))))))))
    {:p p :jobs jobs :weak @weak :entry @held :rank rank :epoch epoch :next-id next-id}))
(defn- canceled-allocation [kinds next]
  (if-let [kind (first kinds)]
    (let [{:keys [p jobs weak entry rank epoch next-id]} (canceled-fixture kind)]
      (until (str "held canceled " (name kind) " entry releases allocation closure before pump")
             #(nil? (hs/deref-weak weak))
             #(do
                (assert (= {:phase :canceled} @(.-state entry)))
                (assert (seq @jobs)) (pump! jobs)
                (assert (= rank @v2/world-order)) (assert (= next-id (v2/peek-id p)))
                (assert (identical? epoch (aget p rw/W-EPOCH)))
                (assert (nil? (aget p rw/W-OWNED)))
                (v2/release-world! p) (pump! jobs)
                (canceled-allocation (rest kinds) next))))
    (next)))
(defn- closed-child-fixture []
  (let [p (v2/world) c (v2/fork! p) jobs (atom []) payload (js/Uint8Array. (* 1024 1024))
        world (hs/weak c) private (hs/weak payload)]
    (v2/reset-world! c {:payload payload})
    (with-redefs [hs/execute! (fn [_ f] (swap! jobs conj f))] (v2/release-world! c))
    (pump! jobs)
    {:p p :world world :private private}))
(defn- closed-child [next]
  (let [{:keys [p world private]} (closed-child-fixture)]
    (until "live parent releases terminal fork and private payload"
           #(and (nil? (hs/deref-weak world)) (nil? (hs/deref-weak private)))
           #(do (assert (not (:requested? (v2/world-close-status p))))
                (v2/release-world! p) (next)))))
(defn- fixed-frontier [next]
  (let [p (v2/world) jobs (atom [])]
    (with-redefs [hs/execute! (fn [_ f] (swap! jobs conj f))]
      (dotimes [_ 1000] (v2/release-world! (v2/fork! p)) (pump! jobs)))
    (until "1000 fork/close cycles keep only the live parent and bounded weak holders"
           #(= 1 (:worlds (lt/census (aget p rw/W-FAMILY) (aget p rw/W-WATCHES) nil)))
           #(do
              (assert (<= (reduce + 0 (map (fn [e] (.-length (aget e 0))) (hs/mvals (aget p rw/W-OWNED)))) 16))
              (assert (zero? (.-length (aget p rw/W-AFTER))))
              (assert (zero? (.-length (aget p rw/W-CALLBACKS))))
              (v2/release-world! p) (next)))))
(defn- refused-frontier [next]
  (let [p (v2/world {:inline? false}) jobs (atom []) rank @v2/world-order next-id (v2/peek-id p)]
    (with-redefs [hs/execute! (fn [_ f] (swap! jobs conj f))]
      (dotimes [_ 1000]
        (try (v2/fork! p) (throw (ex-info "expected synchronous refusal" {}))
             (catch :default error (assert (= :world-control (:spindel/invalid (ex-data error))))))
        (pump! jobs)))
    (until "1000 refused controls leave no allocation or metadata/queue history"
           #(= 1 (:worlds (lt/census (aget p rw/W-FAMILY) (aget p rw/W-WATCHES) nil)))
           #(do
              (assert (= rank @v2/world-order))
              (assert (= next-id (v2/peek-id p)))
              (assert (nil? (aget p rw/W-OWNED)))
              (assert (hs/mpsc-empty? (aget p rw/W-INGRESS)))
              (assert (zero? (.-length (aget p rw/W-AFTER))))
              (assert (zero? (hs/msize (aget p rw/W-WATCHES))))
              (v2/release-world! p) (pump! jobs) (next)))))

(defn -main []
  (assert (and (exists? js/gc) (exists? js/WeakRef)))
  (canceled-allocation [:unsupported :preclaim] #(closed-child (fn [] (fixed-frontier (fn [] (refused-frontier (fn [] (println "HOST FORK GC OK")))))))))
(set! *main-cli-fn* -main)
