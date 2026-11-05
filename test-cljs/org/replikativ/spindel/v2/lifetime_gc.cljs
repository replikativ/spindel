(ns org.replikativ.spindel.v2.lifetime-gc
  "Run compiled Node artifact with --expose-gc. Real GC supplements finite tests."
  (:require [org.replikativ.spindel.v2.core :as v2 :refer [task]]
            [org.replikativ.spindel.v2.host :as hs]
            [org.replikativ.spindel.v2.rows :as rw]))

(defn- until [label ready next]
  (letfn [(step [n]
            ;; Collect before dereferencing WeakRefs: deref keeps a surviving
            ;; target alive for the rest of this JavaScript job.
            (js/gc)
            (cond (ready) (do (println "PASS" label) (next))
                  (>= n 200) (do (println "FAIL" label) (js/process.exit 1))
                  :else (js/setTimeout #(step (inc n)) 10)))]
    ;; WeakRef keeps a newly observed target alive until the end of this job.
    (js/setTimeout #(step 0) 0)))

(defn- self-watches [w]
  (binding [v2/*world* w]
    (let [a (v2/atom :value) s (v2/signal :value)]
      (add-watch a :self (fn [_ _ _ _] (meta a)))
      (add-watch s :self (fn [_ _ _ _] (v2/handle? s)))
      [(hs/weak a) (hs/weak s)])))

(defn- watch-cycles [verify? next]
  (let [w (v2/world {:verify? verify?}) refs (self-watches w)]
    (until (str "self-capturing watches, verify=" verify?)
           #(and (every? (comp nil? hs/deref-weak) refs)
                 (empty? (aget w rw/W-ATOMS))
                 (zero? (hs/msize (aget w rw/W-WATCHES))))
           #(do (v2/release-world! w) (next)))))

(defn- fork-atoms [p]
  (binding [v2/*world* p]
    (let [a (v2/atom :a) b (v2/atom :b)]
      {:refs [(hs/weak a) (hs/weak b)] :worlds [(v2/fork! p) (v2/fork! p)]})))

(defn- idle-forks [next]
  (let [p (v2/world) {:keys [refs worlds]} (fork-atoms p)]
    (until "dead atoms pruned in idle forks"
           #(and (every? (comp nil? hs/deref-weak) refs)
                 (every? (fn [w] (empty? (aget w rw/W-ATOMS))) (cons p worlds)))
           #(do (doseq [w worlds] (v2/release-world! w)) (v2/release-world! p) (next)))))

(defn- foreign-world [p s]
  (let [c (v2/fork! p)]
    (binding [v2/*world* c]
      (task (add-watch s :foreign (fn [_ _ _ _]))))
    (hs/weak c)))

(defn- foreign-ownership [next]
  (let [p (v2/world) s (binding [v2/*world* p] (v2/signal 0))
        wc (foreign-world p s)
        owner (:foreign-owner (aget (.-cell s) 2))]
    (assert (= 1 (hs/msize (:capsules owner))))
    (until "live invoking Handle releases dead foreign-world watches"
           #(and (nil? (hs/deref-weak wc))
                 (zero? (hs/msize (:capsules owner)))
                 (= 1 (hs/msize (:worlds (aget p rw/W-FAMILY)))))
           #(do (assert (v2/handle? s)) (v2/release-world! p) (next)))))

(defn- empty-tokens [w]
  (binding [v2/*world* w]
    (dotimes [_ 1000] (v2/signal 0))))

(defn- token-churn [next]
  (let [w (v2/world)]
    (empty-tokens w)
    (until "empty source-token index has no churn history"
           #(zero? (hs/msize (aget w rw/W-WATCHES)))
           #(do (v2/release-world! w) (next)))))

(defn- alias-fixture [w]
  (let [s (binding [v2/*world* w] (v2/signal 0))
        seen (atom [])]
    (add-watch s :k (fn [_ _ _ n] (swap! seen conj n)))
    {:alias (v2/in-world w s) :original (hs/weak s) :seen seen}))

(defn- surviving-alias [next]
  (let [w (v2/world {:verify? true}) {:keys [alias original seen]} (alias-fixture w)]
    (until "surviving alias preserves watches"
           #(nil? (hs/deref-weak original))
           #(do (reset! alias 1) (assert (= [1] @seen))
                (remove-watch alias :k) (v2/release-world! w) (next)))))

(defn- isolated-child [p]
  (let [s (binding [v2/*world* p] (v2/signal :value))
        c (v2/fork! p)]
    (add-watch s :self (fn [& _] (v2/handle? s)))
    {:child c :alias (v2/in-world c s) :parent-source (hs/weak s)}))

(defn- parent-isolation [next]
  (let [p (v2/world) {:keys [child alias parent-source]} (isolated-child p)]
    (until "child alias does not retain parent watch cycle"
           #(nil? (hs/deref-weak parent-source))
           #(do (assert (= :value (v2/value alias)))
                (v2/release-world! child) (v2/release-world! p) (next)))))

(defn- neutral-fixture [p]
  (let [s (binding [v2/*world* p] (v2/signal :value))]
    (add-watch s :self (fn [& _] (v2/handle? s)))
    {:ref (v2/world-ref s) :source (hs/weak s)}))

(defn- neutral-reference [next]
  (let [p (v2/world) {:keys [ref source]} (neutral-fixture p)]
    (until "world-neutral reference releases source watch cycle"
           #(nil? (hs/deref-weak source))
           #(do (assert (= :value (v2/value (v2/resolve-ref p ref))))
                (v2/release-world! p) (next)))))

(defn -main []
  (when-not (exists? js/gc) (throw (js/Error. "Run node with --expose-gc")))
  (let [done (fn [] (println "LIFETIME GC OK"))
        neutral (fn [] (neutral-reference done))
        isolated (fn [] (parent-isolation neutral))
        alias (fn [] (surviving-alias isolated))
        churn (fn [] (token-churn alias))
        foreign (fn [] (foreign-ownership churn))
        forks (fn [] (idle-forks foreign))]
    (watch-cycles false (fn [] (watch-cycles true forks)))))

(set! *main-cli-fn* -main)
