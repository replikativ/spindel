(ns org.replikativ.spindel.v2.api-test
  "M6 phase A: host calls, world state, refs, atoms (.internal/m6-phase-a-design.md v2)."
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.v2.core :as v2 :refer [spin task track await]]
            [org.replikativ.spindel.v2.verify :as verify]
            [org.replikativ.spindel.incremental.interval :as iv]))

(def ^:dynamic *divergences* nil)

(defn- vworld []
  (v2/world {:verify? true :hook (verify/checking-hook *divergences*)}))

(defmacro checked [& body]
  `(binding [*divergences* (atom [])]
     ~@body
     (is (empty? @*divergences*) (str "Rule R divergences: " (vec (take 3 @*divergences*))))))

(defn- outcome [h]
  (try [:ok (v2/value h 1000 ::timeout)] (catch Exception e [:err (ex-data e)])))

(defn- wait-until [f]
  (loop [n 0] (cond (f) true (> n 500) false :else (do (Thread/sleep 5) (recur (inc n))))))

;; --- R5 host-call! / send-world!, R7 value guard

(deftest host-call-returns-and-guards
  (checked
   (let [w (vworld) other (vworld)]
     (binding [v2/*world* w]
       (is (= 42 (v2/host-call! w (fn [] 42))) "a host item's value")
       (is (= [:ok :inside] (outcome (task (v2/host-call! (v2/current-world) (fn [] :inside)))))
           "inside its own world it runs at once")
       (is (= :host-call
              (:spindel/invalid (second (outcome (task (v2/host-call! other (fn [] 1)))))))
           "waiting on another world from a body is refused (B7)")
       (let [x (v2/signal other 0)]
         (is (= [:ok nil] (outcome (task (v2/send-world! other #(v2/write! x 7))))))
         (is (wait-until #(= 7 (v2/value x))) "send-world! enqueues and the item runs later"))))))

(deftest value-in-a-callback-is-refused
  (checked
   (let [w (vworld) seen (promise)]
     (binding [v2/*world* w]
       (let [x (v2/signal 1)
             c (spin (* 2 (iv/get-new (track x))))]
         (v2/observe! c (fn [_ _] (deliver seen (try (v2/value x) :read (catch Exception e (ex-message e))))))
         (is (re-find #"processing a world" (str (deref seen 1000 nil)))))))))

;; --- R1 world state and refs

(deftest world-state-forks-by-value
  (checked
   (let [w (vworld)]
     (v2/assoc-in-world! w [:room :name] "a")
     (is (= {:room {:name "a"}} (v2/world-state w)))
     (let [c (v2/fork! w)]
       (v2/assoc-in-world! c [:room :name] "b")
       (is (= "a" (v2/get-in-world w [:room :name])) "the parent is unchanged")
       (is (= "b" (v2/get-in-world c [:room :name])) "the child has its own")
       (v2/update-in-world! w [:n] (fnil inc 0))
       (is (nil? (v2/get-in-world c [:n])) "no write propagates after the fork")))))

(deftest world-state-refuses-handles-and-resolves-refs
  (checked
   (let [w (vworld)]
     (binding [v2/*world* w]
       (let [x (v2/signal 1)]
         (is (= :world-state (:spindel/invalid (try (v2/assoc-in-world! w [:x] x) nil
                                                    (catch Exception e (ex-data e))))))
         (v2/assoc-in-world! w [:x] (v2/world-ref x))
         (let [c (v2/fork! w)
               cx (v2/resolve-ref c (v2/get-in-world c [:x]))]
           (v2/write! cx 2)
           (is (= 2 (v2/value cx)) "the ref resolves to the child's copy")
           (is (= 1 (v2/value (v2/resolve-ref w (v2/get-in-world w [:x])))) "the parent's is unchanged")))))))

(deftest world-state-in-a-body-acts-on-the-slice-world
  (checked
   (let [w (vworld)]
     (binding [v2/*world* w]
       (let [t (task (v2/swap-world! (v2/current-world) assoc :from :task) :done)]
         (is (= [:ok :done] (outcome t)))
         (is (= :task (v2/get-in-world w [:from]))))))))

;; --- R6 atoms

(deftest atoms-have-atom-semantics
  (checked
   (let [w (vworld)]
     (binding [v2/*world* w]
       (let [a (v2/atom 0)]
         (is (= 1 (swap! a inc)))
         (is (= 11 (swap! a + 10)))
         (is (= 0 (reset! a 0)))
         (is (true? (compare-and-set! a 0 5)))
         (is (false? (compare-and-set! a 0 6)))
         (is (= [5 6] (swap-vals! a inc)))
         (is (= 6 @a)))))))

(deftest atoms-are-fork-safe
  (checked
   (let [w (vworld)]
     (binding [v2/*world* w]
       (let [a (v2/atom :parent)
             c (v2/fork! w)]
         (binding [v2/*world* c]
           (reset! a :child)
           (is (= :child @a)))
         (is (= :parent @a) "the parent keeps its value")
         (let [b (v2/atom 1)]
           (binding [v2/*world* c]
             (is (= 1 (:spindel/missing-state-id
                       (try @b nil (catch Exception e {:spindel/missing-state-id (if (:spindel/missing-state (ex-data e)) 1 0)}))))
                 "an atom made after the fork has no state in the child"))))))))

(deftest atoms-in-a-forked-body
  ;; the body copied into a fork acts on the fork's atom value
  (checked
   (let [w (vworld)]
     (binding [v2/*world* w]
       (let [a (v2/atom 0)
             out (promise)
             gate (v2/deferred)
             t (task (let [[side child] (v2/fork)]
                       (swap! a + (if (= side :child) 100 1))
                       (when (= side :parent) (deliver out child) (await gate))
                       @a))
             child (deref out 1000 nil)]
         (is (= [:ok 100] (outcome (v2/in-world child t))) "the child's copy")
         (v2/deliver! gate :go)
         (is (= [:ok 1] (outcome t)) "the parent's own"))))))

;; --- R8 signal reset!/swap!, invokable deferreds and mailboxes, semaphore parity

(deftest signals-reset-and-swap
  (checked
   (let [w (vworld)]
     (binding [v2/*world* w]
       (let [x (v2/signal 1)
             c (spin (* 10 (iv/get-new (track x))))
             seen (atom [])]
         (v2/observe! c (fn [v _] (swap! seen conj v)))
         (is (= 5 (reset! x 5)))
         (is (= 6 (swap! x inc)))
         (is (= 8 (swap! x + 2)))
         (is (true? (compare-and-set! x 8 9)))
         (is (false? (compare-and-set! x 8 10)))
         (is (= 9 @x))
         (is (= [10 50 60 80 90] @seen) "every write is a T2 with its delivery")
         (is (= :swap (:spindel/invalid (try (swap! (v2/deferred) inc) nil (catch Exception e (ex-data e)))))
             "swap! is for signals and cells"))))))

(deftest invokable-deferreds-and-mailboxes
  (checked
   (let [w (vworld)]
     (binding [v2/*world* w]
       (let [d (v2/deferred) mb (v2/mailbox)
             t (task [(await d) (v2/take! mb)])]
         (is (true? (d :first)) "the first delivery wins")
         (is (false? (d :second)) "later ones do not")
         (is (nil? (mb :msg)))
         (is (= [:ok [:first :msg]] (outcome t))))))))

(deftest semaphores-have-a-maximum
  ;; Z#62: (semaphore n) starts with n permits and never exceeds n
  (checked
   (let [w (vworld)]
     (binding [v2/*world* w]
       (let [s (v2/semaphore 1)]
         (is (= [:ok :acquired] (outcome (task (v2/acquire! s)))))
         (v2/sem-release! s)
         (v2/sem-release! s)                         ; at the maximum: refused
         (is (= [:ok :acquired] (outcome (task (v2/acquire! s)))))
         (is (= :pending (v2/value (task (v2/acquire! s)) 100 :pending))
             "only one permit existed, so a third acquire waits"))))))

;; --- R2 external waits

(defn- census [w]
  (v2/call-in! w #(frequencies (map (fn [r] (aget ^objects r org.replikativ.spindel.v2.rows/TYPE))
                                    (vals (aget ^objects w org.replikativ.spindel.v2.rows/W-REG))))))

(defn- runs-and-res [w]
  (let [c (census w)]
    [(get c org.replikativ.spindel.v2.rows/T-RUN 0) (get c org.replikativ.spindel.v2.rows/T-RES 0)]))

(deftest external-completes-from-any-thread
  (checked
   (let [w (vworld) cb (promise)]
     (binding [v2/*world* w]
       (let [t (task (inc (v2/external (fn [complete!] (deliver cb complete!) nil))))
             complete! (deref cb 1000 nil)]
         @(future (complete! 41))
         (complete! 99)                                      ; a second completion does nothing
         (is (= [:ok 42] (outcome t)))
         (is (wait-until #(= [0 0] (runs-and-res w))) "joined and retired"))))))

(deftest external-errors-and-throws
  (checked
   (let [w (vworld) cb (promise)]
     (binding [v2/*world* w]
       (let [t (task (v2/external (fn [complete!] (deliver cb complete!) nil)))]
         ((deref cb 1000 nil) (ex-info "io failed" {:io true}) true)
         (is (= [:err {:io true}] (outcome t))))
       (is (= [:err {:reg true}]
              (outcome (task (v2/external (fn [_] (throw (ex-info "no" {:reg true})))))))
           "a throwing registration fails the effect")))))

(deftest external-cancel-protocol
  (checked
   (let [w (vworld) cancels (atom []) cbs (atom [])]
     (binding [v2/*world* w]
       (testing ":joined from the cancel fn joins at once"
         (let [t (task (v2/external (fn [c] (swap! cbs conj c) (fn [] (swap! cancels conj :a) :joined))))]
           (is (wait-until #(= 1 (count @cbs))))
           (v2/cancel-task! t)
           (is (= [:a] @cancels))
           (is (wait-until #(= [0 0] (runs-and-res w))) "joined without a completion")
           ((first @cbs) :late)                              ; a completion after joining does nothing
           (is (:spindel/cancelled (second (outcome t))))))
       (testing "otherwise the physical completion joins"
         (let [t (task (v2/external (fn [c] (swap! cbs conj c) (fn [] (swap! cancels conj :b) :in-flight))))]
           (is (wait-until #(= 2 (count @cbs))))
           (v2/cancel-task! t)
           (Thread/sleep 20)
           (is (= [1 1] (runs-and-res w)) "the run waits in cleanup for the in-flight operation")
           ((second @cbs) :done)
           (is (wait-until #(= [0 0] (runs-and-res w))) "the completion joined it")))))))

(deftest external-in-a-fork-is-dormant
  ;; §8.1: an inherited external wait fails with ::forked in the child; the
  ;; child's copy holds no controller of the parent (F1)
  (checked
   (let [w (vworld) cb (promise)]
     (binding [v2/*world* w]
       (let [t (task (try (v2/external (fn [c] (deliver cb c) nil))
                          (catch Exception e (if (:spindel/forked (ex-data e)) :forked (throw e)))))
             complete! (deref cb 1000 nil)
             c (v2/fork! w)]
         (is (= [:ok :forked] (outcome (v2/in-world c t))))
         (complete! :parent-value)
         (is (= [:ok :parent-value] (outcome t)) "the parent's completion is its own"))))))

;; --- R3 custom effects

(v2/defeffect choose [[options] ctx]
  [:value (first options)])

(v2/defeffect fail-with [[msg] _]
  [:error (ex-info msg {:custom true})])

(v2/defeffect later [[v] _]
  [:external (fn [complete!] (future (complete! v)) nil)])

(v2/defeffect ask [[q] _]
  [:savepoint :ask q])

(v2/defeffect where [_ ctx]
  [:value (select-keys ctx [:effect :site])])

(deftest custom-effects-return-ops
  (checked
   (let [w (vworld) pubs (atom [])]
     (v2/install-handlers! w {:ask (fn [p] (swap! pubs conj p))})
     (binding [v2/*world* w]
       (is (= [:ok :a] (outcome (task (choose [:a :b])))) "[:value v]")
       (is (= [:err {:custom true}] (outcome (task (fail-with "boom")))) "[:error e]")
       (is (= [:ok 7] (outcome (task (later 7)))) "[:external f]")
       (let [t (task (inc (ask 41)))]
         (is (wait-until #(seq @pubs)))
         (is (= 41 (:payload (first @pubs))) "[:savepoint site payload]")
         (v2/resume! (first @pubs) 41)
         (is (= [:ok 42] (outcome t))))
       (testing "ctx carries the effect and a site stable per call site"
         (let [f (fn [] (task [(where) (where)]))
               [[a b]] [(second (outcome (f)))]
               [[c _]] [(second (outcome (f)))]]
           (is (= `where (:effect a)))
           (is (not= (:site a) (:site b)) "two call sites")
           (is (= (:site a) (:site c)) "the same call site in another run")))))))
