(ns org.replikativ.spindel.v2.c2-merge-test
  "C2 (spec Z#74, model PR #288): `seal!`/`unseal!`, `diff`, `merge!` with a
   resolver and the §9 guards, `transfer!` of a root-owned fork, `descendant?`."
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.v2.core :as v2 :refer [task await]]
            [org.replikativ.spindel.v2.rows :as rw]
            [org.replikativ.spindel.v2.verify :as verify]))

(def ^:dynamic *divergences* nil)

(defn- vworld [] (v2/world {:verify? true :hook (verify/checking-hook *divergences*)}))

(defmacro checked [& body]
  `(binding [*divergences* (atom [])]
     ~@body
     (is (empty? @*divergences*) (str "Rule R divergences: " (vec (take 3 @*divergences*))))))

(defn- wait-until [f] (loop [n 400] (or (f) (when (pos? n) (Thread/sleep 5) (recur (dec n))))))

(defn- sealed-refusal [f]
  (try (f) :accepted
       (catch clojure.lang.ExceptionInfo e (if (:spindel/sealed (ex-data e)) :sealed (throw e)))))

(deftest a-sealed-world-refuses-host-changes-and-admissions
  (checked
   (let [w (vworld)]
     (binding [v2/*world* w]
       (let [s (v2/signal 1) d (v2/deferred) m (v2/mailbox) st (v2/stream)
             child (v2/fork! w {:mergeable? true})
             [cs cd cm cst] (map #(v2/in-world child %) [s d m st])]
         (v2/seal! child)
         (is (v2/sealed? child))
         (is (not (v2/sealed? w)) "the parent is not sealed")
         (is (= [:sealed :sealed :sealed :sealed :sealed :sealed]
                [(sealed-refusal #(v2/write! cs 2))
                 (sealed-refusal #(swap! cs inc))
                 (sealed-refusal #(v2/deliver! cd :x))
                 (sealed-refusal #(v2/post! cm :x))
                 (sealed-refusal #(v2/append! cst :x))
                 (sealed-refusal #(v2/observe! cs (fn [_ _])))]))
         (is (= :sealed (sealed-refusal #(binding [v2/*world* child] (task 1)))) "no new host task")
         (is (= 1 (v2/value cs 1000 ::timeout)) "reads are not refused")
         (is (empty? (v2/diff child)))
         (v2/unseal! child)
         (v2/write! cs 2)
         (is (= 2 (v2/value cs 1000 ::timeout)) "unsealed: writes again")
         (v2/write! s 5)
         (is (= 5 (v2/value s)) "the parent was never sealed"))))))

(deftest a-sealed-worlds-bodies-keep-running
  (checked
   (let [w (vworld)]
     (binding [v2/*world* w]
       (let [s (v2/signal 1)
             t (task (v2/sleep 50) (v2/write! s 9) :done)]
         (v2/seal! w)
         (is (= :done (v2/value t 2000 ::timeout)))
         (is (= 9 (v2/value s 1000 ::timeout)) "a body's write after the seal is accepted"))))))

(deftest diff-lists-the-changed-inherited-sources
  (checked
   (let [w (vworld)]
     (binding [v2/*world* w]
       (let [s (v2/signal 1) t (v2/signal 2) u (v2/signal 3)
             child (v2/fork! w {:mergeable? true})]
         (v2/write! (v2/in-world child s) 10)
         (v2/write! (v2/in-world child t) 2)       ; same value: still a change (a version)
         (is (= 3 (v2/value (v2/in-world child u) 1000 ::timeout)) "a read is not a change")
         (binding [v2/*world* child] (v2/signal 7)) ; created in the child: not listed
         (let [d (v2/diff child)]
           (is (= #{{:base 1 :value 10} {:base 2 :value 2}} (set (vals d))))
           (is (= #{10 2} (set (map #(v2/value % 1000 ::timeout) (keys d)))) "keys are the child's handles"))
         (is (nil? (v2/diff (v2/fork! w))) "not mergeable"))))))

(deftest merge-requires-a-sealed-quiescent-child
  (checked
   (let [w (vworld)]
     (binding [v2/*world* w]
       (let [s (v2/signal 1)
             child (v2/fork! w {:mergeable? true})
             cs (v2/in-world child s)]
         (v2/write! cs 10)
         (is (false? (v2/merge! w child)) "unsealed")
         (testing "a run parked on an armed timer (model F2)"
           (let [t (binding [v2/*world* child] (task (v2/sleep 150) (v2/write! cs 11) :woke))]
             (v2/seal! child)
             (is (false? (v2/merge! w child)) "not quiescent: the timer would write after the seal")
             (is (= :woke (v2/value t 2000 ::timeout)))
             (is (wait-until #(true? (v2/merge! w child))) "quiescent once the run retired")
             (is (= 11 (v2/value s 1000 ::timeout))))))))))

(deftest merge-into-a-sealed-parent-is-refused
  (checked
   (let [w (vworld)]
     (binding [v2/*world* w]
       (let [s (v2/signal 1)
             child (v2/fork! w {:mergeable? true})]
         (v2/write! (v2/in-world child s) 10)
         (v2/seal! child)
         (v2/seal! w)
         (is (false? (v2/merge! w child)) "the parent's own diff would move after its seal")
         (v2/unseal! w)
         (is (true? (v2/merge! w child)))
         (is (= 10 (v2/value s))))))))

(deftest a-resolver-settles-conflicts
  (let [run (fn [resolve]
              (let [w (vworld)]
                (binding [v2/*world* w]
                  (let [s (v2/signal 1) t (v2/signal 10)
                        child (v2/fork! w {:mergeable? true})
                        seen (atom nil)]
                    (v2/write! (v2/in-world child s) 2)
                    (v2/write! (v2/in-world child t) 13)
                    (v2/write! t 11)
                    (v2/seal! child)
                    (let [r (v2/merge! w child {:resolve (fn [ident base pv cv]
                                                           (reset! seen [(some? ident) base pv cv])
                                                           (resolve base pv cv))})]
                      {:merged r :s (v2/value s) :t (v2/value t) :seen @seen
                       :released (boolean (wait-until #(aget ^objects child rw/W-RELEASED)))})))))]
    (checked
     (is (= {:merged true :s 2 :t 14 :seen [true 10 11 13] :released true}
            (run (fn [base pv cv] (+ pv (- cv base)))))
         "t: both sides added; s: no conflict, the child's value"))
    (checked
     (is (= {:merged false :s 1 :t 11 :seen [true 10 11 13] :released false}
            (run (fn [_ _ _] :org.replikativ.spindel.v2.core/refuse)))
         "a refusal refuses the whole merge"))
    (checked
     (is (= {:merged false :s 1 :t 11 :seen [true 10 11 13] :released false}
            (run (fn [_ _ _] (throw (ex-info "boom" {})))))
         "a throw is a refusal"))))

(deftest transfer-moves-a-forks-ownership
  (checked
   (let [w (vworld)]
     (binding [v2/*world* w]
       (let [k1 (v2/fork! w) k2 (v2/fork! w)
             m (v2/fork! w {:owner k1})]
         (is (v2/descendant? m w))
         (is (not (v2/descendant? m k1)) "ownership is not lineage")
         (is (true? (v2/transfer! m k2)))
         (is (false? (v2/transfer! m k2)) "already the owner")
         (is (not (v2/descendant? m k2)) "a transfer changes no lineage answer")
         (testing "the old owner no longer waits for it"
           (v2/release-world! k1)
           (is (true? (v2/await-complete k1 2000 ::timeout))))
         (testing "the new owner does"
           (v2/release-world! k2)
           (is (true? (v2/await-complete m 2000 ::timeout)) "closing k2 released m")
           (is (true? (v2/await-complete k2 2000 ::timeout)))))))))

(deftest transfer-refusals
  (checked
   (let [w (vworld) kid (promise)]
     (binding [v2/*world* w]
       (let [pgate (v2/deferred)
             k1 (v2/fork! w) k2 (v2/fork! w)
             m (v2/fork! w {:owner k1})
             below (v2/fork! w {:owner m})
             gone (v2/fork! w)]
         (is (false? (v2/transfer! m m)) "itself")
         (is (false? (v2/transfer! m below)) "a world m owns: a cycle")
         (v2/release-world! gone)
         (v2/await-complete gone 2000 ::timeout)
         (is (false? (v2/transfer! m gone)) "a released new owner")
         (is (false? (v2/transfer! gone k2)) "a done child")
         (testing "a body's (fork) child is counted on its scope and stays there"
           (let [_t (task (let [[side c] (v2/fork)]
                            (if (= side :child) (await (v2/deferred)) (do (deliver kid c) (await pgate) :p))))
                 c (deref kid 2000 nil)]
             (is (false? (v2/transfer! c k2)))
             (v2/release-world! c)))
         (is (true? (v2/transfer! m k2)) "the refusals changed nothing")
         (v2/deliver! pgate 1)
         (doseq [x [below m k1 k2 w]] (v2/release-world! x))
         (is (true? (v2/await-complete w 2000 ::timeout))))))))

(deftest a-host-start-in-flight-at-the-seal-holds-the-merge
  ;; model: the seal check is atomic with the enqueue. A start that passed
  ;; its check before the seal but has not enqueued yet is in flight (the
  ;; counter), and §9 waits for it: the diff cannot move after a merge saw
  ;; the child settled
  (checked
   (let [w (vworld)]
     (binding [v2/*world* w]
       (let [s (v2/signal 1)
             child (v2/fork! w {:mergeable? true})
             admitting (aget ^objects child rw/W-ADMITTING)]
         (v2/write! (v2/in-world child s) 10)
         (v2/seal! child)
         (org.replikativ.spindel.v2.host/kids-add! admitting 1)   ; between its check and its enqueue
         (is (false? (v2/merge! w child)))
         (org.replikativ.spindel.v2.host/kids-add! admitting -1)
         (is (true? (v2/merge! w child)))
         (is (= 10 (v2/value s))))))))
