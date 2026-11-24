(ns org.replikativ.spindel.v2.adoption-test
  "Adoption follows the model's T1/T4/create-link and T11 (phase-d design §1.2
   R2/R3, §1.13): a candidate moves into the basis only after every
   acceptance check passed, a rejected predecessor stays in the adoption
   basis until T12."
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.v2.core :as v2 :refer [spin task track await aseq]]
            [org.replikativ.spindel.v2.rows :as rw]
            [org.replikativ.spindel.v2.verify :as verify]
            [org.replikativ.spindel.v2.port.helpers :as h]
            [org.replikativ.spindel.incremental.interval :as iv]))

(def ^:dynamic *divergences* nil)

(defn- vworld []
  (v2/world {:verify? true :hook (verify/checking-hook *divergences*)}))

(defmacro checked [& body]
  `(binding [*divergences* (atom [])]
     ~@body
     (is (empty? @*divergences*) (str "Rule R divergences: " (vec (take 3 @*divergences*))))))

(defn- rid
  "The row ID behind handle `x`, inside a body or a world item."
  [x] (aget ^objects (v2/row-of x) rw/ID))

(defn- hid [w x] (v2/call-in! w #(rid x)))

(defn- proj [w] (v2/call-in! w #(verify/projection w)))

(defn- adoption
  "C's basis and adoption basis, as ID sets."
  [w c]
  (let [p (get-in (proj w) [:comps (hid w c)])]
    {:basis (set (map first (:basis p)))
     :adopt (set (get-in p [:adoption :basis]))}))

(defn- settle! [w] (v2/call-in! w (fn [] nil)) (v2/call-in! w (fn [] nil)))

;; ---------------------------------------------------------------------------
;; A-repl-1 (R3): rejected predecessors stay in the adoption basis

(deftest a-repl-1-source-kind-change
  ;; body sources share site -1: run 1 makes S (ord 0) and M (ord 1); run 2
  ;; makes the mailbox at ord 0, meets S, rejects it (T1: same kind) and
  ;; creates M2; S stays in the adoption basis until T12 releases it. Run 3
  ;; readopts M2.
  (checked
   (let [w (vworld)]
     (binding [v2/*world* w]
       (let [s (v2/signal 0)
             gates {0 (v2/deferred) 1 (v2/deferred) 2 (v2/deferred)}
             seen (atom [])
             c (spin (let [v (iv/get-new (track s))
                           a (when (zero? v) (v2/signal 0))
                           m (v2/mailbox)]
                       (swap! seen conj [(when a (rid a)) (rid m)])
                       (await (get gates v))
                       v))
             u (v2/observe! c (fn [_ _]))
             [[sig m1]] @seen]
         (is (some? sig))
         (v2/write! s 1)
         (let [[_ m2] (peek @seen)
               a (adoption w c)]
           (is (not= m1 m2) "the mailbox at the signal's ordinal is a new source")
           (is (contains? (:basis a) m2))
           (is (not (contains? (:basis a) sig)) "the rejected signal does not move into the basis")
           (is (contains? (:adopt a) sig) "it stays in the adoption basis"))
         (v2/deliver! (gates 1) :go)
         (is (= 1 (v2/value c 2000 ::timeout)))
         (let [[_ m2] (peek @seen)
               a (adoption w c)]
           (is (= #{m2} (:basis a)) "T12 released the rejected signal")
           (is (empty? (:adopt a))))
         (v2/write! s 2)
         (let [[[_ m2] [_ m3]] (take-last 2 @seen)]
           (is (= m2 m3) "the next run readopts the mailbox"))
         (u)
         (verify/gc-settle! w)
         (let [srcs (set (keys (:sources (proj w))))
               ids (into #{} (comp cat (remove nil?)) @seen)]
           (is (empty? (filter srcs ids)) "no created source remains after demotion")))))))

(deftest a-repl-1-task-changed-captures
  ;; T4: a spawn with changed captures is a fresh task; the predecessor stays
  ;; in the adoption basis and keeps running until the run completes, then
  ;; T12 cancels it.
  (checked
   (let [w (vworld)]
     (binding [v2/*world* w]
       (let [s (v2/signal 0)
             never (v2/deferred)
             gates {0 (v2/deferred) 1 (v2/deferred)}
             log (atom [])
             ks (atom [])
             c (spin (let [v (iv/get-new (track s))
                           k (task (try (await never) (finally (swap! log conj [:fin v]))))]
                       (swap! ks conj (rid k))
                       (await (get gates v))
                       v))
             u (v2/observe! c (fn [_ _]))]
         (v2/write! s 1)
         (settle! w)
         (let [[k1 k2] @ks
               p (proj w)
               a (adoption w c)]
           (is (not= k1 k2) "changed captures: a fresh task")
           (is (= [] @log) "the predecessor is not cancelled at the spawn")
           (is (contains? (:adopt a) k1) "the predecessor stays in the adoption basis")
           (is (contains? (:basis a) k2))
           (is (some? (get-in p [:tasks k1 :run])) "and keeps running"))
         (v2/deliver! (gates 1) :go)
         (is (= 1 (v2/value c 2000 ::timeout)))
         (is (h/wait-until #(= [[:fin 0]] @log)) "T12 cancels the predecessor")
         (is (empty? (:adopt (adoption w c))))
         (u)
         (is (h/wait-until #(= [[:fin 0] [:fin 1]] @log)) "demotion cancels the current task"))))))

(deftest a-repl-1-sequence-changed-initial-state
  ;; create-link: a sequence with a changed initial state is a new link; the
  ;; predecessor stays in the adoption basis until T12.
  (checked
   (let [w (vworld)]
     (binding [v2/*world* w]
       (let [s (v2/signal 0)
             gates {0 (v2/deferred) 1 (v2/deferred)}
             ls (atom [])
             c (spin (let [v (iv/get-new (track s))
                           xs (aseq [n v] [n (inc n)])]
                       (swap! ls conj (rid xs))
                       (await (get gates v))
                       (first (await xs))))
             u (v2/observe! c (fn [_ _]))]
         (v2/write! s 1)
         (let [[l1 l2] @ls
               a (adoption w c)]
           (is (not= l1 l2) "a changed initial state: a new sequence")
           (is (contains? (:basis a) l2))
           (is (contains? (:adopt a) l1) "the predecessor stays in the adoption basis"))
         (v2/deliver! (gates 1) :go)
         (is (= 1 (v2/value c 2000 ::timeout)))
         (let [[l1 l2] @ls
               a (adoption w c)]
           (is (= #{l2} (:basis a)))
           (is (not (contains? (:adopt a) l1)) "T12 released it"))
         (u))))))
