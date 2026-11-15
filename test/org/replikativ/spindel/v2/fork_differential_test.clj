(ns org.replikativ.spindel.v2.fork-differential-test
  "Fork isolation, differentially (§8.1): a generated program runs a common
   prefix of host operations, forks into a parent and two sibling children,
   and each world continues with its own operations, interleaved. Every
   world must end in the state of a fresh world that ran the prefix and its
   own operations without forking."
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is]]
            [clojure.test.check :as tc]
            [clojure.test.check.generators :as gen]
            [clojure.test.check.properties :as prop]
            [org.replikativ.spindel.v2.core :as v2 :refer [spin task track await take!]]
            [org.replikativ.spindel.incremental.interval :as iv]))

(def n-sig 3)
(def n-def 3)

;; --- programs -------------------------------------------------------------

(def gen-input (gen/one-of [(gen/tuple (gen/return :sig) (gen/choose 0 (dec n-sig)))
                            (gen/tuple (gen/return :def) (gen/choose 0 (dec n-def)))]))

(def gen-comp (gen/tuple (gen/elements [:flat :nested]) (gen/vector gen-input 1 3)))

(def gen-step (gen/one-of [(gen/tuple (gen/return :await) (gen/choose 0 (dec n-def)))
                           (gen/tuple (gen/return :take))
                           (gen/tuple (gen/return :read) (gen/choose 0 (dec n-sig)))
                           (gen/tuple (gen/return :write) (gen/choose 0 (dec n-sig)) (gen/choose 0 9))
                           (gen/tuple (gen/return :spawn) (gen/choose 0 (dec n-def)))]))

(def gen-task (gen/vector gen-step 1 4))

(def gen-op (gen/one-of [(gen/tuple (gen/return :write) (gen/choose 0 (dec n-sig)) (gen/choose 0 9))
                         (gen/tuple (gen/return :deliver) (gen/choose 0 (dec n-def)) (gen/choose 0 9))
                         (gen/tuple (gen/return :post) (gen/choose 0 9))
                         (gen/tuple (gen/return :cancel) (gen/choose 0 2))]))

(def gen-case
  (gen/hash-map :comps (gen/vector gen-comp 0 3)
                :tasks (gen/vector gen-task 0 3)
                :prefix (gen/vector gen-op 0 5)
                :ops-p (gen/vector gen-op 0 5)
                :ops-a (gen/vector gen-op 0 5)
                :ops-b (gen/vector gen-op 0 5)
                :ops-aa (gen/vector gen-op 0 5)
                :nest-at (gen/choose 0 5)
                :order (gen/vector (gen/elements [:p :a :b]) 15)
                :order2 (gen/vector (gen/elements [:p :a :b :aa]) 20)))

;; --- running --------------------------------------------------------------

(defn- read-input [{:keys [sigs defs]} [kind i]]
  ;; expands inside the comp body below; kept as data for the closure
  (case kind :sig (nth sigs i) :def (nth defs i)))

(defn- make-comp [h [shape inputs]]
  (let [srcs (mapv #(vector (first %) (read-input h %)) inputs)]
    (case shape
      :flat (spin (loop [xs srcs acc []]
                    (if (empty? xs)
                      acc
                      (let [[kind x] (first xs)]
                        (recur (rest xs)
                               (conj acc (if (= kind :sig) (iv/get-new (track x)) (await x))))))))
      ;; an inner computation created by the outer body: adopted across reruns
      :nested (spin (let [inner (spin (loop [xs srcs acc []]
                                        (if (empty? xs)
                                          acc
                                          (let [[kind x] (first xs)]
                                            (recur (rest xs)
                                                   (conj acc (if (= kind :sig) (iv/get-new (track x)) (await x))))))))]
                      [:outer (await inner)])))))

(defn- make-task [{:keys [sigs defs mb]} steps]
  (task (loop [ss steps acc []]
          (if (empty? ss)
            acc
            (let [[op a b] (first ss)]
              (recur (rest ss)
                     (case op
                       :await (conj acc (await (nth defs a)))
                       :take (conj acc (take! mb))
                       :read (conj acc (iv/get-new (track (nth sigs a))))
                       :write (do (v2/write! (nth sigs a) b) (conj acc [:w a b]))
                       :spawn (let [d (nth defs a)] (conj acc [:sub (await (task [:in (await d)]))])))))))))

(defn- build [w {:keys [comps tasks]}]
  (binding [v2/*world* w]
    (let [h {:sigs (vec (repeatedly n-sig #(v2/signal 0)))
             :defs (vec (repeatedly n-def v2/deferred))
             :mb (v2/mailbox)}
          cs (mapv #(make-comp h %) comps)]
      (doseq [c cs] (v2/observe! c (fn [_ _])))      ; keep them live
      (assoc h :comps cs :tasks (mapv #(make-task h %) tasks)))))

(defn- in [w h]
  {:sigs (mapv #(v2/in-world w %) (:sigs h))
   :defs (mapv #(v2/in-world w %) (:defs h))
   :mb (v2/in-world w (:mb h))
   :comps (mapv #(v2/in-world w %) (:comps h))
   :tasks (mapv #(v2/in-world w %) (:tasks h))})

(defn- apply-op! [h [op a b]]
  (case op
    :write (v2/write! (nth (:sigs h) a) b)
    :deliver ((nth (:defs h) a) b)
    :post ((:mb h) a)
    :cancel (when-let [t (get (:tasks h) a)] (v2/cancel-task! t))))

(defn- outcome [x]
  (try (v2/value x 20 ::pending)
       (catch Exception e [:err (or (some-> (ex-data e) keys sort first) (ex-message e))])))

(defn- state [h]
  {:sigs (mapv outcome (:sigs h))
   :comps (mapv outcome (:comps h))
   :tasks (mapv outcome (:tasks h))})

(defn- fresh [prog ops]
  (let [w (v2/world)]
    (try (let [h (build w prog)]
           (run! #(apply-op! h %) (concat (:prefix prog) ops))
           (state h))
         (finally (v2/release-world! w)))))

(defn- split-a [{:keys [ops-a nest-at]}]
  (split-at (min nest-at (count ops-a)) ops-a))

(defn- run-queues! [hs queues order]
  ;; the generated interleaving, then whatever is left in each queue
  (doseq [k (concat order (apply concat (repeat 5 (keys hs))))]
    (when-let [op (first (get @queues k))]
      (swap! queues update k rest)
      (apply-op! (hs k) op))))

(defn- forked [{:keys [prefix ops-p ops-b ops-aa order order2] :as prog}]
  (let [w (v2/world)
        [a1 a2] (split-a prog)]
    (try
      (let [hp (build w prog)
            _ (run! #(apply-op! hp %) prefix)
            a (v2/fork! w) b (v2/fork! w)
            hs {:p hp :a (in a hp) :b (in b hp)}
            queues (atom {:p ops-p :a a1 :b ops-b})
            ;; phase 1: until the child a has run a1 (the rest of p and b may wait)
            _ (doseq [k order]
                (when-let [op (first (get @queues k))]
                  (swap! queues update k rest)
                  (apply-op! (hs k) op)))
            _ (run! #(apply-op! (:a hs) %) (get @queues :a))
            _ (swap! queues assoc :a a2)
            ;; a nested fork of the child, then everyone continues
            aa (v2/fork! a)
            hs (assoc hs :aa (in aa hp))
            _ (swap! queues assoc :aa ops-aa)
            _ (run-queues! hs queues order2)
            res {:p (state (:p hs)) :a (state (:a hs)) :b (state (:b hs)) :aa (state (:aa hs))}]
        (v2/release-world! aa) (v2/release-world! a) (v2/release-world! b)
        res)
      (finally (v2/release-world! w)))))

(def fork-isolation
  (prop/for-all [prog gen-case]
                (let [got (forked prog)
                      [a1 _] (split-a prog)]
                  (and (= (:p got) (fresh prog (:ops-p prog)))
                       (= (:a got) (fresh prog (:ops-a prog)))
                       (= (:b got) (fresh prog (:ops-b prog)))
                       (= (:aa got) (fresh prog (concat a1 (:ops-aa prog))))))))

(deftest forks-behave-like-unforked-runs
  (let [n (Long/getLong "spindel.v2.fork-diff-tests" 150)
        r (tc/quick-check n fork-isolation)]
    (is (:pass? r) (pr-str (select-keys r [:seed :fail :shrunk])))))
