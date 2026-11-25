(ns org.replikativ.spindel.v2.dom.addressing-cljc-test
  "DOM addressing (A3) on both platforms (phase-d design §2.10: D1, D2, D8):
   element addresses travel in lexical locals across suspension, are the
   same keywords on the JVM and on Node, and a plain component's
   synchronous context is valid only within its call."
  (:refer-clojure :exclude [await])
  (:require #?(:clj [clojure.test :refer [deftest is testing]]
               :cljs [cljs.test :refer-macros [deftest is testing async]])
            [org.replikativ.spindel.v2.core :as v2 :refer [spin await]]
            [org.replikativ.spindel.v2.dom.addressing :as addr]
            [org.replikativ.spindel.v2.dom.elements :as el]
            [org.replikativ.spindel.v2.dom.addressing-fixture :as fx]
            #?(:clj [org.replikativ.spindel.v2.verify :as verify]))
  #?(:cljs (:require-macros [org.replikativ.spindel.v2.dom.addressing-cljc-test :refer [static+awaited]])))

#?(:clj
   (defn- subst
     "`form` with every `hole` replaced by `x`, keeping each form's metadata
      (so element forms keep their source locations)."
     [form hole x]
     (cond (= form hole) x
           (seq? form) (with-meta (apply list (map #(subst % hole x) form)) (meta form))
           (vector? form) (with-meta (mapv #(subst % hole x) form) (meta form))
           (map? form) (with-meta (into {} (map (fn [[k v]] [(subst k hole x) (subst v hole x)])) form)
                         (meta form))
           :else form)))

#?(:clj
   (defmacro static+awaited
     "From one tree form: [the tree with `hole` replaced by `v`, evaluated
      here; a computation of the tree with `hole` replaced by (await d)].
      Both have the same source locations."
     [hole v d tree]
     [(subst tree hole v) `(spin ~(subst tree hole `(await ~d)))]))

(defn- then
  "Calls `(k v)` with `h`'s settled value (`[:err e]` for an error)."
  [h k]
  #?(:clj (k (try (v2/value h 2000 ::timeout) (catch Exception e [:err e])))
     :cljs (v2/value-async h (fn [v err?] (k (if err? [:err v] v))))))

(defn- later
  "Runs `f` off the current synchronous extent: a JVM future, a JS timer."
  [f]
  #?(:clj (future (Thread/sleep 20) (f))
     :cljs (js/setTimeout f 20)))

(defn- in-world
  "Runs `(f done)` with a fresh world bound; the test ends at `(done)`."
  [f]
  #?(:clj (let [acc (atom [])
                w (v2/world {:verify? true :hook (verify/checking-hook acc)})
                p (promise)]
            (try (binding [v2/*world* w] (f #(deliver p true)))
                 (is (true? (deref p 5000 false)) "the test completes")
                 (finally (v2/release-world! w)))
            (is (empty? @acc) (str "Rule R divergences: " (vec (take 3 @acc)))))
     :cljs (async done
                  (let [w (v2/world)]
                    (binding [v2/*world* w]
                      (f (fn [] (v2/release-world! w) (js/setTimeout done 0))))))))

(defn- addrs
  "Pre-order [tag address] of the element nodes of vnode `n`."
  [n]
  (if (and (map? n) (:addr n))
    (into [[(:tag n) (:addr n)]] (mapcat addrs (:children n)))
    []))

;; ---------------------------------------------------------------------------
;; D1: nested elements around an await

(deftest d1-addresses-survive-suspension
  (in-world
   (fn [done]
     (let [d (v2/deferred)
           [static c] (static+awaited
                       HOLE "v" d
                       (el/div {:class "a"}
                               (el/span HOLE)
                               (el/ul (el/li "x")
                                      (el/li (let [u HOLE] (el/b u)))
                                      (el/li {:key HOLE} (el/i "k")))
                               (el/p (str "p" HOLE))))
           u (v2/observe! c (fn [_ _]))]
       (later #(v2/deliver! d "v"))
       (then c (fn [vn]
                 (is (= (addrs static) (addrs vn)) "the awaited tree has the static tree's addresses")
                 (is (= 9 (count (addrs vn))))
                 (is (apply distinct? (map second (addrs vn))))
                 (is (= "v" (get-in vn [:children 0 :children 0 :content])))
                 (u) (done)))))))

;; ---------------------------------------------------------------------------
;; D2: the same static tree, the same keywords on every platform

(def ^:private d2-expected
  ;; generated on the JVM from addressing-fixture/tree; Node must agree
  [[:div :el-1668504a-c61a-5bd2-8050-b30ec27309db]
   [:span :el-1ba67d83-54c4-52df-a4b8-32183fb58a6d]
   [:ul :el-295ef1b2-32ce-5686-ba56-c2ebb39dd0ff]
   [:li :keyed-2d69bf6e-2cfd-58ea-80d0-31b9b2a179bc]
   [:li :el-176260a0-29b5-582d-b488-fd28a6f14d38]
   [:li :el-202cbdc2-828c-5e8d-9f90-8274717f0115]
   [:span :el-303bd29c-b3cf-510d-abcd-635de2457ec2]])

(deftest d2-same-addresses-on-every-platform
  (is (= d2-expected (addrs (fx/tree)))))

;; ---------------------------------------------------------------------------
;; D8: the synchronous context lives only within its call

(deftest d8-context-within-the-call-only
  (testing "valid inside, absent after"
    (is (= [:p 3] (addr/call-with-context :p 3 addr/current)))
    (is (= [nil nil] (addr/current))))
  (testing "a callback made inside and called after the call returns"
    (let [cb (addr/call-with-context :p 3 #(#?(:clj bound-fn* :cljs identity) addr/current))]
      (is (= [nil nil] (cb)))))
  (testing "nested calls restore the outer context"
    (is (= [[:q 1] [:p 3]]
           (addr/call-with-context :p 3 (fn [] [(addr/call-with-context :q 1 addr/current) (addr/current)]))))))

(defn- probe
  "A plain component: records its context during the call and, from a
   future or a timer started in the call, after it."
  [seen]
  (swap! seen assoc :in-call (addr/current))
  (later #(swap! seen assoc :later (addr/current)))
  (el/span "probe"))

(defn- when-seen
  "Calls `k` once `seen` has a :later entry."
  [seen k]
  (if (contains? @seen :later)
    (k)
    #?(:clj (do (Thread/sleep 10) (recur seen k))
       :cljs (js/setTimeout #(when-seen seen k) 10))))

(deftest d8-deferred-reads-see-no-context
  (in-world
   (fn [done]
     (let [seen (atom {})
           c (spin (el/div (el/b "x") (probe seen)))]
       (then c (fn [vn]
                 (is (= [(:addr vn) 1] (:in-call @seen)) "the component's root is the div's slot 1")
                 (when-seen seen
                            (fn []
                              (is (= [nil nil] (:later @seen)) "a future or a timer started in the call sees none")
                              (done)))))))))
