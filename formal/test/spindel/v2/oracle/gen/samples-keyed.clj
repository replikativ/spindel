;; Keyed creation (spec §5.2 Z#82, phase-d design §1.13): oracle log samples 75-79. Keys are absent from the
;; model (ids are item inputs), so the replay shows each chosen id is a legal item; the shape checks in
;; oracle_test.clj (`keyed-sample-shapes`) pin the key -> id mapping.
;;
;; 75  w: keyed children reversed, then one inserted, then one removed. The parent tracks the item list and
;;     awaits one keyed computation per item. The reverse names only existing ids; the insert creates one fresh
;;     child; the removed key's child is released at the parent's T12.
;; 76  w: keyed tasks with a vanished key. One keyed task per item, parked on a mailbox take; the parent
;;     completes. The write drops key 2: its task stays in the adoption basis until the parent's T12 cancels it.
;; 77  root, child: a fork family reordering independently. The root's parent has three keyed children; a host
;;     fork; the child reverses its list, then the root rotates its own. Each world readopts by key in its copy.
;; 78  w: a resume between keyed creations plus a duplicate (site, K). One site and one key in a loop: two
;;     creations before a track (n = 0, 1) and one after (n = 2). The write re-enters at the track: the counts
;;     continue from the kept prefix, so the suffix child is readopted.
;; 79  w: repeated interrupted reruns with fresh keys. Each run creates a child under the key of the tracked value
;;     and parks on an empty mailbox (no completion). Each cut replaces the adoption basis with the previous run's
;;     child only.
;;
;; From the repository root (one -Xmx1g JVM):
;;   clojure -J-Xmx1g -Sdeps '{:paths ["src" "test"]}' -M -i formal/test/spindel/v2/oracle/gen/samples-keyed.clj
;; Generated logs are registered in oracle_test.clj (`keyed-specs`).
(ns samples-keyed
  (:refer-clojure :exclude [await])
  (:require [org.replikativ.spindel.v2.core :as v2 :refer [spin task track await await-all take!]]
            [org.replikativ.spindel.v2.verify :as verify]
            [org.replikativ.spindel.incremental.interval :as iv]
            [clojure.pprint]))

(def dir "formal/test/spindel/v2/oracle/")
(defn dump! [path l]
  (spit path (with-out-str (clojure.pprint/pprint l)))
  [path (count l) (frequencies (map (comp first :item) l))])
(defn vworld [acc] (v2/world {:verify? true :hook (verify/projecting-hook (verify/checking-hook acc))}))
(defn- in [w g] (binding [v2/*world* w] (g)))

(defn finish! [n w acc]
  (v2/release-world! w)
  (assert (true? (v2/await-complete w 2000 :timeout)) "the world completes")
  (prn (dump! (str dir "log-sample-" n "-w.edn") (verify/log w)))
  (prn :sample n :divergences @acc))

(defn keyed-parent [items]
  (spin (let [xs (iv/get-new (track items))
              hs (loop [xs xs acc []]
                   (if-let [x (first xs)]
                     (recur (rest xs) (conj acc (v2/with-key x (spin (* 10 x)))))
                     acc))]
          (await-all hs))))

;; 75
(let [acc (atom []) w (vworld acc)
      [items c] (in w #(let [items (v2/signal [1 2 3])] [items (keyed-parent items)]))]
  (v2/observe! c (fn [_ _]))
  (doseq [xs [[3 2 1] [3 4 2 1] [3 4 1]]]
    (v2/write! items xs)
    (assert (= (mapv #(* 10 %) xs) (v2/value c 2000 :timeout))))
  (finish! 75 w acc))

;; 76
(let [acc (atom []) w (vworld acc)
      [items c] (in w #(let [items (v2/signal [1 2])
                             mb (v2/mailbox)]
                         [items (spin (let [xs (iv/get-new (track items))]
                                        (loop [xs xs n 0]
                                          (if-let [x (first xs)]
                                            (do (v2/with-key x (task (take! mb) x))
                                                (recur (rest xs) (inc n)))
                                            n))))]))]
  (v2/observe! c (fn [_ _]))
  (v2/write! items [1])
  (assert (= 1 (v2/value c 2000 :timeout)))
  (finish! 76 w acc))

;; 77
(let [acc (atom []) w (vworld acc)
      [items c] (in w #(let [items (v2/signal [1 2 3])] [items (keyed-parent items)]))]
  (v2/observe! c (fn [_ _]))
  (assert (= [10 20 30] (v2/value c 2000 :timeout)))
  (let [child (v2/fork! w)
        cc (v2/in-world child c)]
    (v2/observe! cc (fn [_ _]))
    (v2/write! (v2/in-world child items) [3 2 1])
    (assert (= [30 20 10] (v2/value cc 2000 :timeout)))
    (v2/write! items [2 3 1])
    (assert (= [20 30 10] (v2/value c 2000 :timeout)))
    (v2/release-world! child)
    (assert (true? (v2/await-complete child 2000 :timeout)) "the child completes")
    (v2/release-world! w)
    (assert (true? (v2/await-complete w 2000 :timeout)) "the world completes")
    (prn (dump! (str dir "log-sample-77-root.edn") (verify/log w)))
    (prn (dump! (str dir "log-sample-77-child.edn") (verify/log child)))
    (prn :sample 77 :divergences @acc)))

;; 78
(let [acc (atom []) w (vworld acc)
      [mid c] (in w #(let [mid (v2/signal 0)]
                       [mid (spin (loop [i 0 acc []]
                                    (if (= i 3)
                                      (await-all acc)
                                      (do (when (= i 2) (track mid))
                                          (recur (inc i) (conj acc (v2/with-key :k (spin i))))))))]))]
  (v2/observe! c (fn [_ _]))
  (assert (= [0 1 2] (v2/value c 2000 :timeout)))
  (v2/write! mid 1)
  (assert (= [0 1 2] (v2/value c 2000 :timeout)))
  (finish! 78 w acc))

;; 79
(let [acc (atom []) w (vworld acc)
      [s c] (in w #(let [s (v2/signal 0)
                         mb (v2/mailbox)]
                     [s (spin (let [v (iv/get-new (track s))]
                                (v2/with-key [:gen v] (spin v))
                                (take! mb)))]))]
  (v2/observe! c (fn [_ _]))
  (doseq [v [1 2 3 4]] (v2/write! s v))
  (finish! 79 w acc))
