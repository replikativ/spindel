(ns org.replikativ.spindel.engine.world-identity-test
  (:require #?(:clj [clojure.test :refer [deftest is]]
               :cljs [cljs.test :refer-macros [deftest is]])
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.protocols :as rtp]))

(defrecord SharedStoreWorld [backend identity bindings home]
  rtp/PWorldIdentity
  (world-identity [_] identity))

(defn- token [] #?(:clj (Object.) :cljs (js-obj)))

(deftest lexical-restoration-preserves-the-selected-world-with-a-shared-store
  (let [store (token)
        saved (->SharedStoreWorld store (token) {:scope :outer} nil)
        entered (assoc saved :bindings {:scope :inner})
        child (->SharedStoreWorld store (token) {:scope :resumed} nil)
        restored (ec/restore-scope saved child entered)]
    (is (ec/same-world? saved entered))
    (is (not (ec/same-world? saved child)))
    (is (ec/same-world? child restored))
    (is (= {:scope :outer} (:bindings restored)))
    ;; An explicit world switch restores the complete outer context.
    (is (identical? saved (ec/restore-scope saved child child)))))

(deftest missing-backends-do-not-imply-the-same-world
  (let [saved {:bindings {:scope :outer}} current {:bindings {:scope :child}}
        entered {:bindings {:scope :inner}}]
    (is (not (ec/same-world? saved entered)))
    (is (identical? saved (ec/restore-scope saved current entered)))))

(deftest world-identity-supports-legacy-and-explicit-contexts
  (let [backend (token) identity (token)
        explicit (->SharedStoreWorld nil identity {} nil)
        custom (token)]
    (is (ec/same-world? {:backend backend} {:backend backend}))
    (is (not (ec/same-world? {:backend backend} {:backend (token)})))
    (is (ec/same-world? explicit (assoc explicit :bindings {:scope :inner})))
    (is (not (ec/same-world? custom custom)))))

(deftest home-context-is-world-local-even-when-the-store-is-shared
  (let [store (token) home (atom nil)
        parent (->SharedStoreWorld store (token) {} home)
        child (->SharedStoreWorld store (token) {} home)]
    (reset! home parent)
    (is (identical? parent (ec/home-context (assoc parent :bindings {:scope :inner}))))
    (is (identical? child (ec/home-context child)))))

(deftest trampoline-scope-data-excludes-the-runtime-and-keeps-the-runner-world
  (let [store (token)
        parent (->SharedStoreWorld store (token) {:scope :inner :nil-value nil :false-value false} nil)
        child (->SharedStoreWorld store (token) {:scope :runner :absent-in-capture true} nil)
        captured (ec/capture-context-scope parent)
        restored (ec/restore-context-scope captured child)]
    (is (= (:bindings parent) captured))
    (is (ec/same-world? child restored))
    (is (= captured (:bindings restored)))
    (is (not (contains? (:bindings restored) :absent-in-capture)))
    (is (nil? (ec/restore-context-scope captured nil)))))
