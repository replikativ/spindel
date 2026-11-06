(ns org.replikativ.spindel.v2.host-delivery-gc
  (:require [org.replikativ.spindel.v2.core :as v2 :refer [task]]
            [org.replikativ.spindel.v2.host :as hs]
            [org.replikativ.spindel.v2.rows :as rw]))

(defn- until [label ready next]
  (letfn [(check [n]
            (js/gc)
            (cond (ready) (do (println "PASS" label) (next))
                  (= n 200) (throw (ex-info "host delivery GC failed" {:probe label}))
                  :else (js/setTimeout #(check (inc n)) 10)))]
    (js/setTimeout #(check 0) 0)))
(defn- pump! [jobs]
  (with-redefs [hs/execute! (fn [_ f] (swap! jobs conj f))]
    (loop [n 10000] (when-let [f (first @jobs)] (assert (pos? n)) (swap! jobs subvec 1) (f) (recur (dec n))))))
(defn- payload-action [payload] (fn [] (.-byteLength payload)))
(defn- pending-action [original w f] (fn [] (original w f)))
(defn- canceled-fixture [kind]
  (let [p (v2/world {:inline? (= kind :preclaim) :budget 1}) jobs (atom []) entry (atom nil) action (atom nil)
        payload (js/Uint8Array. (* 1024 1024)) weak (hs/weak payload)
        original v2/prepare-host-entry! error (ex-info "earlier body" {})]
    (with-redefs [hs/execute! (fn [_ f] (swap! jobs conj f))]
      (when (= kind :preclaim) (v2/send-world! p #(throw error)))
      (with-redefs [v2/prepare-host-entry! (fn [control f reject intent]
                                             (when-not @entry (reset! entry control) (reset! action (hs/weak f)))
                                             (original control f reject intent))]
        (let [[actual failed?] (try [(v2/call-in! p (payload-action payload)) false]
                                    (catch :default e [e true]))]
          (assert failed?) (when (= kind :preclaim) (assert (identical? error actual))))))
    {:p p :jobs jobs :entry @entry :action @action :payload weak}))
(defn- canceled [kinds next]
  (if-let [kind (first kinds)]
    (let [{:keys [p jobs entry action payload]} (canceled-fixture kind)]
      (until (str "held canceled " (name kind) " ordinary entry releases body and payload before pump")
             #(and (nil? (hs/deref-weak action)) (nil? (hs/deref-weak payload)))
             #(do (assert (= {:phase :canceled} @(.-state entry)))
                  (assert (seq @jobs)) (pump! jobs)
                  (assert (= {} (aget p rw/W-STATE)))
                  (v2/release-world! p) (pump! jobs) (canceled (rest kinds) next))))
    (next)))
(defn- deferred-setup []
  ;; Persistent savepoint handler/task closures must never share the frame
  ;; containing the probe's payload (:none retains that shared JS Context).
  (let [p (v2/world) pubs (atom []) jobs (atom []) pending (atom [])
        original-internal v2/internal!]
    (v2/install-handlers! p {:s #(swap! pubs conj %)})
    (binding [v2/*world* p]
      (task (v2/savepoint :s nil))
      (let [child (v2/instantiate (first @pubs))]
        (with-redefs [v2/internal! (fn [w f] (if (identical? p w)
                                               (swap! pending conj (pending-action original-internal w f))
                                               (original-internal w f)))] (v2/activate! child :go))
        {:p p :child child :jobs jobs :pending @pending}))))
(defn- deferred-fixture []
  (let [{:keys [child jobs] :as setup} (deferred-setup)
        entry (atom nil) action (atom nil) original-prepare v2/prepare-host-entry!
        payload (js/Uint8Array. (* 1024 1024)) weak (hs/weak payload)]
    (with-redefs [hs/execute! (fn [_ f] (swap! jobs conj f))
                  v2/prepare-host-entry! (fn [control f reject intent]
                                           (when-not @entry (reset! entry control) (reset! action (hs/weak f)))
                                           (original-prepare control f reject intent))]
      (let [failed? (try (v2/call-in! child (payload-action payload)) false (catch :default _ true))]
        (assert failed?)))
    (assoc setup :entry @entry :action @action :payload weak)))

(defn- deferred [next]
  (let [{:keys [p child jobs pending entry action payload]} (deferred-fixture)]
    (until "held S4 canceled ordinary entry releases body and payload before parent admission"
           #(and (nil? (hs/deref-weak action)) (nil? (hs/deref-weak payload)))
           #(do (assert (= {:phase :canceled} @(.-state entry)))
                (assert (hs/flag? (aget child rw/W-ACTIVATION-INTENT)))
                (doseq [f pending] (f)) (pump! jobs)
                (v2/release-world! p) (pump! jobs) (next)))))
(defn- callback [payload seen tag fail?]
  (fn [v failed?]
    (when (and (= 1 v) (not failed?))
      (swap! seen conj [tag (.-byteLength payload)])
      (when fail? (throw (ex-info "consumed callback" {}))))))
(defn- callback-fixture []
  (let [p (v2/world) x (v2/signal p 0) jobs (atom []) seen (atom [])
        payload (js/Uint8Array. (* 1024 1024)) weak (hs/weak payload)
        a (v2/observe! x (callback payload seen :a true))
        b (v2/observe! x (callback payload seen :b false))]
    (with-redefs [hs/execute! (fn [_ f] (swap! jobs conj f))]
      (let [failed? (try (v2/write! x 1) false (catch :default _ true))] (assert failed?))
      (assert (seq @jobs)) (pump! jobs))
    (assert (= [[:a (* 1024 1024)] [:b (* 1024 1024)]] @seen))
    (a) (b) {:p p :payload weak}))
(defn- consumed-callback [next]
  (let [{:keys [p payload]} (callback-fixture)]
    (until "live world releases consumed failed callback batch payload after unobserve"
           #(nil? (hs/deref-weak payload)) #(do (v2/release-world! p) (next)))))
(defn- frontier [next]
  (let [p (v2/world {:inline? false}) jobs (atom [])]
    (with-redefs [hs/execute! (fn [_ f] (swap! jobs conj f))]
      (dotimes [_ 1000]
        (let [failed? (try (v2/call-in! p (fn [] (throw (ex-info "canceled body ran" {})))) false
                           (catch :default _ true))] (assert failed?))
        (pump! jobs)))
    (assert (empty? @jobs)) (assert (hs/mpsc-empty? (aget p rw/W-INGRESS)))
    (assert (zero? (.-length (aget p rw/W-CALLBACKS))))
    (assert (zero? (.-length (aget p rw/W-HOST-REPLAY))))
    (assert (zero? (.-length (aget p rw/W-AFTER))))
    (println "PASS 1000 canceled ordinary controls leave bounded empty queues")
    (v2/release-world! p) (pump! jobs) (next)))
(defn -main []
  (assert (and (exists? js/gc) (exists? js/WeakRef)))
  (canceled [:unsupported :preclaim] #(deferred (fn [] (consumed-callback (fn [] (frontier (fn [] (println "HOST DELIVERY GC OK")))))))))
(set! *main-cli-fn* -main)
