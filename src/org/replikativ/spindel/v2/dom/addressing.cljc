(ns org.replikativ.spindel.v2.dom.addressing
  "DOM element addresses on engine v2 (phase-d design §2.3-§2.4, A3).

  An element's address hashes its source location, its parent's address
  and its slot in the parent. The parent and slot reach an element in one
  of two ways:

  - Lexically: element macros bind the reserved locals `__dom-parent` and
    `__dom-slot` around each child form. A nested element macro reads them
    from its environment; they survive suspension (continuations close over
    them), and a computation created inside captures them as inputs.
  - Synchronously: a plain function component cannot see its caller's
    locals. The caller runs it under `call-with-context`; its root element
    reads `current`. The context is valid only on the calling thread and
    only until the call returns: it holds a lifetime token, never a run, so
    a binding frame conveyed to a future, a deferred callback or a child
    computation retains only a small dead record."
  (:require [org.replikativ.spindel.engine.hash :as h]
            #?(:clj [clojure.string :as str])
            #?(:clj [replikativ.logging :as log])))

(defn element-address
  "The address of the element at source location `loc` (a map of :file
   :line :column) under `parent` (an address, nil at the root) in `slot`."
  [loc parent slot]
  (keyword (str "el-" (h/content-hash [loc parent slot]))))

(defn keyed-child-address
  "The address of a child keyed by `k` under `parent`: independent of its
   position."
  [parent k]
  (keyword (str "keyed-" (h/content-hash [parent :keyed k]))))

(defn check-keys!
  "Throws unless the item keys `ks` of a keyed list are distinct and
   neither nil nor false: ::invalid-key, ::duplicate-key (ex-data :type).
   The keyed diff drops nil and false keys, and the commit keeps one item
   per key."
  [ks]
  (reduce (fn [seen k]
            (cond
              (or (nil? k) (false? k))
              (throw (ex-info "a keyed list item has a nil or false key" {:type ::invalid-key :key k}))
              (contains? seen k)
              (throw (ex-info "a keyed list has a duplicate key" {:type ::duplicate-key :key k}))
              :else (conj seen k)))
          #{} ks)
  nil)

;; ---------------------------------------------------------------------------
;; The synchronous context

(defrecord Ctx [parent slot live])

(def ^:dynamic *context*
  "The synchronous context of a plain component call (a Ctx), or nil."
  nil)

(defn call-with-context
  "Calls `(f)` with the synchronous context `parent`, `slot`: `current`
   returns them on this thread until `f` returns."
  [parent slot f]
  (let [live (volatile! #?(:clj (Thread/currentThread) :cljs true))]
    (try (binding [*context* (->Ctx parent slot live)] (f))
         (finally (vreset! live nil)))))

#?(:clj (def ^:private diagnose?
          "Development builds (assertions on) report a context read outside its call."
          *assert*))

#?(:clj (defonce ^:private diagnosed (atom #{})))

#?(:clj
   (defn- diagnose!
     "Logs ::uncaptured-context once per call site."
     [site]
     (when (and diagnose? (not (contains? @diagnosed site)))
       (swap! diagnosed conj site)
       (log/warn ::uncaptured-context
                 {:site site
                  :note "a context read outside its component call: create the computation with el/component"}))))

(defn current
  "[parent slot] of the synchronous context, or [nil nil] at the root or
   when the context's call has returned or runs on another thread. `site`
   names the reading element for the JVM diagnostic."
  ([] (current nil))
  ([site]
   (let [c *context*]
     (if (nil? c)
       [nil nil]
       (let [o @(:live c)]
         (if (and (some? o) #?(:clj (identical? o (Thread/currentThread)) :cljs true))
           [(:parent c) (:slot c)]
           (do #?(:clj (diagnose! site))
               [nil nil])))))))

#?(:clj
   (defn lexical-context?
     "Macro time: whether the reserved locals are bound in `env`."
     [env]
     (if (:js-globals env)
       (contains? (:locals env) '__dom-parent)
       (contains? env '__dom-parent))))

;; ---------------------------------------------------------------------------
;; Macro time: the source identity an address hashes

#?(:clj
   (defn canonical-source
     "The classpath-relative path of source file `path`, as a compiler names
      it: a resource path (the JVM's `*file*`, shadow-cljs), a path relative
      to the working directory `cwd` or an absolute one (the stock
      ClojureScript compiler), a file: or jar: URL. A file path under one of
      the directories `roots` loses the longest such root; a path under none
      is returned unchanged."
     [path cwd roots]
     (let [p (str path)]
       (cond
         (str/starts-with? p "jar:") (subs p (+ 2 (str/index-of p "!/")))
         (str/starts-with? p "file:") (recur (.getPath (java.net.URI. p)) cwd roots)
         :else
         (let [norm (fn [f] (str (.normalize (.toAbsolutePath (.toPath ^java.io.File f)))))
               abs (norm (let [f (java.io.File. p)] (if (.isAbsolute f) f (java.io.File. (str cwd) p))))
               root (->> roots
                         (map #(norm (let [f (java.io.File. (str %))] (if (.isAbsolute f) f (java.io.File. (str cwd) (str %))))))
                         (filter #(str/starts-with? abs (str % "/")))
                         (sort-by count >)
                         first)]
           (if root (subs abs (inc (count root))) p))))))

#?(:clj
   (def ^:private classpath-dirs
     (delay (->> (str/split (System/getProperty "java.class.path") (re-pattern java.io.File/pathSeparator))
                 (filter #(.isDirectory (java.io.File. ^String %)))
                 vec))))

#?(:clj
   (defn source-file
     "Macro time: the canonical source path of the form being compiled in
      `env`. The JVM names it in `*file*`; ClojureScript compilers in
      `cljs.analyzer/*cljs-file*` (shadow-cljs leaves `*file*` as
      NO_SOURCE_PATH), as a resource path or a file path."
     [env]
     (canonical-source (if (:js-globals env)
                         (some-> (resolve 'cljs.analyzer/*cljs-file*) deref)
                         *file*)
                       (System/getProperty "user.dir")
                       @classpath-dirs)))
