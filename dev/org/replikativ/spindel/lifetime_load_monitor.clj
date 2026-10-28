(ns org.replikativ.spindel.lifetime-load-monitor
  "Observation hooks bracket only timed work; probes run outside its counters.")

(def ^:dynamic *observe!* nil)
(def ^:dynamic *window* nil)
(def ^:dynamic *active-window* nil)

(defn timed [f]
  (if (and *observe!* *window*)
    (do (*observe!* *window* :start)
        (when *active-window* (reset! *active-window* *window*))
        (try (f) (finally
                   (when *active-window* (reset! *active-window* nil))
                   (*observe!* *window* :end))))
    (f)))
