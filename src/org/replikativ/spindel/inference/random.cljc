(ns org.replikativ.spindel.inference.random
  "Where inference draws its randomness from.

  Every draw of a seeded inference run must depend only on WHAT is drawn,
  not on when: particles, chains and proposals run concurrently, and one
  generator shared in arrival order makes a seeded run reproducible only on
  a serial executor. So a draw made while deciding something in a world —
  a sample site, the site an MH move selects, its acceptance — reads a
  STREAM keyed by that world's seed and what is being decided:

    stream(world, key) = generator seeded by hash(seed(world), key)

  World seeds are derived per fork from the parent's seed, the site address
  and the fork index (`savepoint/fork`), so a replay's fresh proposal draws
  from a fresh stream and the same run draws the same numbers.

  anglican's distributions hold `anglican.runtime/RNG` from their
  construction on, so that var is made a delegating generator: it draws from
  the bound stream, and outside one from its own generator, which
  `(.setSeed anglican.runtime/RNG n)` seeds as before. Draws outside any
  world — the seeds of an inference's sessions, SMC's resampling at a
  barrier — come from that generator in program order.

  On ClojureScript draws are not keyed yet: they read the platform generator."
  (:require [org.replikativ.spindel.effects.savepoint :as sp]
            [org.replikativ.spindel.engine.hash :as h]
            #?(:clj [anglican.runtime :as ar]))
  #?(:clj (:import [org.apache.commons.math3.random RandomGenerator Well19937c])))

#?(:clj
   (def ^:dynamic ^RandomGenerator *stream*
     "The stream draws come from, or nil for the process generator."
     nil))

#?(:clj
   (deftype DelegatingGenerator [^RandomGenerator fallback]
     RandomGenerator
     (^void setSeed [_ ^int s] (.setSeed fallback s))
     (^void setSeed [_ ^ints s] (.setSeed fallback s))
     (^void setSeed [_ ^long s] (.setSeed fallback s))
     (nextBytes [_ bs] (.nextBytes (or *stream* fallback) bs))
     (^int nextInt [_] (.nextInt (or *stream* fallback)))
     (^int nextInt [_ ^int n] (.nextInt (or *stream* fallback) n))
     (nextLong [_] (.nextLong (or *stream* fallback)))
     (nextBoolean [_] (.nextBoolean (or *stream* fallback)))
     (nextFloat [_] (.nextFloat (or *stream* fallback)))
     (nextDouble [_] (.nextDouble (or *stream* fallback)))
     (nextGaussian [_] (.nextGaussian (or *stream* fallback)))))

#?(:clj
   (defonce ^:private _installed
     ;; Keep the generator anglican had, so a seed set before this namespace
     ;; loaded still holds.
     (let [fallback ar/RNG]
       (alter-var-root #'ar/RNG
                       (fn [rng] (if (instance? DelegatingGenerator rng)
                                   rng
                                   (->DelegatingGenerator fallback))))
       true)))

#?(:clj
   (defn- key-seed
     "A long from `seed` and `key`."
     [seed key]
     (let [u (h/content-hash [::stream seed key])]
       (bit-xor (.getMostSignificantBits ^java.util.UUID u)
                (.getLeastSignificantBits ^java.util.UUID u)))))

(defn with-stream*
  "Call `f` with draws coming from the stream keyed by `seed` and `key`. A nil
  seed (no session) leaves draws on the process generator."
  [seed key f]
  #?(:clj (if (some? seed)
            (binding [*stream* (Well19937c. (long (key-seed seed key)))]
              (f))
            (f))
     :cljs (f)))

(defn in-world-stream
  "Call `f` drawing from `world`'s stream for `key`."
  [world key f]
  (with-stream* (sp/seed world) key f))

(defn fresh-seed
  "A seed for a new session, drawn from the current generator: in a seeded
  run, the same seeds in the same program order."
  []
  #?(:clj (.nextLong ^RandomGenerator ar/RNG)
     :cljs (random-uuid)))
