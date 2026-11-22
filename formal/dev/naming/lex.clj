;; Naming pass: a lexer that finds whole Clojure symbols in source text without reformatting it.
;; Loaded by renames.clj (babashka).
(ns lex
  (:require [clojure.string :as str]))

;; characters that continue a symbol. `.` and `/` are handled by the callers (a dotted child follows
;; its parent; a namespace alias in front of `/` is not a name).
(def sym-char? (set "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789*+!_?<>=$%&|-'#"))

(defn regions
  "Split Clojure source text into [kind start end] regions, kind :code, :string or :comment."
  [^String s]
  (let [m (re-matcher #"\"(?:[^\"\\]++|\\.)*+\"|;[^\n]*\n?|\\." s) n (count s)]
    (loop [pos 0 out (transient [])]
      (if (.find m)
        (let [a (.start m) b (.end m) c (.charAt s a)]
          (if (= c \\)
            (recur pos out)                                     ; a character literal stays code
            (recur b (conj! (if (< pos a) (conj! out [:code pos a]) out)
                            [(if (= c \") :string :comment) a b]))))
        (persistent! (if (< pos n) (conj! out [:code pos n]) out))))))

(defn md-regions
  "A Markdown file is one :prose region."
  [^String s] [[:prose 0 (count s)]])

(defn tokens
  "Every maximal run of symbol characters, dots and slashes in s[start,end): [text start]."
  [^String s start end]
  (let [m (re-matcher #"[A-Za-z0-9*+!_?<>=$%&|\-'#./:@]+" (subs s start end))]
    (loop [out (transient [])]
      (if (.find m) (recur (conj! out [(.group m) (+ start (.start m))])) (persistent! out)))))

(defn backticked?
  "Is the token at [a,b) of s directly inside backticks (`name`, or within a backticked phrase on one line)?"
  [^String s a b]
  (let [ls (inc (.lastIndexOf s "\n" (max 0 (dec a))))
        le (let [e (.indexOf s "\n" b)] (if (neg? e) (count s) e))
        before (count (filter #(= \` %) (subs s ls a)))
        after (count (filter #(= \` %) (subs s b le)))]
    (and (odd? before) (pos? after))))

(defn line-index "The offsets of the newlines of s." [^String s]
  (let [m (re-matcher #"\n" s)] (loop [out (transient [])] (if (.find m) (recur (conj! out (.start m))) (persistent! out)))))
(defn line-at "1-based line of offset i, given (line-index s)." [idx i]
  (loop [lo 0 hi (count idx)]
    (if (< lo hi) (let [mid (quot (+ lo hi) 2)] (if (< (idx mid) i) (recur (inc mid) hi) (recur lo mid))) (inc lo))))

(defn occurrences
  "Whole-symbol occurrences of the names in `keyset` in text s.
  A token is split at `/` (`ed/inv-sample`), at `@` (`pres-x@gl`) and at `..` (`p3b..p3m`); a leading quote, `#'`, `^`, `~` or `'` is dropped; a dotted token matches on its first
  component when that is a name (`raw0.eq_1`), never on a later one (`Item.post`); a keyword (`:post`)
  never matches. Returns [{:name :start :end :kind :dotted? :backtick?}]."
  [^String s regs keyset]
  (vec
   (for [[kind a b] regs
         [tok ts] (tokens s a b)
         ;; pieces separated by / and @, with their offsets
         [piece off] (let [m (re-matcher #"[/@]|\.{2,}" tok)]
                       (loop [i 0 out []]
                         (if (.find m)
                           ;; in code the piece in front of a slash is a namespace alias, not a name
                           (recur (.end m) (if (and (= kind :code) (= "/" (.group m))) out (conj out [(subs tok i (.start m)) i])))
                           (conj out [(subs tok i) i]))))
         :let [lead (count (re-find #"^(?:#'|['`~^#])*" piece))
               body (subs piece lead)
               ;; drop sentence punctuation after a name in prose: "raw0." "raw0:" "raw0'"
               body (if (#{:comment :prose :string} kind) (-> body (str/replace #"'s$" "") (str/replace #"[.:']+$" "")) body)
               dot (.indexOf ^String body ".")
               head (if (neg? dot) body (subs body 0 dot))
               start (+ ts off lead)]
         :when (and (not (str/starts-with? piece ":")) (contains? keyset head)
                    ;; a keyword piece after a slash (::x/y) or a name directly after a dot never gets here
                    (not (and (pos? start) (= \. (.charAt s (dec start))))))]
     {:name head :start start :end (+ start (count head)) :kind kind
      :dotted? (not (neg? dot))
      :backtick? (and (not= kind :code) (backticked? s start (+ start (count head))))})))
