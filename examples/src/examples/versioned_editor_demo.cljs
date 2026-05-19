(ns examples.versioned-editor-demo
  "Versioned editor — a minimal block-document with branches as
   speculative experiments.

   Goals
   -----
   This example demonstrates the *user-facing* shape of a reactive,
   forkable document. It's intentionally storage-free: branches are
   plain map values in a spindel signal, not datahike branches or
   anything heavier. The point is to prove out the visual algebra
   (chrome pill, gutter decorations, dim unchanged, per-block accept,
   commit-history panel, undo/redo) without dragging in the rest of a
   real app.

   State shape
   -----------
     branches :: {:main {:commits [{:id Int :state BlocksVec :message Str}]
                         :head Int                  ; index into :commits
                         :redo-stack [Commit]}      ; popped commits, for redo
                  :try-1 {:state BlocksVec
                          :base-commit Int           ; main commit it forked from
                          :prompt String}}           ; what the user asked

     active-branch :: :main | :try-N
     prompt-input  :: String         ; live binding of the chat input

   The visual algebra runs on (main-head-state, fork-state). The
   commit history lets us draw the DAG and step backward via undo.

   Actions
   -------
   - `start-try!` clones main's HEAD into a fresh `:try-N` branch
     with synthetic edits driven by the prompt input (stands in for
     `agent did something`), switches active-branch to the fork,
     clears the input.
   - `accept-all!` appends a new commit to main with the fork's
     state, drops the fork, returns to main.
   - `reject!` drops the fork; main untouched.
   - `accept-block!` / `reject-block!` — cherry-pick semantics.
   - `undo!` / `redo!` — step main's head through history.

   Reactive composition
   --------------------
   The page is a single top-level `spin` that tracks `branches`,
   `active-branch`, `branch-menu-open?`, and `prompt-input`. Spindel's
   typed-delta algebra propagates per-block changes incrementally;
   `ifor-each` handles the keyed reconciliation."
  (:require [clojure.string :as str]
            [org.replikativ.spindel.dom.elements :as el]
            [org.replikativ.spindel.dom.browser :as browser]
            [org.replikativ.spindel.dom.render :as render]
            [org.replikativ.spindel.dom.foreach :as foreach]
            [org.replikativ.spindel.incremental.interval :as iv]
            [org.replikativ.spindel.signal :as sig]
            [org.replikativ.spindel.effects.track :refer [track]]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.context :as ctx]
            [org.replikativ.spindel.engine.addressing]
            [org.replikativ.spindel.spin.core]
            [is.simm.partial-cps.async])
  (:require-macros [org.replikativ.spindel.spin.cps :refer [spin]]
                   [org.replikativ.spindel.signal :refer [signal]]
                   [org.replikativ.spindel.dom.foreach :refer [ifor-each]]
                   [org.replikativ.spindel.dom.elements :as el]))

;; =============================================================================
;; State
;; =============================================================================

(defonce runtime (ctx/create-execution-context))

(def seed-blocks
  [{:id 1 :text "Welcome to the versioned editor."}
   {:id 2 :text "Blocks here live in a spindel signal."}
   {:id 3 :text "Branches are speculative experiments over the same blocks."}
   {:id 4 :text "Hit Try below to see an agent-like edit appear as a fork."}
   {:id 5 :text "Accept incorporates the change. Reject discards it."}])

(def initial-branches
  {:main {:commits     [{:id 0 :state seed-blocks :message "Initial blocks"}]
          :head        0
          :redo-stack  []}})

(def branches         (signal runtime initial-branches))
(def active-branch    (signal runtime :main))
(def branch-menu-open? (signal runtime false))
(def prompt-input     (signal runtime ""))

;; `view-commit` is the *time-travel preview* signal. When set, the
;; page renders the trunk at that commit's state without rewinding
;; main's :head. It's read-only — distinct from undo, which mutates.
;; nil = view HEAD as usual. Cleared on accept/reject/switch-branch.
(def view-commit      (signal runtime nil))

;; `author-select` is the persona spawning the next Try. Forks
;; carry the author at the moment they were created; this signal
;; is just the user's current selection.
(def author-select    (signal runtime :user))

;; `editing-block-id` is the ID of the block currently being edited
;; inline (or nil). At most one block edits at a time — simplifies
;; rendering. Click a block body to enter edit mode; blur/Enter to
;; commit. Edits on trunk make a new commit; edits on a fork stack
;; onto the fork's history just like a Refine.
(def editing-block-id (signal runtime nil))

;; `merge-mode?` is the modal review state on a fork. When true, the
;; page renders the diff vs trunk with per-block ✓/✗ and the
;; Accept-all / Cancel banner takes over the action bar. The fork is
;; read-only in this state — to keep editing, Cancel back to
;; workspace mode first. Try and Refine both set this to true because
;; they signal intent to act on the agent's output.
(def merge-mode?      (signal runtime false))

;; Author palette. Hues avoid the diff colors (green/red/amber)
;; so author signals never compete with diff signals. The colors
;; surface only as small cues — a left-border on the chrome pill
;; when viewing a fork, a colored dot in DAG fork stubs, the
;; author label in the proposal banner. Diff decorations stay
;; their own colors; "author" never tints content.
(def author-palette
  {:user        {:color "#1565c0" :label "you"}
   :var         {:color "#6a5acd" :label "Vár"}
   :coder       {:color "#00838f" :label "Coder"}
   :researcher  {:color "#8e24aa" :label "Researcher"}})

(defn- author-color [author]
  (get-in author-palette [author :color] "#666"))

(defn- author-label [author]
  (get-in author-palette [author :label] (name author)))

;; Monotonic counter for synthetic block IDs in Try edits.
(defonce next-id (atom 100))
(defn- fresh-id! [] (swap! next-id inc))

;; Monotonic counter for fork names.
(defonce try-counter (atom 0))

;; Monotonic counter for commit IDs (used as :id, display-only).
(defonce next-commit-id (atom 1))   ; seed commit took :id 0
(defn- fresh-commit-id! [] (let [n @next-commit-id] (swap! next-commit-id inc) n))

(defn- main-head-state
  "Block-vec at main's current head."
  [bs]
  (let [{:keys [commits head]} (:main bs)]
    (:state (nth commits head))))

(defn- main-head-index
  "Current head index into main's commits."
  [bs]
  (get-in bs [:main :head]))

(defn- main-commit-state
  "Block-vec at a specific main-commit index. Nil if out of range."
  [bs idx]
  (let [commits (get-in bs [:main :commits])]
    (when (and (some? idx) (<= 0 idx) (< idx (count commits)))
      (:state (nth commits idx)))))

(defn- fork? [branch-name]
  (not= :main branch-name))

(defn- fork-state
  "Block-vec for a fork branch."
  [bs branch-name]
  (get-in bs [branch-name :state]))

;; =============================================================================
;; Diff classification — pure, no spindel awareness.
;; =============================================================================

(defn classify-blocks
  "Annotate the overlay block list with diff-kinds relative to prev:
     :unchanged - id in prev with identical :text
     :edited    - id in prev with different :text (:prev-text carried
                  for the strikethrough chip)
     :added     - id not in prev

   :removed is NOT emitted inline — see `count-removed`. We walk
   overlay (not prev∪overlay), so the rendered key-list stays
   consistent across fork↔trunk transitions. Simplifies ifor-each's
   reconciliation; a real impl can use a ghost-slot pattern."
  [prev overlay]
  (if (nil? overlay)
    (mapv #(assoc % :diff-kind :unchanged) prev)
    (let [prev-by-id (into {} (map (juxt :id identity) prev))]
      (mapv (fn [o]
              (if-let [p (prev-by-id (:id o))]
                (if (= (:text p) (:text o))
                  (assoc o :diff-kind :unchanged)
                  (assoc o :diff-kind :edited :prev-text (:text p)))
                (assoc o :diff-kind :added)))
            overlay))))

(defn count-removed
  "Number of ids in `prev` absent from `overlay`."
  [prev overlay]
  (let [overlay-ids (set (map :id overlay))]
    (count (filter (fn [p] (not (overlay-ids (:id p)))) prev))))

(defn- diff-summary
  "Counts per diff-kind. :removed comes in separately because we
   don't emit :removed entries in `annotated`."
  [annotated removed-count]
  (let [by-kind (group-by :diff-kind annotated)]
    {:added     (count (:added by-kind))
     :edited    (count (:edited by-kind))
     :removed   removed-count
     :unchanged (count (:unchanged by-kind))}))

;; =============================================================================
;; Actions
;; =============================================================================

(defn- swap-signal!
  "Update a spindel signal under our runtime."
  [sig f & args]
  (binding [ec/*execution-context* runtime]
    (apply swap! sig f args)))

(defn- reset-signal! [sig v]
  (binding [ec/*execution-context* runtime]
    (reset! sig v)))

(defn- short-prompt
  "Truncate a prompt to <30 chars for labels."
  [s]
  (let [s (str/trim (or s ""))]
    (cond
      (str/blank? s)        "(empty)"
      (> (count s) 28)      (str (subs s 0 27) "…")
      :else                 s)))

(defn- canned-fork-edits
  "Synthetic 'agent did some work' on `head-blocks`. The user's
   prompt drives the *labelling* of the new blocks so the visual
   change reflects what they asked for. The edit shape is constant
   for the demo (edit first block, append two, drop last) so all
   four diff-kinds show up reliably.

   In a real impl this is where the LLM would land: receiving
   (head-blocks, prompt), emitting new-blocks."
  [head-blocks prompt]
  (let [topic (let [s (str/trim (or prompt ""))]
                (if (str/blank? s) "a new subsection" s))
        edited (if (seq head-blocks)
                 (update-in (vec head-blocks) [0 :text]
                            #(str % " [extended re: " topic "]"))
                 head-blocks)
        without-last (if (> (count edited) 1)
                       (vec (butlast edited))
                       edited)]
    (into without-last
          [{:id (fresh-id!) :text (str "Heading: " topic)}
           {:id (fresh-id!) :text (str "And a body paragraph elaborating on " topic ".")}])))

(defn- append-main-commit
  "Append a new commit to main, advance head, clear redo-stack."
  [bs state message]
  (let [main      (:main bs)
        commits   (:commits main)
        new-commit {:id      (fresh-commit-id!)
                    :state   state
                    :message message}]
    (assoc bs :main
           {:commits     (conj commits new-commit)
            :head        (count commits)        ; new last index
            :redo-stack  []})))

(defn- start-try!
  "On trunk: spawn a fresh fork from current HEAD. On a fork: stack
   another refinement on top of the current fork state, pushing the
   pre-refinement state onto the fork's :history (fork-level undo)."
  [_]
  (binding [ec/*execution-context* runtime]
    (let [prompt (str/trim @prompt-input)
          bs     @branches
          active @active-branch]
      (if (fork? active)
        ;; Stack on existing fork — fork is now mutable session.
        (let [fork           (get bs active)
              current-state  (:state fork)
              current-prompt (:prompt fork)
              new-state      (canned-fork-edits current-state prompt)]
          (reset! branches
                  (assoc bs active
                         (-> fork
                             (assoc :state new-state
                                    :prompt prompt)
                             (update :history (fnil conj [])
                                     {:state current-state
                                      :prompt current-prompt})
                             (assoc :redo-stack [])))))
        ;; Fresh fork from main HEAD.
        (let [n           (swap! try-counter inc)
              branch-name (keyword (str "try-" n))
              author      @author-select
              head-idx    (main-head-index bs)
              head-state  (main-head-state bs)]
          (reset! branches
                  (assoc bs branch-name
                         {:state       (canned-fork-edits head-state prompt)
                          :base-commit head-idx
                          :prompt      prompt
                          :author      author
                          :history     []
                          :redo-stack  []}))
          (reset! active-branch branch-name)))
      (reset! branch-menu-open? false)
      (reset! prompt-input "")
      ;; Try always operates on HEAD / current fork tip. Clear
      ;; time-travel preview so the projection is unambiguous.
      (reset! view-commit nil)
      ;; Try/Refine are the "intent to merge" trigger — after the
      ;; agent acts, the user lands directly in review mode to
      ;; decide. Hand-edits don't flip this; only agent-prompted
      ;; actions do.
      (reset! merge-mode? true)
      (reset! editing-block-id nil))))

(defn- switch-branch! [name]
  (reset-signal! active-branch name)
  (reset-signal! branch-menu-open? false)
  ;; Switching context clears any time-travel preview — the preview
  ;; is a per-trunk-view affordance, not a global mode.
  (reset-signal! view-commit nil)
  ;; Drop any in-flight inline edit — its target block may not even
  ;; exist on the new branch.
  (reset-signal! editing-block-id nil)
  ;; Review mode is per-branch context too; switching away exits it.
  (reset-signal! merge-mode? false))

(defn- enter-merge!
  "Enter review mode for the currently active fork. Diff overlay
   lights up, page becomes read-only, banner takes over."
  [_]
  (reset-signal! merge-mode? true)
  (reset-signal! branch-menu-open? false)
  (reset-signal! editing-block-id nil))

(defn- cancel-merge!
  "Exit review mode without merging or discarding. Fork stays as-is,
   any per-block cherry-picks done in this session are preserved."
  [_]
  (reset-signal! merge-mode? false))

(defn- toggle-branch-menu! [_]
  (swap-signal! branch-menu-open? not))

(defn- preview-commit!
  "Set the time-travel preview to a specific main-commit index.
   Pure read; main's :head is not touched. Use back-to-head! to clear."
  [idx]
  (binding [ec/*execution-context* runtime]
    ;; Clicking the current HEAD's row clears the preview rather
    ;; than setting view-commit to head's index — saves the user a
    ;; round-trip to the back-to-head button.
    (let [head (main-head-index @branches)]
      (if (= idx head)
        (reset! view-commit nil)
        (reset! view-commit idx)))))

(defn- back-to-head! [_]
  (reset-signal! view-commit nil))

(defn- accept-all! [_]
  (binding [ec/*execution-context* runtime]
    (let [active @active-branch
          bs     @branches]
      (when (fork? active)
        (let [fork   (get bs active)
              state  (:state fork)
              prompt (:prompt fork)
              msg    (str "accept " (name active)
                          (when-not (str/blank? prompt)
                            (str " — " (short-prompt prompt))))]
          ;; ORDER MATTERS: switch the view *first* so the spin's
          ;; intermediate re-render sees `active = :main` and renders
          ;; trunk cleanly. Then update `branches`. Otherwise the
          ;; intermediate render would have `active` pointing at a
          ;; no-longer-present branch and classify against nil.
          (reset! active-branch :main)
          (reset! branches (-> bs
                               (append-main-commit state msg)
                               (dissoc active)))
          (reset! branch-menu-open? false)
          ;; Accept advances HEAD; any prior preview is no longer
          ;; meaningful. Review mode ends with the fork.
          (reset! view-commit nil)
          (reset! merge-mode? false))))))

(defn- discard-branch!
  "Drop the active fork entirely — destructive. Used from workspace
   mode when you decide the branch isn't worth keeping."
  [_]
  (binding [ec/*execution-context* runtime]
    (let [active @active-branch]
      (when (fork? active)
        ;; See accept-all! for why we reset active-branch first.
        (reset! active-branch :main)
        (swap! branches dissoc active)
        (reset! branch-menu-open? false)
        (reset! view-commit nil)
        (reset! merge-mode? false)))))

(defn- undo!
  "Step backward by one. On trunk: pop main's last commit, push it
   onto main's redo-stack. On a fork: pop the fork's :history (its
   pre-refinement state) and push the current state onto the fork's
   redo-stack — fork-level undo, independent of main."
  [_]
  (binding [ec/*execution-context* runtime]
    (let [bs     @branches
          active @active-branch]
      (if (fork? active)
        (let [fork    (get bs active)
              history (or (:history fork) [])]
          (when (seq history)
            (let [{:keys [state prompt]} (peek history)
                  redo-entry             {:state (:state fork) :prompt (:prompt fork)}]
              (reset! branches
                      (assoc bs active
                             (assoc fork
                                    :state state
                                    :prompt prompt
                                    :history (pop history)
                                    :redo-stack (conj (:redo-stack fork)
                                                      redo-entry)))))))
        (let [main    (:main bs)
              commits (:commits main)
              head    (:head main)]
          (when (pos? head)
            (let [popped   (nth commits head)
                  new-head (dec head)]
              (reset! branches
                      (assoc bs :main
                             {:commits    (vec (butlast commits))
                              :head       new-head
                              :redo-stack (conj (:redo-stack main) popped)})))))))))

(defn- redo!
  "Step forward by one — fork-aware, mirroring undo!."
  [_]
  (binding [ec/*execution-context* runtime]
    (let [bs     @branches
          active @active-branch]
      (if (fork? active)
        (let [fork  (get bs active)
              stack (or (:redo-stack fork) [])]
          (when (seq stack)
            (let [{:keys [state prompt]} (peek stack)
                  hist-entry             {:state (:state fork) :prompt (:prompt fork)}]
              (reset! branches
                      (assoc bs active
                             (assoc fork
                                    :state state
                                    :prompt prompt
                                    :history (conj (:history fork) hist-entry)
                                    :redo-stack (pop stack)))))))
        (let [main        (:main bs)
              stack       (:redo-stack main)
              restored    (peek stack)
              new-stack   (pop stack)
              new-commits (conj (:commits main) restored)]
          (when (seq stack)
            (reset! branches
                    (assoc bs :main
                           {:commits     new-commits
                            :head        (dec (count new-commits))
                            :redo-stack  new-stack}))))))))

(defn- apply-blocks-edit!
  "Apply (f current-state) → new-state to the active branch and commit
   under `message`. On trunk this appends a new main commit; on a fork
   it stacks as a refinement (mirroring start-try!'s stacking) so the
   fork's undo history is uniform regardless of whether the change
   came from an agent Refine or a hand-edit."
  [f message]
  (binding [ec/*execution-context* runtime]
    (let [bs     @branches
          active @active-branch]
      (if (fork? active)
        (let [fork           (get bs active)
              current-state  (:state fork)
              current-prompt (:prompt fork)
              new-state      (f current-state)]
          (reset! branches
                  (assoc bs active
                         (-> fork
                             (assoc :state new-state
                                    :prompt message)
                             (update :history (fnil conj [])
                                     {:state current-state
                                      :prompt current-prompt})
                             (assoc :redo-stack [])))))
        (let [state     (main-head-state bs)
              new-state (f state)]
          (reset! branches (append-main-commit bs new-state message)))))))

(defn- enter-edit! [block-id]
  (reset-signal! editing-block-id block-id))

(defn- exit-edit! []
  (reset-signal! editing-block-id nil))

(defn- commit-block-edit!
  "Commit a text edit to block-id with `new-text`. No-op when text
   matches the existing block's text (so an Enter/blur without
   changes doesn't pollute history)."
  [block-id new-text]
  (binding [ec/*execution-context* runtime]
    (let [bs      @branches
          active  @active-branch
          state   (if (fork? active)
                    (fork-state bs active)
                    (main-head-state bs))
          current (some #(when (= (:id %) block-id) (:text %)) state)]
      (when (and (some? current) (not= current new-text))
        (apply-blocks-edit!
         (fn [s] (mapv #(if (= (:id %) block-id)
                          (assoc % :text new-text)
                          %)
                       s))
         (str "edit block " block-id ": " (short-prompt new-text))))
      (exit-edit!))))

(defn- insert-block-after!
  "Insert a fresh empty block after `after-id` (or at the start when
   after-id is nil) and immediately enter edit mode on the new block.
   Works on trunk and on forks."
  [after-id]
  (binding [ec/*execution-context* runtime]
    (let [new-id (fresh-id!)]
      (apply-blocks-edit!
       (fn [s]
         (let [idx (if (nil? after-id)
                     -1
                     (or (some (fn [[i b]] (when (= (:id b) after-id) i))
                               (map-indexed vector s))
                         (dec (count s))))]
           (vec (concat (subvec (vec s) 0 (inc idx))
                        [{:id new-id :text ""}]
                        (subvec (vec s) (inc idx))))))
       (str "insert block " new-id))
      (enter-edit! new-id))))

(defn- delete-block!
  "Remove `block-id` from the active branch. New trunk commit or fork
   refinement, like any other edit."
  [block-id]
  (apply-blocks-edit!
   (fn [s] (filterv #(not= (:id %) block-id) s))
   (str "delete block " block-id))
  (when (= block-id @editing-block-id)
    (exit-edit!)))

(defn- accept-block!
  "Apply the diff for one block from active fork into main as a new
   commit. Cherry-pick semantics: the fork keeps its remaining
   changes."
  [block-id]
  (binding [ec/*execution-context* runtime]
    (let [active     @active-branch
          bs         @branches
          main-state (main-head-state bs)
          fork-state* (fork-state bs active)
          fork-block (some #(when (= (:id %) block-id) %) fork-state*)
          main-block (some #(when (= (:id %) block-id) %) main-state)
          new-main
          (cond
            (and fork-block (not main-block))
            (conj (vec main-state) fork-block)

            (and fork-block main-block
                 (not= (:text fork-block) (:text main-block)))
            (mapv (fn [b] (if (= (:id b) block-id) fork-block b)) main-state)

            (and (not fork-block) main-block)
            (filterv #(not= (:id %) block-id) main-state)

            :else nil)]
      (when new-main
        (reset! branches
                (append-main-commit bs new-main
                                    (str "accept block " block-id " from " (name active))))))))

(defn- reject-block!
  "Discard the change for one block; main stays as-is, fork is
   updated so the block no longer differs."
  [block-id]
  (binding [ec/*execution-context* runtime]
    (let [active     @active-branch
          bs         @branches
          main-state (main-head-state bs)
          fork-state* (fork-state bs active)
          fork-block (some #(when (= (:id %) block-id) %) fork-state*)
          main-block (some #(when (= (:id %) block-id) %) main-state)
          new-fork
          (cond
            (and fork-block (not main-block))
            (filterv #(not= (:id %) block-id) fork-state*)

            (and fork-block main-block
                 (not= (:text fork-block) (:text main-block)))
            (mapv (fn [b] (if (= (:id b) block-id) main-block b)) fork-state*)

            (and (not fork-block) main-block)
            (conj (vec fork-state*) main-block)

            :else nil)]
      (when new-fork
        (swap! branches assoc-in [active :state] new-fork)))))

;; =============================================================================
;; Rendering
;; =============================================================================

(defn- gutter-glyph [kind]
  (case kind
    :added     "+"
    :removed   "−"
    :edited    "✎"
    :unchanged "·"
    " "))

(defn- render-block-row
  "Render a single block. Body switches between plain text and an
   <input> when this block is being edited (one block at a time —
   tracked by `editing-block-id`).

   Toolbar shows:
   - per-block accept/reject in REVIEW mode for non-:unchanged blocks
   - a delete (×) button always when editable (workspace mode)

   `reviewing?` and `editable?` are mutually exclusive: in review
   mode the page is read-only; in workspace mode there's no diff
   overlay so no accept/reject buttons appear."
  [{:keys [id text prev-text diff-kind] :as block} reviewing? editing? editable?]
  (let [cls         (str "block " (name (or diff-kind :unchanged)))
        actionable? (and reviewing?
                         (not= diff-kind :unchanged))]
    (el/div {:class cls :key (str id)}
      (el/div {:class "gutter-icon"} (gutter-glyph diff-kind))
      (el/div {:class "body"
               :on-click (fn [e]
                           (when (and editable? (not editing?))
                             (.stopPropagation e)
                             (enter-edit! id)))}
        (if editing?
          ;; The input is intentionally uncontrolled. We seed it once
          ;; on mount via :ref (which spindel fires exactly once when
          ;; the element is created — :ref is stripped from attr
          ;; reconciliation, so re-renders won't fire it again). If
          ;; we passed :value, every spin re-render would clobber the
          ;; in-progress user input.
          (el/input
            {:class      "block-edit-input"
             :type       "text"
             :ref        (fn [el]
                           (when el
                             (set! (.-value el) text)
                             ;; Defer focus to next paint: when :ref
                             ;; fires the element may not yet be
                             ;; spliced into its parent, so .focus()
                             ;; is a no-op. rAF guarantees the DOM
                             ;; insertion completed.
                             (js/requestAnimationFrame
                              (fn [_]
                                (.focus el)
                                (let [len (.. el -value -length)]
                                  (.setSelectionRange el len len))))))
             :on-blur    (fn [e]
                           (commit-block-edit! id (.-value (.-target e))))
             :on-keydown (fn [e]
                           (cond
                             (= "Enter" (.-key e))
                             (do (.preventDefault e)
                                 (commit-block-edit! id (.-value (.-target e))))
                             (= "Escape" (.-key e))
                             (do (.preventDefault e)
                                 (exit-edit!))))})
          text)
        (when (and (not editing?) (= diff-kind :edited))
          (el/span {:class "prev-text"} prev-text)))
      (el/div {:class "toolbar"}
        (when actionable?
          (el/button
            {:class "icon-btn accept"
             :title "Accept this change"
             :on-click (fn [e] (.stopPropagation e) (accept-block! id))}
            "✓"))
        (when actionable?
          (el/button
            {:class "icon-btn reject"
             :title "Reject this change"
             :on-click (fn [e] (.stopPropagation e) (reject-block! id))}
            "✗"))
        (when (and editable? (not editing?))
          (el/button
            {:class "icon-btn delete"
             :title "Delete this block"
             :on-click (fn [e] (.stopPropagation e) (delete-block! id))}
            "×"))))))

(defn- render-insert-affordance
  "Slim hover-revealed strip that inserts a fresh empty block after
   `after-id` (or at the very start when after-id is nil)."
  [after-id]
  (el/div {:class "insert-row"
           :key (str "ins-" (or after-id "start"))
           :on-click (fn [_] (insert-block-after! after-id))
           :title "Insert a block here"}
    (el/span {:class "insert-glyph"} "+")))

(defn- render-branch-pill
  "The chrome pill. When viewing a fork, the pill's left border
   picks up the fork's author color — small cue only, doesn't
   compete with the main/fork background distinction.

   `pending-count` is the number of blocks on this fork that
   differ from current trunk-HEAD. Rendered as a small badge so
   the user knows there's something to review without the diff
   overlay having to be on."
  [active-name active-author pending-count]
  (let [pill-class (str "branch-pill " (if (fork? active-name) "fork" "main"))]
    (el/div {:class pill-class
             :style (when active-author
                      (str "border-left:4px solid " (author-color active-author)))
             :on-click toggle-branch-menu!}
      (if (fork? active-name) "⟜ " "")
      (name active-name)
      (when (and pending-count (pos? pending-count))
        (el/span {:class "pill-badge"
                  :title (str pending-count " change"
                              (when (> pending-count 1) "s")
                              " pending vs trunk")}
          (str " " pending-count)))
      (el/span {:class "arrow"} "▼"))))

(defn- render-branch-menu [bs active-name]
  (el/div {:class "branch-menu"}
    (for [bname (sort-by name (keys bs))]
      (el/div {:class (str "item" (when (= bname active-name) " active"))
               :key (name bname)
               :on-click (fn [_] (switch-branch! bname))}
        (if (fork? bname) (str "⟜ " (name bname)) (name bname))))))

(defn- render-banner
  "Review-mode action bar. Only rendered when `reviewing?` is true.
   Cancel exits review without merging or discarding — fork stays
   put, the user is back in workspace mode. To throw the fork away,
   use Discard from workspace mode."
  [annotated removed-count author]
  (let [s (diff-summary annotated removed-count)]
    (el/div {:class "branch-banner"}
      (el/div {:class "summary"}
        (when author
          (el/span {:class "author-chip"
                    :style (str "background:" (author-color author))}
            (author-label author)))
        (el/strong {} "Reviewing: ")
        (str (:added s) " added · "
             (:edited s) " edited · "
             (:removed s) " removed"))
      (el/button {:class "btn accept"
                  :title "Merge this fork into trunk and drop the branch"
                  :on-click accept-all!}
        "Accept all")
      (el/button {:class "btn reject"
                  :title "Exit review, keep working on this branch"
                  :on-click cancel-merge!}
        "Cancel"))))

(defn- render-fork-actions
  "Workspace-mode action bar on a fork. Two actions:
   - Merge to trunk → enter review mode
   - Discard branch → destructive, drop fork entirely

   Hidden in review mode (the banner takes over) and on trunk
   (where these actions don't apply)."
  [pending-count]
  (el/div {:class "fork-actions"}
    (el/button {:class "btn primary merge"
                :title "Open the diff vs trunk and decide what to merge"
                :on-click enter-merge!}
      (if (and pending-count (pos? pending-count))
        (str "Merge to trunk (" pending-count ")")
        "Merge to trunk"))
    (el/button {:class "btn ghost discard"
                :title "Throw away this branch and all its work"
                :on-click discard-branch!}
      "Discard branch")))

(defn- render-author-select
  "Persona selector used when starting a Try. Tiny chip-shaped
   <select>; its border picks up the selected author's color so
   the visual link between persona and downstream fork is
   established before the fork even exists."
  [author]
  (el/select
    {:class    "author-select"
     :style    (str "border-color:" (author-color author))
     :value    (name author)
     :on-change (fn [e]
                  (let [v (keyword (.-value (.-target e)))]
                    (binding [ec/*execution-context* runtime]
                      (reset! author-select v))))}
    (for [[k {:keys [label]}] author-palette]
      (el/option {:value (name k) :key (name k)} label))))

(defn- render-prompt-row
  "Author select + prompt input + Try + undo/redo.

   Visibility rules:
   - Trunk + at HEAD: full row (author + input + Try).
   - Trunk + previewing past commit: undo/redo only; prompt would be
     ambiguous (you'd be spawning from HEAD, not the previewed state).
   - Fork: input + Try visible — Try stacks another refinement on the
     fork. Author-select hidden: fork's author was fixed at spawn.
     Button is relabeled \"Refine\" to make the stacking intent clear."
  [prompt author viewing-fork? previewing? can-undo? can-redo?]
  (let [show-prompt? (or viewing-fork? (not previewing?))]
    (el/div {:class "prompt-row"}
      (el/button {:class "btn ghost"
                  :title (if viewing-fork?
                           "Undo last refinement on this fork"
                           "Undo last commit on main")
                  :disabled (not can-undo?)
                  :on-click undo!}
        "↶")
      (el/button {:class "btn ghost"
                  :title (if viewing-fork?
                           "Redo last undone refinement"
                           "Redo last undone commit")
                  :disabled (not can-redo?)
                  :on-click redo!}
        "↷")
      (when (and show-prompt? (not viewing-fork?))
        (render-author-select author))
      (when show-prompt?
        (el/input
          {:class       "prompt-input"
           :type        "text"
           :placeholder (if viewing-fork?
                          "Refine the proposal… (e.g. 'make it more concise')"
                          "Ask the agent to… (e.g. 'add a methods section')")
           :value       prompt
           :on-input    (fn [e]
                          (let [v (.-value (.-target e))]
                            (binding [ec/*execution-context* runtime]
                              (reset! prompt-input v))))
           :on-keydown  (fn [e]
                          (when (= "Enter" (.-key e))
                            (.preventDefault e)
                            (start-try! e)))}))
      (when show-prompt?
        (el/button {:class "btn primary"
                    :on-click start-try!}
          (if viewing-fork? "Refine" "Try"))))))

(defn- render-dag-row
  "Render one commit row of the DAG, with its fork stubs (if any).
   The row itself is click-to-preview (sets view-commit); the fork
   stubs underneath are click-to-switch (sets active-branch).
   `viewed?` highlights the row currently being previewed."
  [{:keys [idx commit head? viewed? forks-here active]}]
  (el/div {:class   (str "dag-row"
                         (when head?    " head")
                         (when viewed?  " viewed"))
           :key     (str "commit-" (:id commit))
           :title   (str "Preview commit at this state"
                         (when head? " (you're already on HEAD)"))
           :on-click (fn [e]
                       (.stopPropagation e)
                       (preview-commit! idx))}
    (el/div {:class "dag-node"} (if head? "●" "○"))
    (el/div {:class "dag-label"}
      (el/span {:class "dag-msg"} (:message commit))
      (when head?   (el/span {:class "head-tag"}   "HEAD"))
      (when viewed? (el/span {:class "viewed-tag"} "VIEWING"))
      (when (seq forks-here)
        (el/div {:class "dag-forks"}
          (for [[fname fork] forks-here]
            (el/div {:class (str "dag-fork"
                                 (when (= fname active) " active"))
                     :key (str "fork-" (name fname))
                     :on-click (fn [e]
                                 (.stopPropagation e)
                                 (switch-branch! fname))}
              (el/span {:class "fork-arrow"} "├─")
              (when-let [a (:author fork)]
                (el/span {:class "author-dot"
                          :style (str "background:" (author-color a))
                          :title (author-label a)}))
              (el/span {:class "fork-name"} (name fname))
              (let [depth (count (:history fork))]
                (when (pos? depth)
                  (el/span {:class "fork-depth"
                            :title (str depth " stacked refinement"
                                        (when (> depth 1) "s"))}
                    (str " +" depth))))
              (when (seq (:prompt fork))
                (el/span {:class "fork-prompt"}
                  (str "  " (short-prompt (:prompt fork))))))))))))

(defn- render-dag
  "DAG panel: vertical line of main commits, top = newest. Each open
   fork branches sideways at its :base-commit.

   The commit rows sit alongside the .dag-title heading as direct
   children of .dag-panel — relying on the discharge's
   fragment-offset derivation (see apply-seq-diff! in discharge.cljc)
   to land the seq-diff's ops at the right index."
  [bs active viewed-idx]
  (let [main      (:main bs)
        commits   (:commits main)
        head      (:head main)
        forks     (->> (dissoc bs :main)
                       (sort-by (fn [[name _]] name))
                       vec)
        rows-data (->> (range (count commits))
                       (mapv (fn [i]
                               (let [commit (nth commits i)]
                                 {:id          (:id commit)
                                  :idx         i
                                  :commit      commit
                                  :head?       (= i head)
                                  :viewed?     (= i viewed-idx)
                                  :forks-here  (filter (fn [[_ f]]
                                                         (= (:base-commit f) i))
                                                       forks)
                                  :active      active})))
                       reverse vec)]
    (el/div {:class "dag-panel"}
      (el/div {:class "dag-title"} "history")
      (ifor-each :id rows-data
                 (fn [row] (render-dag-row row)))
      (when (zero? (count commits))
        (el/div {:class "dag-empty"} "(empty)")))))

;; The whole page is one top-level spin that tracks all five signals.
(defn make-app-spin []
  (spin
    (let [bs            (iv/get-new (track branches))
          active        (iv/get-new (track active-branch))
          menu?         (iv/get-new (track branch-menu-open?))
          prompt        (iv/get-new (track prompt-input))
          viewed-idx    (iv/get-new (track view-commit))
          author        (iv/get-new (track author-select))
          editing-id    (iv/get-new (track editing-block-id))
          merge?        (iv/get-new (track merge-mode?))
          viewing-fork? (fork? active)
          ;; Modal review state — only meaningful on a fork. Drives
          ;; the diff overlay, the read-only gate, and which action
          ;; bar (banner vs prompt+fork-actions) renders.
          reviewing?    (and viewing-fork? merge?)
          active-fork-author (when viewing-fork? (get-in bs [active :author]))
          ;; Time-travel preview is only meaningful on trunk; switching
          ;; to a fork already cleared view-commit in switch-branch!.
          previewing?   (and (not viewing-fork?) (some? viewed-idx))
          ;; The trunk state we project against. HEAD by default; the
          ;; previewed commit when in time-travel mode.
          trunk-state   (or (when previewing? (main-commit-state bs viewed-idx))
                            (main-head-state bs))
          overlay-state (when viewing-fork? (fork-state bs active))
          ;; Compute the diff whenever we're on a fork — we need it
          ;; for the pending-count badge even in workspace mode. The
          ;; result is rendered only in review mode.
          diff-annot    (when viewing-fork?
                          (classify-blocks trunk-state overlay-state))
          diff-removed  (if viewing-fork?
                          (count-removed trunk-state overlay-state)
                          0)
          ;; What we actually feed to the block-row renderer. In
          ;; review mode = annotated diff. In workspace mode = the
          ;; fork's blocks rendered as plain (:unchanged). On trunk =
          ;; the trunk state rendered as plain.
          annotated     (cond
                          reviewing?    diff-annot
                          viewing-fork? (mapv #(assoc % :diff-kind :unchanged)
                                              overlay-state)
                          :else         (mapv #(assoc % :diff-kind :unchanged)
                                              trunk-state))
          removed-count (if reviewing? diff-removed 0)
          ;; Pending-changes count for the pill badge. Only meaningful
          ;; on a fork in workspace mode (not currently reviewing).
          fork-change-count
          (when (and viewing-fork? (not reviewing?))
            (+ (count (filter #(not= :unchanged (:diff-kind %)) diff-annot))
               diff-removed))
          main          (:main bs)
          active-fork   (when viewing-fork? (get bs active))
          ;; Undo/redo are fork-aware. On trunk they walk main.commits;
          ;; on a fork they walk the fork's :history of refinements.
          ;; While previewing past trunk commits, they're inert.
          can-undo?     (cond
                          viewing-fork? (boolean (seq (:history active-fork)))
                          previewing?   false
                          :else         (pos? (:head main)))
          can-redo?     (cond
                          viewing-fork? (boolean (seq (:redo-stack active-fork)))
                          previewing?   false
                          :else         (boolean (seq (:redo-stack main))))
          page-title    (cond
                          viewing-fork? (str "Page viewed via " (name active))
                          previewing?   (str "Page at "
                                             (-> (get-in main [:commits viewed-idx])
                                                 :message))
                          :else         "Page (trunk)")
          ;; Editing is allowed on the live state (trunk-HEAD or the
          ;; current fork tip). Blocked when previewing past trunk
          ;; commits (rewound state should be read-only) AND when
          ;; reviewing (modal merge surface — Cancel out to edit).
          editable?     (and (not previewing?) (not reviewing?))
          ;; Interleave insert-affordances with blocks so the user
          ;; can add a fresh block anywhere. Build [ins, b1, ins, b2,
          ;; ..., ins] as a flat keyed list dispatched by :type.
          ;; IMPORTANT: ifor-each memoizes per-key on (= cached-item
           ;; item), so the row map must carry every value the render
           ;; depends on. `:editing?` flips memo per-block when the
           ;; edit target changes. `:reviewing?` and `:editable?` are
           ;; spin-wide flags but baked into each row so flipping
           ;; between workspace and review mode invalidates the whole
           ;; list — which is what we want (decorations, buttons, and
           ;; insert affordances all change).
          mk-block-row  (fn [b] {:type       :block
                                 :block      b
                                 :editing?   (= (:id b) editing-id)
                                 :reviewing? reviewing?
                                 :editable?  editable?
                                 :id         (str "blk-" (:id b))})
          page-rows     (if editable?
                          (loop [acc [] prev-id nil bs annotated]
                            (let [acc' (conj acc
                                             {:type     :insert
                                              :after-id prev-id
                                              :id       (str "ins-"
                                                             (or prev-id "start"))})]
                              (if (seq bs)
                                (let [b (first bs)]
                                  (recur (conj acc' (mk-block-row b))
                                         (:id b)
                                         (rest bs)))
                                acc')))
                          (mapv mk-block-row annotated))]
      (el/div {:class "layout"}
        ;; DAG panel on the left.
        (render-dag bs active (when previewing? viewed-idx))

        ;; Main column on the right.
        (el/div {:class "main-column"}
          ;; Chrome row 1: branch identity + dropdown +
          ;; back-to-head when previewing. Pill carries a pending-
          ;; changes badge when on a fork in workspace mode.
          (el/div {:class "chrome"}
            (el/div {:style "position:relative;display:inline-block"}
              (render-branch-pill active active-fork-author fork-change-count)
              (when menu? (render-branch-menu bs active)))
            (when previewing?
              (el/button {:class "btn ghost back-to-head"
                          :title "Return to HEAD"
                          :on-click back-to-head!}
                "← back to HEAD")))

          ;; Action bar — exclusive: either banner (review mode) or
          ;; prompt-row + fork-actions (workspace mode). They never
          ;; coexist; the modal split is the whole point.
          (if reviewing?
            (render-banner annotated removed-count active-fork-author)
            (render-prompt-row prompt author viewing-fork? previewing?
                               can-undo? can-redo?))
          (when (and viewing-fork? (not reviewing?))
            (render-fork-actions fork-change-count))

          ;; Page body — block list rendered as a sibling of the
          ;; <h2>. The discharge derives the fragment's offset from
          ;; the first prev-vnode's element position (see
          ;; apply-seq-diff! in discharge.cljc), so siblings are
          ;; tolerated without a wrapping container.
          (el/div {:class (str "page"
                               ;; .viewing-fork dims :unchanged blocks
                               ;; so the diff stands out — only meaningful
                               ;; in review mode.
                               (when reviewing?  " viewing-fork")
                               (when previewing? " previewing"))}
            (el/h2 {} page-title)
            (ifor-each :id page-rows
                       (fn [row]
                         (case (:type row)
                           :insert (render-insert-affordance (:after-id row))
                           :block  (render-block-row (:block row)
                                                     (:reviewing? row)
                                                     (:editing? row)
                                                     (:editable? row)))))))))))

;; =============================================================================
;; Init
;; =============================================================================

(defonce render-handle (atom nil))

(defn ^:export inspect
  "JS-callable accessor for live signal state. Returns a JS object
   with stringified values. Call from devtools as:
     examples.versioned_editor_demo.inspect()"
  []
  (binding [ec/*execution-context* runtime]
    #js {:active        (pr-str @active-branch)
         :branches      (pr-str @branches)
         :menu-open     (pr-str @branch-menu-open?)
         :prompt        (pr-str @prompt-input)
         :view-commit   (pr-str @view-commit)
         :author        (pr-str @author-select)
         :editing       (pr-str @editing-block-id)
         :merge-mode    (pr-str @merge-mode?)}))

(defn ^:export init []
  (js/console.log "Initializing versioned editor demo...")
  (binding [ec/*execution-context* runtime]
    ;; Reset for hot reload.
    (reset! branches initial-branches)
    (reset! active-branch :main)
    (reset! branch-menu-open? false)
    (reset! prompt-input "")
    (reset! view-commit nil)
    (reset! author-select :user)
    (reset! editing-block-id nil)
    (reset! merge-mode? false)
    (reset! try-counter 0)
    (reset! next-id 100)
    (reset! next-commit-id 1))   ; seed commit took :id 0
  (let [container (js/document.getElementById "app")
        discharge (browser/make-dom-discharge js/document)]
    (binding [ec/*execution-context* runtime]
      (let [app-spin (make-app-spin)]
        (reset! render-handle (render/render-spin! container app-spin discharge))))
    (js/console.log "Versioned editor demo ready.")))
