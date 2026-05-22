# Spindel — a guided walkthrough

The plain-language companion to `engine-formalism.md`. The formalism doc
is precise; this one builds the mental model. Read this one first.

The whole engine rests on one idea: **a spin is a body with checkpoints;
a change jumps execution back to a checkpoint and runs forward from
there.** Everything below is that idea, unfolded.

---

## 1. Three nouns

**Signal** — a value in a box. You read it, you change it. When it
changes, it tells its watchers. Nothing more.

**Spin** — a piece of computation the engine can **pause and resume**.
You write a spin as ordinary code; the `spin` wrapper rewrites it behind
the scenes so the engine can freeze it part-way through and pick it up
later.

**track** — used inside a spin: `(track some-signal)`. Two things in one
move:

1. reads the signal's value right now;
2. subscribes: *"whenever this signal changes, resume me from this exact
   spot."*

---

## 2. Checkpoints

When a spin runs, every `track` (and every `await` — §3) drops a
**checkpoint**: a saved bookmark — *the rest of the body, packaged so the
engine can continue it later.*

```clojure
(spin
  (let [a (track s-a)
        b (track s-b)]
    [a b]))
```

Running it the first time:

```
  start ──▶ (track s-a) ──▶ (track s-b) ──▶ [a b] ──▶ done
                 •                •
           checkpoint 1      checkpoint 2
           watches s-a       watches s-b
```

Result: `[0 0]`. Two checkpoints now sit in the engine, each watching its
signal.

**A signal changes →** the engine finds the checkpoint(s) watching it and
**resumes the body from there:**

- `s-b` changes → resume from checkpoint 2 → re-run `(track s-b)` and
  `[a b]` with the new `b` → `[0 1]`. `(track s-a)` is *behind* the
  checkpoint — untouched.
- `s-a` changes → resume from checkpoint 1 → run forward → `[10 1]`.

A checkpoint left alone by an unrelated change stays valid — it keeps
watching its signal. (That is exactly what `generation_staleness_test`
pins down.)

---

## 3. await — waiting for another spin

`track` watches a signal. **`await` watches another spin.**

`(await child)` means: *pause here until `child` produces a value, then
continue with that value.* It drops a checkpoint just like `track` —
this one watches a child spin instead of a signal:

```clojure
(spin
  (let [x (await child-spin)]
    (* x 2)))
```

```
  parent:  start ──▶ (await child-spin) ──▶ (* x 2) ──▶ done
                            •
                       checkpoint
                       watches child-spin
                            ┊
  child-spin:   runs on its own  ┄┄┄▶ produces 5
                            ┊
                            ▼
       child done → checkpoint fires → parent continues, x = 5 → 10
```

The parent runs until `(await child-spin)`, then **pauses**. The child
runs separately. When it produces a value, the await checkpoint fires
and the parent continues — `x` is the child's value.

|              | `track`                     | `await`               |
|--------------|-----------------------------|-----------------------|
| watches      | a signal                    | a child spin          |
| fires when   | the signal changes          | the child completes   |
| you get      | the value (+ what changed)  | the child's value     |

**Does an await fire more than once?** It depends on the child. A child
that completes once → the await fires once. But a child can be
*reactive* — it can re-complete later, because its own signals changed.
When it does, the await checkpoint fires *again* and the parent continues
again with the child's new value. So an await fires **once per
completion of its child** — usually once, more if the child is reactive.
That re-firing is what makes `parallel` reactive (§4).

*(The categorical framing, if you like it: `track` is comonadic — it
hands you a value together with its change-context. `await` is monadic —
sequencing: do this, then with its result do the next thing. You don't
need this to use the engine; checkpoints are enough.)*

---

## 4. parallel — many checkpoints at once

Until now a spin's checkpoints sat in a **line**: track, then track, then
await — one after another, the body paused at one of them.

`parallel` is the first thing with **many live checkpoints at the same
time.** `(parallel [c1 c2 c3])` runs three spins, waits for **all** of
them, and gives back `[r1 r2 r3]`. It drops **one await checkpoint per
child**, all at once:

```
  parallel:  • checkpoint → watches c1  ┄┄▶ c1 runs ┄▶ done ┐
             • checkpoint → watches c2  ┄┄▶ c2 runs ┄▶ done ┤
             • checkpoint → watches c3  ┄┄▶ c3 runs ┄▶ done ┘
                                                       │
             all three fired ─────────────────────────▶ parallel
                                                        completes [r1 r2 r3]
```

Three checkpoints, live simultaneously. As each child finishes, its
checkpoint fires; when the last fires, `parallel` has every result and
completes.

And because await checkpoints **re-fire** when a reactive child
re-completes (§3): if `c2` later re-completes with a new value,
`parallel`'s `c2` checkpoint fires again and `parallel` re-completes with
the updated vector. `parallel` is reactive.

This is why a spin's await checkpoints are a **set**, not a stack —
`parallel` holds three at once, none "on top of" another.

`race` is `parallel`'s sibling: same many-checkpoints shape, but it
completes as soon as the *first* child finishes, and cancels the rest.

---

## 5. The drain queue — how a change actually travels

"A signal changes → the engine resumes the checkpoints." Here is the
*how* — and it is deliberately not immediate.

The engine has **one queue of events** and processes them **one at a
time.**

- Changing a signal does **not** resume anything directly. It drops an
  event — *"signal s-b changed"* — onto the queue.
- A **drain** is the engine working through that queue: take one event,
  handle it, repeat, until the queue is empty.
- Handling *"s-b changed"* = resuming s-b's checkpoints, which re-runs
  spins. A spin finishing drops a *new* event — *"spin X completed"* —
  onto the **same** queue.
- The drain handles that too — resuming whoever awaited X — which may
  finish more spins — more events. The drain runs until nothing is left.

```
   change s-b
       │
       ▼
   ┌──────────────── event queue ─────────────────┐
   │  [s-b changed]                                │
   └───────────────────────────────────────────────┘
       │  drain takes one event  ◀───────────────┐
       ▼                                         │
   handle it: resume checkpoints, re-run spins    │  finishing a spin
       │                                         │  drops a new event
       └──▶ spin completed ──▶ [spin X completed]─┘

   ... repeat until the queue is empty ...
```

Why a queue, instead of just calling things directly?

- **One thing at a time.** No spin ever sees a half-updated world: every
  consequence of a change is fully processed before the next change is
  touched. This is *glitch-freedom*.
- **Defined order.** A change and its ripple effects happen in a
  predictable sequence.
- **One drainer.** A lock ensures only one drain runs at a time; a change
  that arrives mid-drain simply adds to the queue the running drain is
  already working through.

So the full path of one signal change:

```
change → event on queue → drain picks it up → checkpoints resume
       → spins re-run → completion events → drain picks those up
       → ... → queue empty
```

---

## 6. The whole picture

- A **spin** is a body with **checkpoints**.
- `track` checkpoints watch **signals**; `await` checkpoints watch
  **child spins**.
- A change becomes an **event**; the **drain** works the event queue one
  at a time — resuming checkpoints, re-running spins — until quiet.
- `track` checkpoints are permanent (a signal lives forever); `await`
  checkpoints fire once per child-completion. `parallel` is just many
  await checkpoints held at once.

Everything else in the engine — caching results, the two *kinds* of spin
(replayable computations vs. one-shot resources), fork/restore, the typed
delta algebra — is refinement layered on this skeleton. When a piece of
the engine confuses you, come back to the one sentence: *a spin is a body
with checkpoints; a change jumps back to a checkpoint and runs forward.*
