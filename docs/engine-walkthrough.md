# Spindel — a guided walkthrough

The plain-language companion to `engine-formalism.md`. The formalism doc
is precise; this one builds the mental model. Read this one first —
after `concepts.md` (how to *use* spindel), before `engine.md` /
`scheduling.md` (the detailed internals).

The whole engine rests on one idea: **a spin is a body of checkpoints;
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

*(The engine's source and the other docs call a checkpoint a*
**continuation** *— the standard term for "the saved rest of a
computation." This walkthrough says* checkpoint *because it is the
friendlier picture. Same thing.)*

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
watching its signal.

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

---

## 4. parallel — many checkpoints at once

Until now a spin's checkpoints sat in a **line**: track, then track, then
await — one after another, the body paused at one of them.

`parallel` is the first thing with **many live checkpoints at the same
time.** `(parallel [c1 c2 c3])` runs three spins, waits for **all** of
them, and gives back `[r1 r2 r3]`. It drops **one await checkpoint per
child**, all at once:

```
  parallel:  • watches c1  ┄┄▶ c1 runs ┄▶ done ┐
             • watches c2  ┄┄▶ c2 runs ┄▶ done ┤
             • watches c3  ┄┄▶ c3 runs ┄▶ done ┘
                                           │
             all fired ────────────────────▶ parallel completes [r1 r2 r3]
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

"A signal changes → checkpoints resume" — the *how* is deliberately not
immediate. The engine has **one event queue**, worked **one event at a
time.**

- Changing a signal does **not** resume anything directly. It drops an
  event — *"signal s-b changed"* — onto the queue.
- A **drain** is the engine working through that queue: take one event,
  handle it, repeat, until the queue is empty.
- Handling *"s-b changed"* = resuming s-b's checkpoints, which re-runs
  spins. A spin finishing drops a *new* event — *"spin X completed"* —
  onto the **same** queue.
- The drain handles that too — resuming whoever awaited X — until nothing
  is left.

```
   change s-b
       │
       ▼
   ┌──────────── event queue ─────────────┐
   │  [s-b changed]                        │
   └───────────────────────────────────────┘
       │  drain takes one  ◀──────────────┐
       ▼                                  │  finishing a spin
   handle it: resume checkpoints,          │  drops a new event
   re-run spins                            │
       └──▶ spin completed ──▶ [X done] ───┘

   ... repeat until the queue is empty ...
```

Why a queue, instead of just calling things directly?

- **One thing at a time.** No spin ever sees a half-updated world: every
  consequence of a change is fully processed before the next change is
  touched. This is *glitch-freedom*.
- **Defined order.** A change and its ripple effects happen in a
  predictable sequence.
- **One drainer.** A lock ensures only one drain runs at a time; a change
  that arrives mid-drain simply joins the queue the running drain is
  already working through.

---

## 6. Effects — the pattern behind track and await

You have now seen three things that drop a checkpoint: `track`, `await`,
and (next section) `yield`. They are not three special cases. They are
three **effects**, and "effect" is the real general concept:

> **An effect is a call the `spin` wrapper recognizes and turns into a
> checkpoint.**

When the `spin` macro rewrites a body, it scans for effect calls. At each
one it splits the body — everything *after* the call becomes the
checkpoint — and routes the call to that effect's **handler**, the code
that decides what to watch and when to resume:

```
  (spin  …code…  (track s)  …rest…)
                     │
        macro splits the body here
                     │
        ┌────────────┴─────────────┐
   the track call            …rest… becomes
   → track's handler         the checkpoint
     (watch s, resume
      on change)
```

So the engine does not hard-code "track" and "await." It keeps a small
**registry** of effects, and the macro builds a body's checkpoints from
whatever is registered. That is why you can **add your own effect**
(`custom-effects.md`): register a symbol and a handler, and
`(your-effect …)` becomes a checkpoint in spin bodies just like the
built-ins.

Three words name three real *stages* of one effect — keep them straight:

- the **effect** — the call you write (`track`), at the source level;
- the **breakpoint** — the macro splitting the body there, at compile
  time;
- the **continuation** (this doc's *checkpoint*) — the runtime suspension
  it produces.

---

## 7. yield — and the second axis: push vs pull

`track` and `await` both *consume* — they wait for something. `yield`
*produces*.

`(yield v)` drops a checkpoint that hands out the value `v`, then pauses
— until someone asks for the next one. You use it inside `gen-aseq`,
which builds a lazy **async sequence**:

```clojure
(gen-aseq
  (yield 1)
  (yield 2)
  (yield 3))
```

A consumer **pulls** the sequence one step at a time with `anext`: each
`anext` runs the body to the next `yield`, hands back
`[value rest-of-sequence]`, and pauses again. Nothing runs until pulled.

That exposes a second axis the model needs — **push vs pull**:

```
        PUSH — a signal                  PULL — an async sequence
  change it → engine notifies            anext → consumer asks for next
  track consumes it, body re-runs        yield produces into it
  the engine drives                      the consumer drives
```

A signal is a stream the engine *pushes* at you; an async sequence is a
stream you *pull*. Same "stream of values" idea — opposite direction of
control.

---

## 8. Caching — why a re-run is cheap

A signal change re-runs spins. If every re-run redid all the work from
scratch, a deep reactive graph would be hopeless. It is not, because of
**caching**.

Every spin's engine record holds a **cached result** and a
**clean / dirty** flag:

- **clean** — the cache is valid; the spin's inputs have not changed
  since it last ran.
- **dirty** — an input changed; the cache is stale; the spin must re-run.

A signal change marks only the spins *downstream of it* dirty; everything
else stays clean. When a spin `await`s a child that is **clean**, it gets
the cached result *immediately* — the child does not re-run. Only
**dirty** spins actually re-run.

There is a second, finer check — the **capture gate**. When a spin is
defined *inside* another spin's body and the parent re-runs, that inner
spin is re-encountered. The engine compares the values the inner spin
captured from its surroundings: if they are unchanged, the inner spin is
left clean and serves its cache; only if a captured value actually moved
does it re-run. So re-running a parent does **not** blindly re-run all
its children — each re-runs only if *its own* inputs moved.

Together: a change re-runs the minimum — the dirty sub-graph — and
everything else answers from cache.

---

## 9. Two kinds of spin

Not every spin is a cacheable calculation. There are **two kinds**, and
the engine labels each one:

- A **computation spin** — the normal kind, written with the `spin`
  macro. It is a pure-ish calculation: the same inputs give the same
  result. It has a stable identity, it is cacheable, and it can be
  *replayed* — re-run from scratch and land in the same place. Replay is
  what makes fork / restore possible.

- A **resource spin** — `sleep`, `parallel`, `race`, a deferred, a
  mailbox. Its body is an *effect on the outside world*: it arms a timer,
  starts coordination, allocates a one-shot slot. It is not a pure
  calculation and **not replayable** — replaying it would arm the timer
  twice. Each one is a fresh, single-use thing.

The engine treats them differently exactly where it must: a computation
spin's cache is reused and the spin replayed; a resource spin is always
run fresh and never replayed. Labelling the two kinds explicitly is what
lets the engine apply the right rule everywhere instead of guessing.

---

## 10. Errors and cancellation

A spin finishes in one of **three** ways: with a **value**, with an
**error**, or **cancelled**.

**Errors travel like values, in reverse.** A spin's result is tagged
`:ok` or `:error`. When a parent `await`s a child that finished
`:error`, the error flows into the parent and **short-circuits** it — the
rest of the parent's body is skipped and the parent finishes `:error`
too. An error propagates up the await chain just as a value would, only
down the failure track.

**Cancellation is cooperative.** `cancel-spin!` *marks* a spin (and
everything depending on it) — it does not kill anything mid-flight. The
consuming effects — `track` and `await` — check "am I cancelled?" the
instant they run, so a cancelled spin stops the next time it reaches one.
A spin in a tight loop with no `track` or `await` in it will not notice
until the loop ends — that "cooperative, not preemptive" contract falls
straight out of *checkpoints are the control points*. `race` and
`parallel` use this internally — `race` cancels the losers, `parallel`
cancels the siblings when one fails.

Cancellation is really a *flavour* of error — a cancelled spin finishes
with a cancellation-typed error — so the same up-the-chain propagation
applies.

---

## 11. The whole picture

- A **spin** is a body of **checkpoints**.
- A checkpoint is created by an **effect** — `track` (watch a signal),
  `await` (watch a child spin), `yield` (emit into a pulled sequence), or
  any effect you register yourself.
- A change becomes an **event**; the **drain** works the event queue one
  at a time — resuming checkpoints, re-running spins — until quiet.
- Re-runs are cheap: only **dirty** spins re-run; **clean** ones serve a
  cache.
- Spins come in two kinds — replayable **computations** and one-shot
  **resources**.
- A spin finishes with a **value**, an **error**, or a **cancellation**.

Two axes organize all of it:

- **compute** — `track` is comonadic (a value carried with its history);
  `await` is monadic (one step sequenced after another);
- **stream** — a signal is **pushed** at you; an async sequence is
  **pulled** by you.

When a piece of the engine confuses you, come back to the one sentence:
*a spin is a body of checkpoints; a change resumes a checkpoint and runs
forward.*
