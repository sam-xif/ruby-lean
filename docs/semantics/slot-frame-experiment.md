# Memo — does the slot frame unlock value? A one-day experiment

**2026-08-29.** Companion to [`slot-frame.md`](slot-frame.md) (the design, and §10
for what is built) and [`../../ruby-ruby-lean/notes/model/HANDOFF-SF.md`](../../ruby-ruby-lean/notes/model/HANDOFF-SF.md)
(state and the unproved bridge). Neither is restated here; this memo is only the
experiment.

## Why a memo rather than just doing it

The frame is the kind of machinery that can look elegant and buy nothing, and
nothing in what has been built so far distinguishes those two outcomes. The
theorems say the algebra is coherent. They say nothing about whether *real
certificates over real programs* hold more rows than they do today, and the
design's motivating measurements (§1) were taken against the guard, not against
the frame — they establish the problem, not the fix.

So: four experiments, thresholds fixed **before** running, and kill criteria that
name the outcome in which we stop rather than iterate.

## The claim, stated so it can fail

> The frame lets a certificate hold rows that the name-global guard forces it to
> choose between, on real programs, at a cost the kernel will pay.

Three independent conditions, each with its own cheap falsifier:

| | must hold | falsifier |
|---|---|---|
| **V1** | row density actually rises | the natural row set collides at *class* level too, so the frame admits barely more than the one-per-name choice |
| **V2** | it stays decidable at the certificate boundary | `frameOkB` by `decide` blows up on a real AST |
| **V3** | the closed world survives real Ruby | the install walk emits `opaque_` on the very classes the rows need |

V2 and V3 can kill the approach. V1 only sizes the prize. Run them in that
order, not in the order that is most satisfying.

## The control, measured 2026-08-29

Before designing around the blocker, it was reproduced — on **boot classes
alone**, so it needs no slice files, no user-class name resolution, and no new
proofs:

```
rowsGuarded baseDecls [String#to_s]                              = true
rowsGuarded baseDecls [String#to_s, Integer#to_s]                = false
rowsGuarded baseDecls [String#to_s, Integer#to_s, Symbol#to_s]   = false
```

`"String#to_s"`, `"Integer#to_s"` and `"Symbol#to_s"` are three distinct real
builtin ids. One row is admissible; two are not. That is the whole blocker, in
three lines, with no Homebrew in sight — which is what makes E3 below a
half-day rather than a week.

---

## E2 — decidability cost  ·  ~1 hour  ·  tests V2  ·  **run first**

**Procedure.** Time `by decide` on `frameOkB` across a 2-D sweep: footprint size
(3 / 10 / 25 rows, the last being all of `certify/core-rows.txt`) × program size
(`egEven` / a ~100-node program / the largest slice AST the decoder already
produces). Record elaboration time and whether `maxRecDepth` must rise.

**Pass:** 25 rows × a real slice AST decides in a few seconds, no
`native_decide`.
**Fail:** superlinear blow-up, or needing `native_decide` — banned on this path
to keep the axiom baseline.

**On failure:** the footprint representation is wrong, not the idea. The fix is
to summarize — per-class *name sets* instead of per-slot lists — which changes
`compose`, `conflicts` and the wire format, so it must happen before anything
else is built on the current shape.

**Why first:** nearly free, and it tests the one constraint with a track record
of killing designs in this project. A failure here invalidates E3's *design*,
not merely its result.

---

## E3 — the accept that is impossible today  ·  ~half a day  ·  the artifact

The deliverable is one program the checker accepts **only** because of the
frame, and one near-identical program it still rejects.

```ruby
"abc".to_s.length + 1.to_s.length
```

Two rows, `String#to_s : () -> String` and `Integer#to_s : () -> String`. Both
boot classes; `bootResolver` covers them.

| case | expected | what it establishes |
|---|---|---|
| control | 2-row cert rejected today | the blocker is real (already measured above) |
| positive | with the frame consulted, `validateJ` accepts | the frame buys an accept |
| **negative** | same cert against `class String; def to_s; 1; end; end` still **rejects** | the frame *discriminates* |

**The negative case is the experiment.** Without it this demonstrates only
permissiveness, and anything is permissive if you delete the guard.

**The throwaway change it needs.** `rowGuards` is
`declaresName D r.name == false && …`; the spike weakens it to
`declaresName D r.name == false || rowFramed c.footprint r`, threading the
footprint through `rowsGuarded`. Roughly fifteen lines.

> **Do not merge this.** That disjunct's soundness rests on the unproved bridge;
> merging it would make `validateJ_certifies` silently conditional on a lemma
> that does not exist — precisely the failure the `frameOkB` docstring was
> written to prevent. Spike branch, deleted after measurement, numbers recorded
> in `HANDOFF-SF.md`.

---

## E1 — row density  ·  ~2 hours  ·  tests V1, sizes the prize

Build the **uncontorted** row set: for every `(class, name)` the slice actually
calls, Sorbet's signature, with the one-per-name restriction dropped. Then count

* `A_guard` — the maximum admissible under `declaresName`, i.e. a maximum
  matching on method names (`core-rows.txt`'s 25 rows are one such choice);
* `A_frame` — those whose footprints compose and survive the install inventory.

**Metric `A_frame / A_guard`. Pass: ≥ 1.5×.**

Below ~1.2× the frame is solving a problem this slice does not have, and the
effort belongs on overload support instead. No Lean is needed for the counting —
`compose` and `conflicts` are pure and callable from `#eval`.

---

## E4 — install census on real ASTs  ·  ~2 hours  ·  tests V3

Run `installsOf` over the decoded slice files and the prelude. Report total
sites, `opaque_` count with reasons, `anyName` count, classes touched, and the
number that decides it: **how many `opaque_` sites land on a class some intended
row reads.**

**Pass:** zero.
**Fail:** sorbet-runtime's shim aliases methods aside, and any `class << self` in
the slice would put `opaque_` on exactly the classes we want rows at. The answer
would then be to model the eigenclass — a larger project than the frame was, and
a prerequisite rather than a tweak.

---

## Kill criteria, fixed in advance

| outcome | decision |
|---|---|
| E2 blows up | redesign the footprint representation before proceeding |
| E1 < 1.2× | the frame is not this slice's bottleneck; park it at what is built and invest in overloads |
| E4 finds `opaque_` on needed classes | eigenclass modelling becomes the prerequisite |
| **E3's negative case accepts** | a real soundness bug in `Install.conflicts`; stop everything and fix it |

## Recommended ordering

**E2 → E3 → E1**, about a day. E4 only if E1's numbers make the slice look
reachable: it is the most expensive of the four and the least likely to surprise,
given §4's measurement that the chain graph is static after boot.

That order buys the two things worth having — a hard answer on whether the
kernel will pay for this at all, and one concrete artifact of the form *"here is
a program the checker accepts only because of the frame, and here is the
near-identical one it still rejects."* That is the only kind of evidence that
survives someone disagreeing with the design.

## Where results go

Numbers into `HANDOFF-SF.md`'s session log, verdict into `slot-frame.md` §10 as
a dated line. A failed experiment is recorded with the same weight as a passed
one; the point of fixing thresholds beforehand is to make that cheap to do
honestly.

---

## Results (added 2026-08-29, after running E2 → E3)

Run in `../../spikes/slot-frame/`; raw numbers, tables and `run.sh` in
[`../../spikes/slot-frame/RESULTS.md`](../../spikes/slot-frame/RESULTS.md),
session log in `../../ruby-ruby-lean/notes/model/HANDOFF-SF.md`, verdict in
[`slot-frame.md`](slot-frame.md) §10.

* **E2 — pass.** 0.32 s at 25 rows × the largest real slice AST, `decide` only,
  linear in both dimensions. Footprint representation stays as built.
* **E3 — pass, negative case included.** The control rejects with `rowsGuarded`
  as its only failing conjunct; the frame buys the accept; the redefining program
  still rejects, and `frameOkB` alone accepts a benign install while rejecting a
  redefinition of either read slot. No bug in `Install.conflicts`.
* **E4 — fail, measured as a byproduct** (E2 needed the ASTs). Every
  certificated slice file carries `opaque_` sites and all of them are
  `def self.x`. Eigenclass modelling is the prerequisite. Also: this memo's E4
  pass criterion (`opaque_` on classes a row reads) is **not** what
  `InstallN.framedBy` implements — it is class-blind, so any `opaque_` anywhere
  rejects. Count sites.
* **E1 — not run.** It sizes the prize; E4's result changes what the park-or-invest
  decision is about, so E1's number is no longer the next thing worth knowing.
