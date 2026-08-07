# Static soundness on the fully-typed fragment — a proof of concept

> **Status:** **P0a and P0b built and proved** (2026-08-07); P1 onward planned. This is deliberately the *smallest*
> soundness result the architecture can produce end-to-end, and it is sequenced **before**
> everything in [`typed-portion-safety.md`](typed-portion-safety.md).
>
> Evidence tags per [`README.md`](README.md): **[V]** verified in this workspace,
> **[D]** documentation or literature, **[?]** open, **[✗→]** a correction of a
> plausible-but-false claim.

---

## 1. Why this one, and why first

[`typed-portion-safety.md`](typed-portion-safety.md) §1 tabulates three targets and
dismisses the first — *static soundness on the fully-typed fragment* — as "`strong` is beta
and rare; true but about almost no code." That dismissal is correct about **coverage** and
wrong as a **priority**, for one reason:

> It is the only one of the three whose theorem is **unconditional**.

No rely condition, no `R1`/`R2`, no assume-guarantee, no measured hypothesis. `check P =
accept` is a fact about `P` that a program computes, and the theorem's conclusion follows
from it and nothing else. The job of a proof of concept is to establish that the
architecture — checker → soundness theorem → executable bad state over the real interpreter
— can deliver an unconditional result at all. Coverage is what the ratchet is for (§7), and
every later target reuses the same parts.

The three targets, re-sequenced:

| Target | Hypothesis | Coverage | Order |
|---|---|---|---|
| **Fully-typed fragment** | none | tiny, growable | **this document, first** |
| Whole-program three-outcome | whole program in fragment | 3/22 corpus | proved (L81) |
| Typed-portion safety | `R1`/`R2`, assumed + measured | every sig'd method | after; `typed-portion-safety.md` |

---

## 2. The shape

```lean
inductive Verdict | accept | unknown

def check : Expr → Verdict                            -- total, executable, difftested

theorem check_sound {P : Expr} (h : check P = .accept) :
    ∀ r, ReachableResult (initial P) r → ¬ typeStuck r
```

Certifying-checker pattern: the executable `check` is what runs, the theorem is what makes
its `accept` mean something. Two decisions are worth stating explicitly.

### 2.1 The conclusion is `typeStuck`, not `sorbetStuck`

`SorbetSafety.lean` weakens the bad state to `isTypeError ∧ ¬ isBlame` (L76) because a
*gradual* program's sig checks can legitimately fire — blame is the licensed outcome of the
three-outcome statement. **In a fully-typed fragment they cannot fire.** With no
`T.untyped` anywhere, a statically well-typed argument always passes its own wrapper check.

So the POC proves the *stronger* property — no uncaught type error at all, blame included —
and the blame carve-out is simply unnecessary here. This is a simplification, not a
weakening: `typeSafe_sorbetSafe` (`SorbetSafety.lean:119`) already derives the Sorbet
statement from the strong one.

### 2.2 `reject`, and what it does *not* claim

The lattice is three-valued. `unknown` remains the default and absorbs everything the
checker has no opinion about.

> `reject` says **our rules refute this program**. It does not say the program fails.

That asymmetry is inherent ([`typed-portion-safety.md`](typed-portion-safety.md) §8.1): a
refuted call may sit on a dead branch. `if false then 1 + nil else 0 end` is rejected here
and runs to `0`. Consequently `reject` is **not** backed by a Lean theorem — its guard is
the difftest direction `reject ⇒ srb rejects` (§7), which is why the failure mode to fear
is `reject` quietly becoming "anything the checker dislikes."

Two design choices keep that from happening.

**It is an independent second pass, not a third value threaded through `infer`.**
`infer`'s `none` conflates "outside the fragment" with "ill-typed". Splitting it would touch
every `KontOk` constructor and every case of preservation. Instead `check` consults
`illTyped` only when `infer` has already failed, so `check_sound` — a statement about
`accept` alone — is untouched, and the entire new obligation is confined to the new pass.

**Every doubt resolves to `unknown`.** `defTy` types only *unconditional* expressions and
takes no environment, so a local variable has no type; `tableRefutes` fires only when the
method is **present** in `builtinSig`, since the table is narrow by design; and `illTyped`
stops recursing at any node off the fragment's spine. Measured against `srb` 0.6.13405 [V]:

| Program | `srb` | `check` | |
|---|---|---|---|
| `1 + nil` | 7002 | `reject` | agrees |
| `1 + true` | 7002 | `reject` | agrees |
| `if false then 1 + nil else 0 end` | 7006 *unreachable* | `reject` | agrees — but on a **different diagnostic**, worth remembering when the difftest starts comparing reasons |
| `1 / 2` | accepted | `unknown` | `/` absent from the table; rejecting here would break the guard |
| `1.foo(2)` | 7003 | `unknown` | the table cannot tell "no such method" from "not tabulated" |
| `q = 1; q + nil` | 7002 | `unknown` | `defTy` has no environment — the obvious next widening |

---

## 3. What already exists

The metatheorem harness is **done** and is bad-state-agnostic, which is the running thesis
of [`../../type-safety-by-reachability.md`](../../type-safety-by-reachability.md).

| Asset | Where | Role |
|---|---|---|
| `invariant_sound` | `Proof/TypeSafety.lean:157` | takes any `I : Machine → Prop` + 3 obligations → `∀ r, ReachableResult → ¬ typeStuck r` |
| `SmallStep`, `Reaches`, `ReachableResult` | `Proof/TypeSafety.lean:97` | `SmallStep m m' := stepFn m = .next m'` — the **full** relation, not the control-core `Step` |
| `typeStuck` / `aboutToTypeStick` | `Proof/TypeSafety.lean:81` | the bad state, already executable |
| `Types/Fragment.lean` | Lean | reflective-send / missing-sig / `attr_*` / sig-level scan, as `Bool` — a good part of the "fully typed" gate |
| `Step.heap_monotone` | `Proof/Step.lean` | the one preservation ingredient already proved (`type-judgments.md` §8) |
| tier-4 corpus, `sorbet check` | `difftest/` | the difftest surface for §7 |

**What has to be written is `I` and its three obligations.** Everything downstream of `I`
is a five-line application.

---

## 4. The invariant, and the idea that makes it tractable

`invariant_sound`'s consecution obligation is over the **full** step function:

```lean
cons : ∀ m m', I m → SmallStep m m' → I m'
```

That is preservation against every branch of `stepFn` — the whole interpreter, including
`define_method`, `catch`/`throw`, and the prelude. Attacked naively it is unbounded work.

The move is to make `I` a **conjunction of a restriction and a typing**:

```
I m  ≡  InFragment m  ∧  WellTyped m
```

`InFragment` is a predicate on the *machine*, not on the source: which `Ctl` shapes, which
`Kont` constructors (`Machine.kont : List Kont` — `seqK`/`asgnK`/`casgnK`/`classDefK`/
`newK`/`methodAddedK`/… , `Machine.lean:140`), which `FrameKind`s, which heap payloads may
appear. Then the case analysis over `stepFn` splits in two:

- branches **excluded by `InFragment`** — discharged by contradiction, cheaply and in bulk;
- branches **admitted by `InFragment`** — the only places real typing work happens.

Getting `InFragment` right is therefore the whole engineering problem, and it is what
decides whether this is weeks or months. It is also why P0 (§8) is sized to measure that
cost before anything is committed to.

> **[✗→] What P0a actually found:** no separate `InFragment` predicate was needed. The
> restriction is already carried by `KontOk` (no constructor for the 43 inadmissible
> `Kont`s) and by `infer` returning `none` off-fragment. See §8.1(1) — the intuition here
> holds, the second conjunct does not.

**[?]** `InFragment` must itself be preserved, and it is the *stronger* of the two
conjuncts to maintain: a program that starts in the fragment must not step out of it. This
is where the static-class-table exclusions of §6 earn their place.

---

## 5. The prelude, and why the builtin signature table arrives at step one

`SorbetSafe` starts from `Prelude.initWithPrelude`, not `Machine.init`, and
`SorbetSafety.lean:88–99` explains why this is not a technicality: with no prelude there is
no core library, every Sorbet program dies on `NameError`, and the theorem says nothing.

Consequence for `I`: **the initial heap contains the entire prelude** — Enumerable,
Comparable, Range, all written in RubyCore — and none of it is in any typed fragment. So

> `WellTyped` cannot mean "every method in the heap is well-typed."

It must quantify over **user** methods only, with prelude methods and native builtins
carried by a declared **builtin signature table** `(class, method) ↦ Ty`, trusted by the
POC and discharged later.

That is the **RBI-conformance obligation** of [`typed-portion-safety.md`](typed-portion-safety.md)
§6 arriving at step one rather than at M3, and there is no version of this work that defers
it: `1 + 2` is a send, so even the most degenerate fragment needs `Integer#+`'s type. Its
mitigation is the one that document already names — our setting is *better off than
Sorbet's*, because the model defines the builtin, so conformance is differentially
checkable rather than assumed forever.

**P0b** holds a three-entry version of this table (`Integer#+`, `#-`, `#*`), and — the
result that matters — **it did not cost the unconditionality of `check_sound`**. See §8.2.

---

## 6. The fragment

| Admitted | Excluded |
|---|---|
| `Integer`, `String`, `NilClass`, `TrueClass`/`FalseClass`, user classes | generics, unions, `T.nilable`, proc types |
| single inheritance; nominal subtyping | modules/mixins, singleton methods, `super` |
| literals, locals, `vasgn`, `seq`, `if`, `while` | blocks/`yield`, exceptions, `catch`/`throw` |
| `send` with fixed positional arity | splat, kwargs, defaults, `fwd`, `vcall`-as-method |
| `def` with a complete sig, in a class body or at toplevel | `def` inside a method body |
| `class C < S`, ivar read/write, `.new` | class reopening, class variables, globals |
| — | every escape hatch and all of `T.*` |

Two exclusions are load-bearing rather than cosmetic, and both exist to keep the **class
table static after load** — which preservation needs, since `mtype` must be stable across
every step:

- **no `def` inside a method body**, and
- **no class reopening**.

Both are syntactically checkable at the source level, and `Fragment.lean`'s
`reflectiveSend` list already closes the metaprogramming route to the same violation
(`define_method`, `*_eval`, …).

Excluding blocks excludes most of Enumerable. That is acceptable and intended: typed code
in this fragment simply cannot call it, and `unknown` absorbs the programs that try.

---

## 7. Ratchet and difftest

One direction only, exactly as [`typed-portion-safety.md`](typed-portion-safety.md) §8
argues: **soundness is proved, not tested.** What difftesting buys is *relevance* —
evidence that `check` formalizes Sorbet rather than a type system we invented.

> `check P = accept` ⇒ `srb tc` reports no error in `P`

Failures the other way (`srb` accepts, `check` says `unknown`) are **incompleteness** and
are the expected state of a growing checker; they must not fail the run.

> `check P = reject` ⇒ `srb tc` reports **some** error in `P`

### 7.1 What the relation has to exclude, measured

Stating the accept direction as the bare *"⇒ `srb` accepts"* of
[`typed-portion-safety.md`](typed-portion-safety.md) §8.1 does not survive contact with
`srb`. Measured over the 1304-program bootstraptest corpus [V, srb 0.6.13405]:

| | count |
|---|---|
| `check` accepts | 21 |
| `check` rejects | **0** |
| `check` unknown | 1190 |
| pipeline failure (export/decode) | 93 |

Of the 21 accepts, **8 draw an `srb` error, and every one of them is benign**:

- **7006** — *unreachable code* / *left side of `&&` was always truthy*, on
  `if true then 1 else 2 end`, `1 && 2 && 3 && 4`, `1 || 2 || 3 || 4` and kin (7 programs).
  The programs are well typed; `srb` is reporting that a branch cannot run. We have no
  reachability analysis and claim none.
- **3002** — *unsupported integer literal*, on `123456789012345678901234567890` (1 program).
  An `srb` implementation limit, not a statement about the program's types.

So the naive guard would fire on **38% of its own accept population** on day one, and every
firing would be noise. A pinned zero that is routinely overridden is worse than no zero, so
the relation is refined rather than the ratchet weakened:

```
accept  ⇒  srb reports no error in a type-relevant class     (7006, 3002 excluded)
reject  ⇒  srb reports some error, in any class
```

The asymmetry is deliberate. `accept` is the strong claim — backed by `check_sound` — so it
gets the strong test. `reject` claims only that our rules refute the program, so it gets the
weak one; it also *must* be the weak one, because our dead-branch rejects are witnessed by
`srb` **only** through 7006.

**Exclusions are enumerated, justified, and closed.** An `srb` error code the harness has
never seen fails the run rather than being silently absorbed — the noisy choice, because the
quiet one is how the exclusion list turns into a place to hide disagreements.

### 7.2 Agreement on the verdict is not agreement on the reason

`if false then 1 + nil else 0 end` is rejected by us for `1 + nil` and by `srb` for 7006.
Verdict-only comparison scores that a win. It is not one, so `reject` splits into two
recorded outcomes — **agrees-on-reason** (some type-relevant `srb` error) and
**agrees-on-verdict-only** (excluded errors only). Only the second is a coincidence, and
watching it is the cheap approximation of the site-level comparison §8.3 defers.

### 7.3 The third zero is free, and it tests the model

The engine already runs CRuby. Crossing that with the checker gives one cell worth more
than the rest:

> `check` accepts **and** CRuby raises a type-family error ⇒ **model bug**

`check_sound` is proved, so this cannot indicate a checker bug — only that the Lean model
and CRuby disagree, i.e. an adequacy failure. The harness is therefore also an adequacy
probe, at no extra cost.

**The metric:** `unknown`-count declining, with **three pinned zeros** —
accept-vs-`srb`, reject-vs-`srb`, and accept-vs-CRuby. `unknown → accept` and
`unknown → reject` are equally risky transitions and get the same guard; only `unknown` is
free.

---

## 8. Milestones

| # | Work | Exit criterion |
|---|---|---|
| **P0a** | `Ty`; `KontOk`/`CtlOk`/`Inv` over `Machine`. Fragment: literals, locals, `if`, `while`, `seq`. **No `send`.** | **DONE** (2026-08-07) — `check_sound` proved, axiom-clean, two worked examples. |
| **P0b** | `send` for `Integer` builtins only + the signature table of §5. Fragment gains `1 + 2`. | **DONE** (2026-08-07) — three entries, conformance proved, `check_sound` still unconditional. See §8.2. |
| **P1** | User classes, sigs, single inheritance, ivars, `.new`, user method dispatch. | A corpus program with real methods accepted and proved safe. |
| **P2** | `check` wired as a total executable into `sorbet check` + difftest, both directions of §7. | Both pinned zeros hold over the 22-program tier-4 corpus; `unknown` baseline recorded. |
| **P3** | Widen by one axis — `T.nilable` + narrowing, **or** arrays with element types. | `unknown` down, zero held. |
| **P4** | `T.untyped` re-enters — the gradual boundary, and where `typed-portion-safety.md` resumes. | — |

P0 is almost degenerate **on purpose**. Its deliverable is not the theorem, which is nearly
trivial at that scope; it is the measured cost of typing the *continuation stack*
(`KontOk`/`ConfigTy`, `type-judgments.md` §10 T1). That is where machine-level preservation
proofs actually get long, and the number is wanted before P1's scope is fixed.

### 8.2 P0b as built — the table did not cost unconditionality

`Types/Core.lean` gains `builtinSig` and a `send` rule;
`Proof/BuiltinConformance.lean` discharges the table against the interpreter;
`Proof/StaticSoundness.lean` gains `TableOk`, two `KontOk` constructors, and the send
cases. `check_sound` and `egArith_safe` (`x = 3; (x + 1) * 2`) are axiom-clean, and the
model runs that program to `8` through the real dispatch path, so the theorem is not
vacuous [V].

**(1) The headline worry was wrong, in the good direction.** §5 warns that the builtin
table is trusted. It is — but only as a statement about *the heap*, and
`TableOk Boot.initHeap` is provable **by `rfl`**. So `check_sound` remains unconditional:
no hypothesis leaks into the theorem, and RBI-conformance is discharged rather than
assumed. This is a direct dividend of L73's reducibility discipline; had any step of the
dispatch path been `partial` or gone through `String.endsWith`, the discharge would have
needed `native_decide` and the theorem would have inherited `ofReduceBool`.

Caveat, stated plainly: this holds for `Machine.init`. A **prelude-booted** start (P1) will
almost certainly need `native_decide` for its `TableOk`, at which point the split has to be
the `SorbetConcrete.lean` one — general theorem clean, concrete instance dirty.

**(2) Conformance is a fact about dispatch, not about the machine.** First cut stated it as
"`m.ctl = …`, `m.kont = argsK … ⟹ stepFn m = .next …`". That proves, but does not compose:
by the time preservation reaches the `argsK` case it has already unfolded `applyKont`. The
lemmas are now about `startArgs` with receiver and argument already values.

**(3) `Builtins.run` reduces by `rfl` instantly and is fatal to `simp`** (maxRecDepth, then
heartbeats, on a 1582-line match). L73's rule generalizes: on this path, `rfl` to prove,
`#eval` to debug, never `simp` through the builtin table.

**(4) The send site is syntactic.** `evalExpr` picks `.selfRecv` vs `.explicit` by matching
on the receiver *expression* (`Interp.lean:2582`), and that match will not rewrite under
`rw` or `simp only`. It has to be forced to compute with `cases r`; every branch but
`self'` is `.explicit`, and `infer` rejects `self'`.

**(5) Scope, stated honestly.** The fragment admits only a binary send with an explicit
receiver, exactly one argument, no block, and a method in the three-entry table. Widening
the table is now a `rfl` lemma plus a three-line instantiation of `int_bin_dispatch`; that
cheapness is the point of the parameterization, and it is the ratchet's next easy win.

### 8.1 P0a as built — what the measurement said

`lean/RubyCore/Types/Core.lean` (checker) + `lean/RubyCore/Proof/StaticSoundness.lean`
(proof). `check_sound` is proved and depends on `[propext, Classical.choice, Quot.sound]`
and nothing else — the same baseline as `Proof/SorbetSafety.lean` [V].

Four findings, two of them corrections to this document's own plan.

**(1) [✗→] No separate `InFragment` predicate was needed.** §4 proposed
`I ≡ InFragment ∧ WellTyped`, with the restriction conjunct doing the bulk discharge. In
practice the restriction is *already carried* by the typing relations, in two ways that
cost nothing:

- `KontOk` simply **has no constructor** for the 43 inadmissible `Kont`s (5 of 48 are
  admitted), so `cases` on it enumerates only the fragment;
- `infer` returns `none` outside the fragment, so the ~40-way `Expr` split collapses to one
  tactic line — `cases e <;> try (simp only [infer] at hinf; contradiction)` — which
  discharges 31 constructors at once.

The §4 intuition was right; the *mechanism* is the checker's own partiality, not a second
predicate. That is a genuine simplification and it should carry into P1.

**(2) The dominant cost was not the continuation stack.** `KontOk` came to 8 constructors
and its preservation cases were mechanical. What actually cost the most was **local-variable
access**: `Machine.getLocal`/`setLocal` walk the `captured` frame chain
(`Machine.lean:324–352`), so nothing about them reduces without knowing the frame shape. P0a
had to add a `Flat` hypothesis (one frame, `captured = none`) and prove four lemmas —
`getLocal_flat`, `setLocal_owner_zero`, `setLocal_frame`, `getLocal_setLocal`, plus a list
lemma `find?_filter_ne` — before any typing argument could start.

**This is the number P0 was for, and it re-prices P1.** `send` pushes frames, so `Flat`
dies immediately and the `captured`-chain reasoning has to be done properly rather than
assumed away. Budget P1 for *frame-store* lemmas first and continuation typing second — the
reverse of the expected order.

**(3) [✗→] P0a did not de-risk the builtin signature table.** §5 argues the table arrives
"at step one" because `1 + 2` is a send. True — and P0a avoided it by excluding `send`
entirely, so the fragment cannot express `1 + 2` at all. The risk §5 identifies is
*undiminished*; it is simply deferred to **P0b**, which now exists as a milestone for that
reason alone. The claim in §5 stands; what changed is which milestone pays it.

**(4) `decide` cannot run the checker.** `infer` is well-founded-recursive (three mutually
recursive functions over `Expr`/`List Expr`/`Option Expr`), so kernel reduction gets stuck
and the §5 examples are discharged by `simp` over the generated equation lemmas.
`native_decide` would work but costs `ofReduceBool`, which would break the axiom baseline —
not worth it. If P1's programs get large enough that `simp` is slow, the fix is a
structurally-recursive reformulation, not `native_decide`.

---

## 9. Open questions [?]

- **[?] `InFragment` preservation** (§4): is the syntactic restriction enough to keep the
  machine in the fragment, or does it need heap-shape clauses too? Expected answer: heap
  clauses are needed as soon as P1 admits user objects.
- **[?] Where the sig lives at runtime.** The `T` shim (`prelude/prelude.rb`, L80) records
  sigs in the heap. `WellTyped` needs `mtype` for user methods — read it from the heap the
  shim built, or from a static side table computed by `check`? The side table is simpler to
  reason about but adds an agreement obligation between it and the runtime.
- **[V] `initial P` — settled.** `check_sound` is stated over `Machine.init P`, which is
  sound for P0a because a `send`-free fragment never touches the prelude. The general form
  `sound_from : Inv m₀ → …` is proved separately, so the prelude-booted start
  (`SorbetSafety.lean:100`) is an *instance* rather than a restatement — nothing to redo at
  P0b.
- **[?] Does the fragment need `puts`?** Corpus programs observe via stdout; a fragment
  that cannot print has no difftestable behaviour. Likely the first builtin-table entry
  after `Integer`.

---

## 10. Relation to the rest of the workspace

- The bad-state swap is **not** used here — this is the first target to reuse `typeStuck`
  *unmodified*, which is the cleanest possible instance of the
  [`../../type-safety-by-reachability.md`](../../type-safety-by-reachability.md) thesis.
- `Ty`/`Sub`/`Δ`/`HasType`/`KontOk` are the **T1** row of
  [`type-judgments.md`](type-judgments.md) §10, with one change: the obligation is
  discharged against `stepFn` via `invariant_sound`, **not** against the inductive `Step`
  relation of `Proof/Step.lean`. That avoids extending the relation and re-doing adequacy,
  at the price of a larger case analysis — which §4's `InFragment` conjunct is what pays.
- `type-judgments.md` §9's `gradual_safety` statement is looser than the theorem actually
  proved in `SorbetSafety.lean` (its middle disjunct admits *any* `TypeError`, where the
  proved version requires `¬ isBlame`). Unrelated to this POC but noted here because it was
  found while scoping it. **[✗→]**
- Everything in [`typed-portion-safety.md`](typed-portion-safety.md) resumes at P4, with
  `check`'s `unknown` already playing the role its §8.3 assigns to `Types/Fragment.lean`.
