# `Denote/notes.md` — the semantic denotation, and the choices that were not forced

`AGENTS.md` §Semantic denotation says what this folder is. This file records the decisions
inside it that could have gone another way, in the same spirit as
`../notes/ratchet/implementation-notes.md`'s clinks — but kept local, because `Denote/` is maintained
separately from the ratchet's rung count and does not move it.

## Why a separate folder at all

`Ratchet/Judge.lean` is a **syntactic** judgment: `Judge : Expr → Ty → Prop`, one
human-checkable constructor per rule, and `Ratchet/Validate.lean` decides its fragment. What
it is *not* is an explanation of what a `Ty` means. Every soundness argument in
`Ratchet/Proof/ChkSound.lean` is therefore syntactic: `validate_sound_syntactic` says `chk`
agrees with `Judge`, and `Judge` is taken as the specification. Ask "and why is `Judge`
right?" and the current answer is prose in a docstring plus, for thirteen rungs,
`CheckRungs.lean`'s comparison of the result's **class name** against `expectedClasses`.

A denotation makes the question answerable. It also has a different shape from a judgment —
it recurses on `Ty`, not on `Expr`; it mentions `Heap`/`Value`/`Machine`, which `Ratchet/`
deliberately does not import; and it is not a checker, so its ratchet is theorems and
`#guard`s rather than rungs. Three reasons for a folder rather than a file, and the
dependency arrow makes it four: `Denote/` imports `Ratchet/Ty.lean` **and** `Semantics/`,
which nothing else in the package does.

## The two-language boundary

`Denote/` is the *second* place allowed to see both sides (`CheckRungs.lean` was the first,
and its docstring says so). The arrow points one way in both:

```
Ratchet/  ──copied text──▶  (nothing)
Semantics/  ──imports──▶  RubyCore/
Denote/  ──imports──▶  Ratchet/Ty.lean  +  Semantics/Interp.lean
```

`Denote/` imports `Ratchet/Ty.lean` and nothing else from `Ratchet/` — **not**
`Ratchet/Expr.lean`. That is deliberate and it is the reason `Ty.clos`'s `idx` field has no
denotation: `idx` indexes the checker's table of `Ratchet.Expr` block literals, and
`Ratchet.Expr` and `RubyCore.Expr` are two separately-copied inductives with no coercion
between them. Comparing a heap `Closure.body : RubyCore.Expr` against a table entry's
`Ratchet.Expr` would need a translation function whose correctness is its own project. So the
`clos` arm denotes the parts that *are* comparable — the captured scope, the creation `self`,
and Proc-hood — and the behavioural content is reached through the arrow instead.

## Heap-indexed or machine-indexed: the one decision that shaped the file

The brief asked for `Ty → Heap → Value → Bool`, and for every first-order type that is
exactly right. It cannot be right for a Proc, and the reason is a fact about the model rather
than a preference: `RubyCore.Closure.captured` and `.home` are `FrameId`s — indices into
`Machine.frames` — so **a closure's captured environment is not in the heap**. Given a bare
heap there is no way to reconstruct the scope a lambda closed over, and `Interp.callClosure`
would run its body against `frames.getD cl.captured default`: a default frame, wrong `self`,
no captured locals. The call modelled would not be the call the program makes.

Three ways out were available.

1. **Denote `clos`/arrow nominally** ("is a Proc") and stop. Cheap, and it throws away the
   entire point of the exercise — an arrow type whose denotation cannot mention a call is not
   a denotation of an arrow.
2. **Keep the heap signature and quantify over all machines with that heap.** Superficially
   attractive (it stays `Heap`-shaped and is a *stronger* obligation) and it is unusable:
   a machine with the right heap and arbitrary frames makes the closure's `captured` index
   point at garbage, so the obligation is false for procs that are perfectly well-typed. A
   specification nothing can satisfy is not conservative, it is broken.
3. **Make the master definition machine-indexed and prove the heap view adequate where it
   is.** Chosen. `denM : Ty → Machine → Value → Prop` is the master; `den : Ty → Heap →
   Value → Prop` is `denM` at a bare machine; and `denM_heap_only` proves the machine
   argument is irrelevant for every arrow-free, `clos`-free type. So the brief's signature is
   met exactly on the fragment where it is meaningful, and the extra argument appears exactly
   where the model forces it — with a theorem, not a comment, drawing the line.

`FirstOrder : Ty → Bool` is that line, and it is a *hypothesis* of `denM_heap_only`,
`den_iff_denM`, `denB_iff` and `arrowCheck_of_arrowFlat` rather than a caveat in prose.

## The arrow: what "quantifies over machine states" cashes out as

`(A, B) → R` at machine `m`, applied to `f`, means: `f` is a Proc, and for every `a : A` and
`b : B` **at `m`**, if `f.call(a, b)` from `m` returns `v` in machine `m'`, then `v : R`
**at `m'`**. Four choices in that sentence, each of which could have gone another way:

* **Partial correctness.** A run that raises, diverges, gates (`.unsupported`) or jumps
  imposes no obligation. The alternative — requiring termination — is not available: `Ty` has
  no totality discipline, and `Ty.never` (the type of an expression that *does not return*)
  is defined by exactly this asymmetry. Making the arrow total would make `never`'s reading
  inconsistent with it.
* **Codomain checked at the post-machine.** Calling a proc can allocate, mutate, reopen a
  class, `define_method`. Checking the result against `m`'s heap would be checking it against
  a heap that no longer exists — and since the nominal arms are `isA` at *the heap they are
  given*, that is not a stylistic point: `.cls "Foo"` can be true at `m'` and false at `m`.
* **Domain checked at the pre-machine.** The caller has to supply the arguments before the
  call, so that is the state where the hypothesis lives.
* **Variance is not stipulated.** The domain sits in a hypothesis and the codomain in a
  conclusion, so contravariance/covariance are theorems about this definition rather than
  rules inside it. Nothing in `Denote/` mentions `subTy`.

**Currying was rejected.** `Ty`'s arrow is a params *spine* (`arrowCons A (arrowCons B
(arrow0 R))`) because `Ty` must stay simple-recursive, and it would have been easy to read the
spine as curried — "`A → (B → R)`". Ruby has no currying: `f.call(a, b)` is one call with two
arguments, and a curried denotation would be a claim about a `f.call(a)` that raises
`ArgumentError`. So `denApp` **gathers** arguments down the spine and states the obligation
once, at the `arrow0`. `denM_arrowOf` then proves the spine version equals the flat,
argument-list version (`ArrowFlat`) — which is the form to cite; the spine is an artifact of
staying structurally recursive.

**`ArrowStable` is the honest target, `ArrowFlat` is what is provable today.** A lambda is
almost never called at the state where it was created, so an arrow established only at `m` is
worth little; `ArrowStable` quantifies over every machine reachable from `m` by `Interp.stepFn`
(`Reaches`). It is strictly stronger, and only the trivial direction is provable
(`ArrowStable.here`) — the gap is Ruby's open classes: `define_method` on a class the body
dispatches to can invalidate a local arrow. Recorded as the specification a future
arrow-inferring rule must meet, not as something claimed.

## Why `denB` gives up on the arrow, permanently

`Denote/DenB.lean`'s `denB : Ty → Heap → Value → Bool` answers `false` on both arrow arms.
That is not a stub: the arrow is a universally quantified statement over every value in the
domain and every fuel, and no `Bool` decides it. `denB` is therefore **one-sided** — a `true`
is a real membership fact at every type (`denB_sound`, proved by its own induction because
`FirstOrder τ = false` does not localise: `nilable (arrow0 int)` is higher-order without
being an arrow), and a `false` means "not in it, *or* higher-order". On the `FirstOrder`
fragment the one-sidedness disappears and `denB_iff` gives an `↔`.

`Ty.clos`, by contrast, *is* decidable — once you have a machine. `closB` decides it, which is
what makes the arrow the only genuinely undecidable arm rather than one of three. The reuse
that made this nearly free is `denSpineB`'s `String → Value` parameter: an object's `ivarOf`
and a closure's `closLocal` are the same shape, so one spine denotation serves both of `Ty`'s
uses of the spine.

## Refuting instead of proving

`Denote/ArrowCheck.lean` is the arrow's computable half, and it is stated in the only direction
that survives contact with the undecidability: **a true arrow passes every sample**
(`arrowCheck_of_arrowFlat`), so a failing sample refutes the arrow
(`not_arrowFlat_of_arrowCheck_false`) and the sample is the counterexample. There is
deliberately no converse — passing samples say nothing, and `arrowSample` records its two
*skip* conditions (arguments not provably in the domain; the call did not return within fuel)
as skips rather than quietly counting them as passes.

This is the same shape as the rest of the project's checking story:
`../../bounded-effect-checking.md`'s bounded model checker and
`../../type-safety-by-reachability.md`'s witness-finding direction both run the semantics to
*find* a bad state, and are self-certifying by replay rather than by proof. `arrowCheck` is
that move applied to arrows.

## Relation to `RubyCore/HJudge/HTy.lean`

The real model already has a semantic denotation: `HTy.den : HTy → Heap → Value → Prop`
(judgment-layer J36), with a nominal core plus a `sem (P : Heap → Value → Prop)` door that
makes the language semantically complete by construction. This folder is **not** a
reimplementation of it and the difference is worth stating, since duplicating it would be the
obvious mistake:

* `HTy` is its own grammar, designed to be denoted. `Denote/` denotes **`Ratchet.Ty`** — the
  grammar the ratchet's checker actually infers, spine constructors, `sameAs` alias, `.never`
  sentinel in `clos` and all. Nothing is redesigned to be easier to denote; where the type
  language is awkward the denotation says so (§Two stated gaps in `Denote/Den.lean`).
* `HTy.den` is `Prop`-only and `sem` costs it `DecidableEq`/`Repr`/JSON by construction.
  `Denote/` carries a computable core (`denB`/`closB`) with an `↔` on the first-order fragment,
  because the ratchet's whole method is executable checks that can be `#guard`ed against real
  runs.
* `HTy.den`'s higher-order content goes through `sem`, an *arbitrary* Lean predicate — the
  priced escape hatch, admitted as a lemma. `Denote/`'s higher-order content is the **arrow**,
  a specific structure with a specific meaning (call it, look at what returns), so it can be
  refuted by execution rather than only admitted by proof. `HTy`'s own docstring names
  "behavioural content of the methods" as *not yet expressible* and flags step-indexing as the
  flip condition; the arrow here is a first cut at that content in the one case Ruby hands you
  a first-class callable.

If the two are ever unified, the direction is `Denote/` → `HTy.sem`: an `ArrowFlat` is
precisely a `Heap`-and-frames-indexed predicate, i.e. what `sem` was left open for.

## What is deliberately not built

* ~~**No `Judge` soundness theorem.**~~ **Taken up — see `Denote/Sem/notes.md`.** This entry
  used to read: "`Denote/` imports no `Judge` and states no `Judge e τ → ∀ …, den τ …`,
  because that theorem needs an evaluation relation for `Ratchet.Expr` and the only executable
  one in reach is over `RubyCore.Expr` (§The two-language boundary)." The missing piece was
  the translation, and `Denote/Sem/Trans.lean` is it — 48 arms, no default case, and it closes
  the `Ty.clos` `idx` gap in §The two-language boundary as a side effect. `Denote/Sem/` is the
  parallel judgment built on top: `SemJudge` with `Judge`'s exact signature, 83 obligations
  *derived* from the inductive rather than transcribed, and a ladder that counts them. Nothing
  discharged yet. `ClosArrow` (`Denote/Arrow.lean`) is still the shape of the bridge a
  `Judge.closCall` rung will need.
* **No `subTy` soundness.** `subTy σ τ → den σ ⊆ den τ` is the obvious next theorem and is
  not proved here; the denotation exists first so that it *can* be.
* **No narrowing soundness.** `truthyTy`/`falsyTy`/`isNilTy`/`nonNilTy` (`Ratchet/Ty.lean`,
  tier 12) each make a claim about Ruby's truth values that is now *statable* —
  e.g. `den (truthyTy τ) h v ↔ (den τ h v ∧ v.truthy)`. Statable, not stated.
* **No fuel-free execution.** Everything goes through `Interp.run`'s fuel loop, so
  `Returns` is `∃ fuel`. A fuel-free `Step`-relation version would be equivalent and is not
  needed by anything here.
