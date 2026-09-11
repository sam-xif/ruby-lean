# ratchet — hand-off note (2026-09-10)

> **EMERGENCY EXIT INVOKED, clink 64** — see `implementation-notes.md` §EMERGENCY EXIT for the
> statement and the evidence. In one line: the ladder counts one rule at a time and 26 of the 35
> remaining rules only come out *together*, at the end of a layer that is several sessions long,
> so three consecutive sessions of verified work have left the number at 48. The recommended fix
> is a **ladder** change, not a proof change — count **conditional rungs** (`StepSound →
> Obl.Judge.if'` is a real theorem and the layer hypothesis is already a named `Prop`), which
> would have counted most of clinks 62–64 without weakening anything.

> **Superseded again, 2026-09-10 (clink 63): `enterUserMethod` is PROVED, and the "one
> transcription away" note below is wrong about the transcription.** Hand-splitting the
> conditions does not work — see `Denote/Sem/notes.md` §The nineteenth stall point (nine `let`s,
> a nine-field projection literal, and `generalize … at h` silently abstracting nothing because a
> hand-written `match` is a fresh matcher constant). What works is
> `Denote/Sem/StepAct.lean`'s **mirror gated by `rfl`**: the same function with its five
> machine-touching stages named, `enterUM_eq` by `rfl`, walk in 18 s. **Read that file's header
> before touching any other `Interp/` let-chain**, because `finishSend`, `invokeDispatch`,
> `startArgs`, `tryReflect` and `evalExpr` are the same shape.
>
> **`tryMixin` and `defineAttr` landed too, so stage 2 is complete except `enterClassBody`**
> (deprioritised — declaration family), **and stage 4 is thirteen of fifteen**
> (`Denote/Sem/StepReflect.lean`).
>
> **Stage 4 is complete and `Step.dispatchMiss` is proved — the miss path is closed.**
>
> **The resume point is the twentieth stall point** (`Denote/Sem/notes.md`): `Builtins.run` answers
> four ways and three carry a machine, but every walk under it (`builtins_run_locals`,
> `builtins_run_cap`, `Step.builtins`) is stated over **`.ok` alone** — so a builtin that *raises*
> is outside the layer, and `invokeDispatch` cannot be closed. Try (1) first: generalise the
> statement over the result (`∀ r, Builtins.run … = r → LocalsSame m (mOf r)`) and re-run the
> existing `builtin_arms`/`cap_norm` tactics; that is one measurement rather than a new walk. After
> that the **dispatch spine** (`invokeDispatch`/`invoke`, then stage 3's `finishSend`/`startArgs`)
> is unblocked for the first time. Read `Denote/Sem/StepReflect.lean`'s header first: it lists the
> two relation-level corrections (`PreAct` is false across `defineMethod`; `PayKeep` is the
> interface for `eigenclassOf`) and the ordering rule's fifth and sixth costumes.
> `PreAct` (`StepSupport.lean`) is the transport every allocating-then-pushing helper needs, and
> the six `methodIn` bridges are on file, so a new caller of `enterUserMethod` costs one line.
> **The ladder is unchanged at 48/83 and none of this moves it directly.**

> **Superseded in one respect, 2026-09-10 (L269, clink 62): `BuiltinsSeal` is PROVED.**
> This file's resume point was "re-attempt the `Builtins` layer walk". That walk is done —
> `Denote/Sem/BuiltinsCap*.lean`, all six dispatchers plus `Builtins.run`, axiom-clean, seconds
> each — and `builtinsSeal`/`builtinsFramesWF` close the eighteenth stall point: `Sealed` survives
> `Builtins.run`. Read `implementation-notes.md` clink 62 and `Denote/Sem/notes.md` §The second
> walk (eight tactic measurements) before starting anything else in this layer; the two that
> transfer are *put the arm's shape in a `rfl`-provable hypothesis and leave the conclusion
> first-order* and *a `simp` in a 600-arm walk is a search, not a step*.
>
> **The new resume point is the next step of the same layer**: `Sealed.push`/`pop`/
> `alloc_closure` at the *interpreter*'s six frame pushes, `ClosuresOk`'s exactness component
> (the sixteenth stall point sized it; note it needs a third escape for a closure a *builtin*
> created), and then the per-arm `stepFn` walk. After that come jump-freeness and the `frameK`
> decomposition, which the fifteenth stall point argues cannot be sequenced apart. **The ladder
> is unchanged at 48/83 and none of this moves it directly** — `if'`/`ifNoElse`/`begin'` and the
> 22 call rules come out at the end of the whole layer, not in stages.
>
> Also new: `found-issues.md` **§F22**, a third independent reason `Judge.casgn`'s obligation is
> false (`constAsgnOk`'s guard list is not the set of class names a `Ty` can carry, and `Regexp`
> is outside it). Not reachable. It means `casgn` is two fixes away, not one.

## The 2026-09-08 note, unchanged below


> Written after clink 60 so a fresh-context agent can pick up the **semantic
> ratchet** without re-deriving the last session. Read [`AGENTS.md`](AGENTS.md)
> §Semantic ratchet status first, then `Denote/Sem/notes.md` in full; this file
> is only the resume point and the one correction that arrived after the clink
> was written.

## Where the ladders stand

| Ladder | Reads | Script |
|---|---|---|
| Syntactic (*reach*) | **178 / 259** rungs certified, 35 expect_validate mismatches, agreement 0 disagreements | `scripts/run_ratchet.sh` (now over `corpus-untyped/`) |
| Typed pipeline (*Sorbet in the loop*) | srb clean **184/259**, derivation emitted **75/259**, `validateD` (a **shape check**, not typing) accepts 75 | `scripts/run_typed_ratchet.sh` |
| Clink registry (*what the judgment may contain*) | **48 registered**, each proved by construction; **35 rules not in the judgment** (coverage, not debt) | `scripts/run_denote.sh`, or `lake exe semladder` |

`checkrungs corpus-untyped` reads 177/177 hand derivations + 148/148 negative
controls.

**The third row changed meaning on 2026-09-11** and the old reading (*47 of 83
`Judge` rules discharged*) is gone. The judgment is now generated from the
proofs (`Denote/Clink/`): a rule enters `JudgeC clinks` only as a `Clink`, whose
`sem` field *is* the semantic proof, so `registry_sound` is unconditional at
every registry size and an unregistered rule is not an obligation owed — it is
not a rule. `lake exe semladder` exits nonzero only if the registry **shrank**;
`Denote/Clink/Registry.lean`'s growth gate fails the build if a `Judge`
constructor appears that is neither registered nor a named legacy exception.
See `AGENTS.md` §The clink registry and `implementation-notes.md` clink 65.

## The resume point, in one paragraph

The semantic ladder is halted, and **not** because a rung is hard. All 36
remaining rules sit behind one of four unbuilt layers (`Denote/Sem/notes.md`
§Where the remaining 36 rules sit). The layer that gates the most —
`if'`/`ifNoElse`/`begin'` directly, and the 22 call rules through
jump-freeness — is the **locals layer**, and its invariant `Sealed`
(`Denote/Sem/Locals.lean`) is not preserved by `Builtins.run`.
`Denote/Sem/StepLocal.lean`'s `not_BuiltinsSeal` is the refutation.

## …and the correction that came after the clink

Clink 60 read that as an invariant redesign. **Probing against CRuby says it is
a bounded model-fidelity fix instead** (`found-issues.md` §A6, and the probe
results appended to the eighteenth stall point):

```
:upcase.to_proc.binding          # => ArgumentError (C-level Proc)
:upcase.to_proc.source_location  # => nil
```

CRuby's `Symbol#to_proc` proc has **no binding at all**, so the model's
`captured := 0` is a capture edge the reference semantics does not have —
forced by `Closure.captured : Nat` (`../lean/RubyCore/Heap.lean:136`) where
`Frame.captured` is already `Option FrameId`
(`../lean/RubyCore/Machine.lean:57`). `Sealed.clos` reads exactly that field.

**So: try the `Option` first, then re-attempt the `Builtins` layer**, before
designing a joint frame-graph/control-state invariant. **And add a third clause
while you are there** — see the next section. Two construction sites
(`Builtins/Strings.lean:449` and `Interp/Support.lean:448` — the `&:sym`
`coerceToProc` path builds the same closure, so the fiction is not confined to
the `Builtins` layer), ~4 readers in `RubyCore/Interp/`, 14 files in
`RubyCore/Proof/`, 12 in `Denote/`. It changes the *machine*, so the whole
difftest and all 47 rungs have to be re-verified.

`not_BuiltinsSeal` stands either way: it is a theorem about `Sealed` and
`Builtins.run`, both definitions in this repo, so fidelity does not bear on its
truth. What moved is the prognosis.

## What the `Option` fix does and does not buy (enumerated 2026-09-08)

Every writer of the two things `Sealed` reads was enumerated; the model is small
enough for this to be exhaustive (`Denote/Sem/notes.md`, the eighteenth stall
point's third subsection).

- **Closures close.** Three `.proc` allocations exist. `reifyBlock` captures
  `m.stack.headD 0` — the current frame, which is *on the stack*, so
  `Sealed.stack` discharges it and it was never a problem. The other two are the
  `:sym.to_proc` fiction and go to `none`.
- **Six `frames.push` sites**; four default `captured` to `none`. Of the two that
  set it, `callClosure` reads a `Closure` from the heap (that is what
  `Sealed.clos` is for) and **`enterUserMethod` reads
  `MethodDef.capturedFrame`, which `Sealed` does not mention at all.**
- **So a third clause is needed**, over methods installed in the heap.
  `define_method` is the writer, and the hazard is real on both executors:
  `x = 1; Object.send(:define_method, :setx) { x = 2 }; def g; setx; end; g; x`
  is `2` under CRuby *and* the model.
- **The third clause is closed**, which is the point: `reflectDefineMethod` takes
  its `capturedFrame` from a closure already in the heap, so `Sealed.clos`
  discharges it. Every other `MethodDef` writer either defaults the field to
  `none` or copies an already-installed method. J33's capture erasure makes it
  vacuous for any body that reads no local.

**Verdict:** `Sealed` + the `Option` + a `MethodDef` clause is three clauses that
discharge each other, with no writer left over — the control state does not have
to enter the invariant after all. Not a proof: it says no arm is blocked in
principle, and the per-arm `stepFn` walk is still the work. Measure the new
clause at the booted machine (`Denote/Sanity.lean`, `MethodsExact`'s shape)
before writing it down.

## DONE (2026-09-08, L266) — and one thing it does **not** cover

**Implemented.** Read the box at `Denote/Sem/notes.md` §The decision for how the
work differed from the plan (three departures, two of which changed a definition's
*shape* rather than its parenthesisation). Re-verification, all green: difftest
tier 0 1304/992 agree/**0 disagree**, corpus agreement 254/254, `checkrungs`
177/177 + 145/145, `run_ratchet.sh` **178/254** (unmoved), `semladder` **47/83**
(denominator still 83), `lake build` clean in both packages, no `sorry`.

**`not_BuiltinsSeal` is retired.** It was a true theorem about two definitions in
this repo, and L266 changed one of them: `Symbol#to_proc`'s Proc now captures
`none`, so `Sealed.alloc`'s premise holds for it. `toProcSealsB` (`#guard`ed)
replaces `toProcBreaksB`. `BuiltinsSeal` itself is still **stated and unproved** —
one builtin measured is not the layer walked, and re-attempting that walk is the
resume point now.

**Baseline finding, unrelated and not fixed:** `lake build Metatheory` is red at
HEAD, three pre-existing breaks — `found-issues.md` §A7. One of them
(`startArgs_lambda`) is a *false statement*, not a broken script.

---

**The original decision, for the record (2026-09-08):** `Closure.captured` becomes `Option FrameId` (matching
`Frame.captured`, which always was one) and the two `:sym.to_proc` construction
sites take `none`. Eight sites in the model proper, listed in
`Denote/Sem/notes.md` §The decision, plus the `cl.captured` statements in
`RubyCore/Proof/Static/{Konts,Locals,Iter,LambdaArrow}.lean` and in
`Denote/{Apply,Local,Ext}.lean` + `Denote/Sem/Locals.lean`. Behaviour-preserving
(`callClosure` keeps reading the same frame via `.getD 0`; only the pushed block
frame's own `captured` becomes `none`, and the body's free names are its own
parameters). **Changes the machine**, so difftest and all 47 rungs need
re-verification.

**TRACKING — this is not a general fix.** It is right for exactly the two sites
where the model *invents* a Proc for a Symbol. When `&obj` learns to dispatch a
**user-defined `to_proc`** — `coerceToProc` gates it today ("block-pass of a
non-Proc (to_proc dispatch is L2)") — the Proc returned is an ordinary
`reifyBlock` closure over a real frame and it *will* capture. The `none`
shortcut neither breaks nor helps there; `Sealed.clos` carries it like any other
user closure. **Explicitly out of scope right now.** Re-read
`found-issues.md` §A6a and `Denote/Sem/notes.md` §The decision before assuming
the seal still closes once L2 lands.

**Rejected alternative**, recorded so it is not re-proposed: keep `captured := 0`
and discharge the allocation with a lemma that unfolds `Symbol#to_proc` and shows
its closure body mutates nothing in whatever frame it names. It does not
discharge `Sealed` as stated (that clause is about the capture *graph*, so you
would first have to weaken it to "…or this closure is inert" — and that escape
is what drags the unconditional `stack` clause into control-state territory), it
does not generalise to the user-defined `to_proc` above, and it leaves the
fidelity gap standing for every future proof to pay again. Full reasoning in
`Denote/Sem/notes.md` §The decision.

**Also drafted, not implemented:** the **`MethodDef` arm** of `Sealed` — the
third clause, its `FramesWF` twin, what consumes it (`Sealed.push` at
`enterUserMethod`), and the writer-by-writer argument that it is closed. Both it
and the existing `clos` clause are **vacuous at the booted machine** (0 capturing
methods, 0 Procs — `lake env lean probes/measure_captures.lean`), so the arm
costs no vacuity risk.

## Two things worth not re-deriving

- **The seal is guarding a real hazard.** `x = 1; f = lambda { x = 2 }; def
  g(p); p.call; end; g(f); x` is `2` under CRuby *and* under the model, while
  the same shape with a `to_proc` proc leaves `x` at `1` on both. So the
  sixteenth stall point's witness is genuine and `Symbol#to_proc` is not an
  instance of it.
- **`Judge.if'` is not the cheapest remaining rung**, despite `semladder`
  listing it first (it prints the inductive's constructor order). All six
  narrowing type-lemmas are proved and `stateOk_narrow_then`/`_else` are
  assembled, but `if'` is blocked *twice*: by the `&&` sandwich's `thenOnly`
  refinement (the locals layer) and by the eleventh stall point, where
  `joinEnv` synthesizes an alias nobody promised. There is no cheapest
  remaining rung.

## Reproducing the probe run

```sh
cd ruby && python3 ratchet/probes/seal_fidelity_probes.py   # writes /tmp/probes
cd difftest && uv run python -m difftest replay /tmp/probes --sut lean
```

20 programs, 17 agree / 2 disagree / 1 gate against CRuby 4.0.5. The two
disagreements are §A6b (`Symbol#to_proc` is not identity-stable — CRuby interns
per symbol) and §A6c (the zero-argument `ArgumentError` message); the gate is
`Proc#arity`, unmodeled.

## The working rule this session paid for twice

**Write the layer's target down as a named `Prop` before proving the layer under
it.** `FrameLocal.lean`'s 532 lines were proved for a target that was never
stated, and the target turned out to be false. The same lesson is what
`not_KontFrame` bought in clink 52.
