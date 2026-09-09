# ratchet — hand-off note (2026-09-08)

> Written after clink 60 so a fresh-context agent can pick up the **semantic
> ratchet** without re-deriving the last session. Read [`AGENTS.md`](AGENTS.md)
> §Semantic ratchet status first, then `Denote/Sem/notes.md` in full; this file
> is only the resume point and the one correction that arrived after the clink
> was written.

## Where the two ladders stand

| Ladder | Reads | Script |
|---|---|---|
| Syntactic (*reach*) | **178 / 254** rungs certified, 35 expect_validate mismatches, 254/254 CRuby agreement | `scripts/run_ratchet.sh` |
| Semantic (*justification*) | **47 / 83** `Judge` rules discharged | `scripts/run_denote.sh`, or `lake exe semladder` |

`checkrungs` reads 177/177 hand derivations + 145/145 negative controls. Both
ladder scripts exit nonzero while anything remains; that is the convention, not
a failure.

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
