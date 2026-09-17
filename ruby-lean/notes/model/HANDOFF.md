# Lean model — hand-off

> ## ⚠️ CURRENT STATE (2026-08-03) — read this block, then skip to §"Open threads"
>
> Everything dated earlier in this file (and the 2026-07-30 banner it replaces) is
> **historical**; numbers below are the measured current ones.
>
> - **`--sut lean` is GREEN. Tier-0 baseline: 940/1304 agree, 0 disagree**
>   (722 → 940 in the 2026-08-03 batch). Tier-1 fuzzing (n=400, seed 7) 371 agree /
>   0 disagree; tier-3 and regression replays clean. Concolic suite 28/28. All ten
>   `Proof/` files build, axiom-clean.
> - **What landed (see `implementation-notes.md` L62–L73):**
>   - **A prelude** — the core library written *in RubyCore* (`prelude/prelude.rb`,
>     generated into `RubyCore/Prelude.lean`, loaded by a two-phase boot). Enumerable
>     (~36 methods), Comparable, `Range#each` (Range is now a full collection), Hash's
>     Enumerable overrides, `BasicObject#!=`. **This is the mechanism to reach for
>     when a builtin is missing**: a few lines of Ruby, not a new `IterKind`.
>   - **Reflective metaprogramming** — `define_method`, the `*_eval`/`*_exec` block
>     forms, `prepend`, `alias_method`, `singleton_class`, ivar/const reflection,
>     `Class.new`.
>   - **`defined?`** (the old largest gate), **class variables**, `Array#[]`/
>     `String#[]` slices, **`catch`/`throw`**, `redo` in a block, **payload-core
>     subclassing** (`class MyString < String`), full `zsuper` param shapes,
>     **visibility** (`private`/`protected`/`public`, enforced at dispatch),
>     `Kernel`/`Numeric` in the ancestor chain (so `ancestors` is byte-exact).
> - **Top remaining tier-0 gates** (356 total): string `eval` family (48,
>   permanently out of scope), `Rational`/`Complex` (43), blockless `Integer#times`
>   i.e. `Enumerator` (22), `Regexp` (20), `Struct` (16), dynamic keyword keys (14),
>   `TracePoint`/`File`/`RubyVM` (22, out of scope). Re-measure rather than trust
>   this: `difftest run --tier 0 --sut lean`, then read `reports/<latest>/cases.jsonl`.
> - **The next structural lever is *dispatching repr*, not more builtins.**
>   `Struct` and `Rational` are both blocked on the same thing: their `inspect`/`==`
>   cannot live in the prelude because defining those names flips the global
>   `reprPure` flag (L7) and every `puts` in every program would gate. Making
>   `p`/`puts`/interpolation dispatch `to_s`/`inspect` (moving them into the prelude
>   over a printing primitive) retires that flag and unlocks ~59 cases plus every
>   user class with a custom `to_s`. See `README.md` §Fragment.
> - **Two traps to know before touching the step function** (L73): a `partial def`
>   or a `String.endsWith`/`startsWith` on the dispatch path is **not
>   kernel-reducible** and silently breaks every `Proof/` file while the difftest
>   ratchet stays green. Dispatch on literal-list membership instead, and build the
>   proofs (`lake build RubyCore.Proof.T5Loop …`) as part of a batch.

Fresh-context hand-off for the Lean interpreter work begun 2026-07-07 (mirrors
Read `README.md` first for layout/build;
`implementation-notes.md` (L1–L12) for revertable decisions; this file for
state, the coverage assessment, and what happens next.

## State

Built and green: the L0 slice of `../docs/semantics/lean-model-sketch.md` §3–4
runs as a difftest SUT (`--sut lean`). Pipeline: Ruby source → desugar
(`../desugar-dt/`) → RubyCore JSON (`lib/export.rb`, versioned) →
`rubycore` binary → Observation JSON. Two fragment gates compose (desugar's
and the model's); binary exit 3 = Unsupported, exit 1 = model bug
(`MODEL-BUG:` prefix in the engine — never silently absorbed).

Corpus status at hand-off, all with **0 disagreements**:
- **tier 0 (full bootstraptest): 372/1304 agree** (up from 295 after L1
  blocks; rest gate at desugar/model, 7 control-invalid, 1 pre-existing
  control-side harness error `test_syntax_115`)
- tier 1 fuzzing (n=300, seed 11): 214 agree / 86 unsupported
- regression + tier-3 replay: clean (incl. `blocks-jumps/000`)

**L1 (blocks/procs/lambdas) is now implemented in the executable stepper**
(export v3; `impl-notes L16`): literal blocks + `yield`, `block_given?`,
`&blk` capture, block-pass `&e`/`&:sym`, `proc`/`lambda`/`->`/`Proc.new`,
`Proc#call`, and non-local control (`next`/`break`/`return`) with the
proc-vs-lambda `return` distinction and shared-scope locals — all validated
above. The `Step` relation/proofs were **not** touched (still the L0
control-core PoC). Builtins that *yield* (`Array#each`/`map`, `times`,
`Hash.new{}`) stay `Unsupported` — a pure builtin cannot push a block frame.

Bugs already caught and fixed by the loop (each was a real semantics error):
`$!` visibility during ensure-of-unmatched-region; unmodeled `String#getbyte`
shadowing a toplevel `def getbyte`; missing rest-param binding; zero-arg
builtins silently ignoring args; coercion/comparison error messages using
class name where CRuby uses inspect for special constants — and the mirror
image on `String#<` (inspect where CRuby uses class name for non-special
operands, mix-00579). Fuzzing found the last two; minimized reproducers are
committed in `../difftest/corpus/regressions/`. The lesson generalizes: one
operand-description rule (`coerceDesc`) governs all coerced/comparison
messages — special constants by inspect, everything else by class name.

## Coverage assessment (what "L0" cashes out as)

**By node head** — most RubyCore heads evaluate:
- Handled: `int flt str sym true false nil self const casgn send if while def
  array hash splat return break next retry begin seq`, `var`/`vasgn` for
  local/ivar/gvar, and (L1) `block yield blockpass` + `&blk` capture params.
- Gated: `class module sclass defs super zsuper` (L2), `cvar`.

**Partial gates inside handled heads:** hash-splat and anonymous-splat
operands; Float *rendering* (arithmetic works — Ruby needs shortest-roundtrip
output, Lean's `Float.toString` is `%f`-style); the vcall/fcall NameError
ambiguity (RubyCore conflates them, their error classes differ); and the
builtin library surface itself — a slice of each core class.

**By throughput:** of the bootstraptest cases that survive the desugar, the
model now fully executes 372 (up from 295 after L1 blocks). The model-side
gates break down roughly: class/module/singleton definitions (L2), unmodeled
methods/constants, iterating builtins that yield, tail of specific builtins
(`Array#[]` slices, Float
formatting, `Rational`/`Complex` constructors, …).

**The load-bearing fidelity mechanism** (understand this before growing the
fragment): a partial model must know what it *doesn't* implement.
`RubyCore/CRubyNames.lean` — generated from the pinned oracle by
`scripts/gen_cruby_names.rb` — holds per-class method/singleton name sets and
toplevel constants. Dispatch uses it to (a) gate when an unmodeled CRuby
builtin would shadow a resolved method, (b) gate exists-but-unmodeled misses,
(c) raise byte-exact `NoMethodError` only on genuine total misses. The
companion `reprPure` flag gates pure-repr consumers (`puts`, `p`, `String()`,
container `inspect`) once a user `def` shadows a repr-sensitive method. These
two policies are why partial coverage yields `Unsupported` rather than silent
disagreement — preserve them as the fragment grows.

## Next steps for the semantics (in intended order)

1. **Desugar M2 (params + `yield`) — upstream, biggest lever.** 544/1304
   cases never reach Lean. Plan already written:
   the desugarer's M2 params+yield batch, since landed (migrate the flat
   `[String]` param slot to structured param nodes). The Lean `parseParams`
   ("*"-prefix convention) must migrate in lockstep — the export is
   versioned (`Export::VERSION`), so bump it when the shape changes.
2. **L1: blocks + `yield` + proc/lambda jumps — DONE** (`impl-notes L16`;
   executable stepper only, `Step` untouched). The sketch's §1.1/§1.2 payoff
   realized: generative jump targets = frame identity, `captured` chains in the
   frame store, targeted `retJ`. Remaining L1 tails (opportunistic): block
   frames for iterating *builtins* (`Array#each`/`map`, `times`) — needs a way
   for a builtin to request a block-frame push (or model them as RubyCore
   methods); `redo`; multi-arg `Symbol#to_proc` edge cases; `Proc#curry`/
   `arity`/`===` (currently gate).
3. **L2: object-model definition forms** (`class`/`module`/`sclass`/`defs`,
   `super`, eigenclasses) — ~171 gated cases. Classes as ordinary heap
   objects is already the heap's shape; these heads are "push a class-body
   frame with fresh cref/self + heap mutation". Includes migrating const
   lookup off the flat-Object namespace (artifact 03's two-phase rule).
4. **`inductive Step` + metatheory** — the definition of record
   (PROJECT_PLAN §7). Author it against `stepFn` (the helpers are
   deliberately non-mutual single transitions, so rule extraction is
   mechanical), then `step_deterministic` and `stepFn` soundness/completeness.
   **A proof-of-concept slice of this is now done** (`RubyCore/Proof/`, off the
   default target; README §Metatheory, implementation-notes L13–L15): an
   inductive `Step` over an effect-light control-core fragment with
   `Step.sound`, `Step.complete`, `Step.adequacy` (function–relation adequacy
   on the fragment), `Step.deterministic`, and a `Step.heap_monotone`
   preservation invariant — all axiom-clean (`#print axioms` shows only
   propext/Classical.choice/Quot.sound). It validates that the
   interpreter-first design admits real theorems and that rule extraction is
   mechanical (soundness = one uniform `cases`+`simp`). Refreshed against the
   current stepper (control core now covers `redo`/`dowhile`; L13).
   **Type-safety metatheory landed** (`RubyCore/Proof/TypeSafety.lean`; L51):
   the `invariant_sound` progress/preservation theorem of
   `type-safety-by-reachability.md` §4, proved over the *full* transition
   relation `SmallStep m m' := stepFn m = .next m'` (so it applies to real
   programs — dispatch/classes/blocks — not just the control core), plus the
   Direction-A execution certificate (`run_value_type_safe`, the `q_learning`
   coverage story) and a fully-discharged Direction-B invariant demo. Remaining
   for a *relational* dispatch metatheory: extend the inductive `Step` to `send`
   (fold `invoke`/`Builtins.run` as a trusted oracle), then `return`/frames and
   `begin` — but note `invariant_sound` already does NOT need this, since it is
   formulated over `stepFn` directly.
5. **Opportunistic, any time:** Float shortest-roundtrip formatting (contained;
   unlocks ~5 tier-0 cases and all float observations); more builtins driven
   by the `Unsupported` histogram (`Rational`/`Complex` are the top names);
   the sketch §5 export cross-check (render→parse→desugar→export ≟ export) in
   the harness test suite.

Ratchet discipline carries over from the desugar: after any change, tier-0
full + tier-1 + regression replay must stay **0 disagree**, and agreement may
only go up (baseline now **940**). At batch boundaries also build the `Proof/`
files and run `../concolic` (28 tests) — the ratchet does not notice a
kernel-reducibility regression (L73).

---

## C-1 — SUPERSEDED AND DELIVERED THROUGH THE JUDGMENT LAYER (2026-08-26, same day)

> The section below is kept as written for its tactical records (the four wrong
> turns are still traps). Its *task* is done, by the re-scoping
> `docs/semantics/judgment-layer.md` argued for rather than by the `chk` port it
> describes: the invariant is stated over the inductive `Judge`
> (`RubyCore/Proof/Judgment/`, J18–J27), `judge_sound_cert` is the composed
> theorem with `hctl`'s role filled by a derivation, and `egEven` — the
> `_certified` corollary below parks on C-1 — is proved **unconditionally**
> (`Proof/Judgment/Cert.lean`, and again from a data certificate in
> `Proof/Judgment/Adequacy.lean`). The `chk_table_ret` rung was abandoned
> deliberately (judgment-layer.md §5); `chk` remains the coverage tier.

## C-1 (historical) — the one open premise of `validate_sound` (2026-08-26)

`validate` no longer calls `infer`; `#check @infer` does not elaborate from
`RubyCore.Cert.Validate`. The composed certificate theorem is
`Proof/Cert/Sound.lean`'s

```lean
validate_sound_of_ctl (h : validate c p = true) (ha : ⟦c.rowAssn⟧)
  (hctl : CtlOk (c.table p) { cls := "Object" } [] [] (Machine.init p)) :
  ∀ r, ReachableResult (Machine.init p) r → ¬ typeStuck r
```

axiom-clean, no `infer` in the statement (that is what L268's `initiation_ctl`
factoring is for). **`hctl` is the only thing open.** Closing it is C-1:
restate `CtlOk`/`KontOk` over `chk` and repair `Mono`/`Locals`/`Preservation`.
`docs/semantics/certificate-language.md` §10.5–10.6 is the design account;
`ruby-lean/RubyCore/Cert/implementation-notes.md` V9–V20 is the decision record.

### Start here, and do not re-derive these

1. **`chk.induct` exists** (V19) — `chk` and its eight helpers are one `mutual`
   block with fuel decreasing on *every* call. Do not "simplify" that back into
   the callback (`Rec`) form: a recursive call passed as a higher-order argument
   makes the induction principle underivable, and all twenty of
   `Proof/Static/Mono.lean`'s laws are `induction … using infer.induct`.
2. **The motive map is in `Proof/Cert/Mono.lean`** and cannot be read off the
   file. Motives 3/5/7 (`chkSeq`/`chkElems`/`chkArgs`) have identical types, so a
   swapped assignment *type-checks* and only the IH shapes reveal it — same for
   1/10 (`chkOpt`/`chkRecv`). Measured, twice.
3. **The immediate next task**: `chk_table_ret` is one uniform tactic away from
   green. Motives 4 and 8 (`chkPairs`/`chkKwEntries`) need their three-link IH
   chain applied *explicitly*; `simp_all` diverges there (max steps → max
   recursion → `isDefEq` heartbeats, and at 40M it does not terminate in ten
   minutes). Everything else closes.
4. **Do not build a bridge back to `infer`.** One was written and deleted: it
   makes the headline theorem depend on the function the pivot exists to retire.
   Two findings from it are kept in `Cert/Frag.lean` §5 and are load-bearing —
   `defFreeF` must be a *fragment* condition (otherwise the two checkers take
   different promotion branches and **both accept**), and a literal-block send
   needs a receiver (`infer`'s `lambda` arm ignores `ctx.selfCls`).

### Four tactical facts, each of which cost a wrong turn

* `split at h`, not `cases`, on a scrutinee that is not a hypothesis.
* A generic `VarKind`/`Option` payload blocks the head match and makes `split`
  re-open all 47 arms; split those at the *pattern*. Where the enclosing pattern
  must stay a wildcard, name the computation instead (that is `chkOpt`/`chkRecv`).
* `absurd h (by simp)` is not a finisher — it elaborates and leaves its side goal
  open, so `first` treats it as a success. Twenty-six arms failed silently that
  way. Use `simp at h; done`.
* **Macro bodies are hygienic.** An `ih`/`hr` written inside a `local macro`
  refers to a fresh `ih✝`, and the failure mode is a `first` branch that never
  fires. Three wrong turns. Pass them as parameters.

### Ratchets as of this handoff

`lake build` 94 jobs green; `scripts/check-proofs.sh` **OK**; difftest tier-0
`--sut lean` 1304 ran / **992 agree** / **0 disagree** / 306 unsupported. Note
992 exceeds the 940 baseline recorded above and this initiative added no
interpreter behaviour — the baseline line is stale, but the delta was not
attributed, so it is left as written rather than silently updated.
