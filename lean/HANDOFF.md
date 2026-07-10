# Lean model — hand-off (2026-07-10)

Fresh-context hand-off for the Lean interpreter work begun 2026-07-07 (mirrors
`../difftest/HANDOFF.md` in role). Read `README.md` first for layout/build;
`implementation-notes.md` (L1–L12) for revertable decisions; this file for
state, the coverage assessment, and what happens next.

## State

Built and green: the L0 slice of `../docs/semantics/lean-model-sketch.md` §3–4
runs as a difftest SUT (`--sut lean`). Pipeline: Ruby source → desugar
(`../harness/desugar-dt/`) → RubyCore JSON (`lib/export.rb`, versioned) →
`rubycore` binary → Observation JSON. Two fragment gates compose (desugar's
and the model's); binary exit 3 = Unsupported, exit 1 = model bug
(`MODEL-BUG:` prefix in the engine — never silently absorbed).

Corpus status at hand-off, all with **0 disagreements**:
- **tier 0 (full bootstraptest): 295/1304 agree** (544 gate at desugar, 457 at
  the model, 7 control-invalid, 1 pre-existing control-side harness error)
- tier 1 fuzzing (n=300, seed 11): 214 agree / 86 unsupported
- regression + tier-3 replay: clean

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

**By node head** — 22 of the 29 RubyCore heads evaluate:
- Handled: `int flt str sym true false nil self const casgn send if while def
  array hash splat return break next retry begin seq`, and `var`/`vasgn` for
  local/ivar/gvar.
- Gated: `block` (L1), `class module sclass defs super zsuper` (L2), `cvar`.

**Partial gates inside handled heads:** hash-splat and anonymous-splat
operands; Float *rendering* (arithmetic works — Ruby needs shortest-roundtrip
output, Lean's `Float.toString` is `%f`-style); the vcall/fcall NameError
ambiguity (RubyCore conflates them, their error classes differ); and the
builtin library surface itself — a slice of each core class.

**By throughput:** of the 760 bootstraptest cases that survive the desugar,
the model fully executes 295 (~39%). The model-side gates break down roughly:
class/module/singleton definitions ~171, unmodeled methods/constants ~166,
blocks 85, tail of specific builtins (~35: `Array#[]` slices, Float
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
   `../harness/desugar-dt/M2-params-yield-plan.md` (migrate the flat
   `[String]` param slot to structured param nodes). The Lean `parseParams`
   ("*"-prefix convention) must migrate in lockstep — the export is
   versioned (`Export::VERSION`), so bump it when the shape changes.
2. **L1: blocks + `yield` + proc/lambda jumps** — the sketch's §1.1/§1.2
   payoff (generative jump targets = frame identity; `captured` chains in the
   frame store). Machinery is already shaped for it: `Frame.captured`,
   `Frame.blk`, `brkJ`/`nxtJ` jumps, and the kont-marker unwinding all exist;
   blocks add block frames and make `frameK`-crossing jumps meaningful
   (today they gate). Essence-of-Ruby's §7 test battery becomes seeds.
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
   mechanical (soundness = one uniform `cases`+`simp`). Remaining for the full
   metatheory: extend the fragment to `send` (fold `invoke`/`Builtins.run` as a
   trusted oracle), then `return`/frames and `begin`; the PoC will likely be
   reworked when L1/L2 change the machine shape. The prior guidance still
   holds — the *complete* metatheory is best finished after L1 so the rule set
   doesn't churn mid-proof.
5. **Opportunistic, any time:** Float shortest-roundtrip formatting (contained;
   unlocks ~5 tier-0 cases and all float observations); more builtins driven
   by the `Unsupported` histogram (`Rational`/`Complex` are the top names);
   the sketch §5 export cross-check (render→parse→desugar→export ≟ export) in
   the harness test suite.

Ratchet discipline carries over from the desugar: after any change, tier-0
full + tier-1 + regression replay must stay **0 disagree**, and agreement may
only go up (baseline 295).
