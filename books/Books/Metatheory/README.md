# `Books/Metatheory/` — facts about the model

Theorems whose subject is the model itself (`RubyCore`: the machine, `stepFn`,
the heap, the builtins), with no type checker in sight. Declarations here are in
the namespace `RubyCore.Proof`.

This book has two audiences. Some of it is a result in its own right. Most of it
is the lemma library that [`../TypeSoundness/`](../TypeSoundness/README.md) is
built on, and is here rather than there because none of it mentions the checker.

```bash
lake build Metatheory           # from books/
./scripts/check-proofs.sh       # the same, plus the axiom audit and the heap measurements
```

## The results

| Theorem | File | Statement |
|---|---|---|
| `Step.sound`, `Step.complete`, `Step.deterministic`, `Step.adequacy` | [`Machine/Step.lean`](Machine/Step.lean), [`Machine/Adequacy.lean`](Machine/Adequacy.lean) | The relation `Step` is the definition of the semantics and `stepFn` is its executable witness. The two agree in both directions, and the result is unique |
| `invariant_sound` | [`Reachability/TypeSafety.lean`](Reachability/TypeSafety.lean) | Type safety by reachability. If a predicate on machines holds initially, is preserved by a step, and excludes the type-stuck states, then no run of the program is ever type-stuck. No type system is involved |
| `sorbet_invariant_sound` | [`Reachability/SorbetSafety.lean`](Reachability/SorbetSafety.lean) | The same statement narrowed to failures Sorbet's runtime would blame on the program |
| `done_inv` | [`Machine/NotDone.lean`](Machine/NotDone.lean) | A run finishes at exactly one place in the interpreter, so a finished run can be inverted |
| `ancestors_congr_grow` | [`Heap/AncestorsGrow.lean`](Heap/AncestorsGrow.lean) | Method lookup's ancestor walk gives the same answer after the heap allocates |
| `t5_loop_type_safe` | [`Examples/T5Loop.lean`](Examples/T5Loop.lean) | A worked instance of `invariant_sound`: a method-dispatch loop runs type-safe from the booted heap |

"Type-stuck" means the machine has raised `NoMethodError`, `ArgumentError` or
`TypeError` (or a subclass) and nothing rescued it. It is defined in
`Reachability/TypeSafety.lean`.

## Layout

| Directory | Contents |
|---|---|
| `Machine/` | The step relation and its agreement with `stepFn` (`Step`, `Adequacy`); every interpreter helper either advances the machine or reports why not (`NotDone*`) |
| `Reachability/` | The bad-state predicate, `invariant_sound`, its Sorbet variant, and `RunCert`, which decides safety of one concrete run by executing it |
| `Heap/` | What reads of the heap are unchanged by which writes: method tables under `def`, lookups and ancestor walks under allocation, class names |
| `Builtins/` | The model's builtins do what their declared signatures say (`BuiltinConformance`); when a builtin can be dispatched directly; reductions for the String pattern functions |
| `Framing/` | Appending a continuation frame below a running computation does not change what it does. One file per part of the interpreter (`RootFrameSend`, `RootFrameEval`, …), ending in `RootFrameStep` for a whole step. `KontFrame` keeps the older names |
| `Typing/Infer/` | Machine-typing invariants stated over the model's own type inference function: declaration tables (`Decls`), frames and environments (`Locals`), continuations (`Konts`), monotonicity (`Mono`) |
| `Typing/Judge/` | The same invariants restated over a declarative judgment, and the two large composites the soundness proof uses: what creating a fresh class (`FreshClass`) or module (`FreshModule`) does to the heap |
| `Examples/` | Concrete programs proved safe: `T5*`, `DispatchLoop`, `QLearningTypeSafe`, `SorbetConcrete`, `Demo` |
| `Controls/` | Counterexamples to earlier, false versions of lemmas in `Heap/` and `Framing/`, kept so the corrected hypotheses stay justified |

`Typing/` is what survives of two earlier type-checking designs for the model.
Their checkers were deleted. These lemmas were kept because the current
soundness proof uses them, which is also why the names inside (`infer`, `Judge`,
`DeclsOk`) refer to things that no longer have a checker attached.

## What depends on what

`../TypeSoundness/` imports `Framing/`, `Heap/`, `Builtins/`, `Typing/` and
`Machine/NotDone`. It does not import `Reachability/SorbetSafety`,
`Machine/Adequacy`, `Examples/` or `Controls/`; nothing downstream depends on
those and they are claims about the semantics only.

## The measurements

Some lemmas here assume a fact about the heap the prelude boots (for instance,
that no two class objects share a name). Those facts are decided by running a
probe on the real booted heap, not proved. `scripts/check-proofs.sh` runs the
probes in `scripts/probes/` and fails if one of them stops holding, so a change
to the prelude that would falsify an assumption is caught there.

## File map

For readers of the notes, which use the old paths under `ruby-lean/RubyCore/Proof/`.

| Before | Now |
|---|---|
| `Step`, `Adequacy`, `NotDone`, `NotDoneAttr`, `NotDoneBase` | `Machine/` |
| `TypeSafety`, `SorbetSafety`, `RunCert` | `Reachability/` |
| `HeapReads`, `HeapFacts`, `HeapGrow`, `NameGrowth`, `AncestorsGrow`, `AncestorBounds` | `Heap/` |
| `ClsCongr` | `Heap/ClassCongr` |
| `BuiltinConformance`, `DirectBuiltin`, `StringFacts` | `Builtins/` |
| `RootFrame*`, `KontFrame`, `FrameAttr` | `Framing/` |
| `Static/*` | `Typing/Infer/*` (`ClsValues` is now `ClassValues`) |
| `Judgment/*` | `Typing/Judge/*` (`ClsFresh`, `ModFresh`, `ClsInv` are now `FreshClass`, `FreshModule`, `ClassInvariant`) |
| `T5`, `T5Concrete`, `T5Loop`, `Demo`, `DispatchLoop`, `QLearningTypeSafe`, `SorbetConcrete` | `Examples/` |
| `DriftControls`, `StatementObstruction` | `Controls/` |
