# `Books/Metatheory/` — facts about the model

Theorems whose subject is the model itself (`RubyCore`: the machine, `stepFn`,
the heap, the builtins), with no type checker involved. Declarations here are in
the namespace `RubyCore.Proof`.

Some of this book is a result in its own right. Most of it is the lemma library
that [`../TypeSoundness/`](../TypeSoundness/README.md) is built on, and it is
here because none of it mentions the checker.

```sh
make metatheory                       # from the repository root
cd books && lake build Metatheory     # the build alone
```

`make metatheory` also audits the axioms of the theorems below and runs the heap
probes.

## The results

| Theorem | File | Statement |
|---|---|---|
| `Step.sound`, `Step.complete`, `Step.deterministic`, `Step.adequacy` | [`Machine/Step.lean`](Machine/Step.lean), [`Machine/Adequacy.lean`](Machine/Adequacy.lean) | An inductive relation `Step` defines one transition of the control core of the language. It agrees with the executable `stepFn` in both directions, and the next state is unique |
| `invariant_sound` | [`Reachability/TypeSafety.lean`](Reachability/TypeSafety.lean) | Type safety by reachability. If a predicate on machines holds initially, is preserved by a step, and excludes the states about to get type-stuck, then no run of the program ends type-stuck. No type system is involved |
| `sorbet_invariant_sound` | [`Reachability/SorbetSafety.lean`](Reachability/SorbetSafety.lean) | The same statement narrowed to failures Sorbet's runtime would blame on the program |
| `done_inv` | [`Machine/NotDone.lean`](Machine/NotDone.lean) | A run finishes at exactly one place in the interpreter, so a finished run can be inverted |
| `ancestors_congr_grow` | [`Heap/AncestorsGrow.lean`](Heap/AncestorsGrow.lean) | Method lookup's ancestor walk gives the same answer after the heap allocates |
| `t5_loop_type_safe` | [`Examples/T5Loop.lean`](Examples/T5Loop.lean) | A worked instance of `invariant_sound`: a loop that dispatches a user-defined method runs type-safe forever, proved without running it |

A machine is *type-stuck* when it has raised `NoMethodError`, `ArgumentError` or
`TypeError` (or a subclass) and nothing rescued it. The definition is in
`Reachability/TypeSafety.lean`.

## Layout

| Directory | Contents |
|---|---|
| `Machine/` | The step relation and its agreement with `stepFn`; every interpreter helper either advances the machine or reports why not |
| `Reachability/` | The bad-state predicate, `invariant_sound`, its Sorbet variant, and `RunCert`, which decides the safety of one concrete run by executing it |
| `Heap/` | Which reads of the heap are unchanged by which writes: method tables under `def`, lookups and ancestor walks under allocation, class names. `HeapCert.lean` has executable forms of the heap facts the proofs assume |
| `Builtins/` | The builtins do what their declared signatures say; when a builtin can be dispatched directly; reductions for the String pattern functions |
| `Framing/` | Appending a continuation frame below a running computation does not change what it does. One file per part of the interpreter, ending in `RootFrameStep` for a whole step |
| `Typing/Lang/` | Definitions: a declaration table, an inference function and a declarative typing judgment over the model's own syntax |
| `Typing/Infer/`, `Typing/Judge/` | Typing invariants of the machine stated over those definitions, and the two composites the soundness proof uses: what creating a fresh class (`FreshClass`) or module (`FreshModule`) does to the heap |
| `Examples/` | Concrete programs proved safe |
| `Probes/` | Programs that decide facts about the booted heap; see below |
| `Controls/` | Counterexamples to earlier, false versions of lemmas in `Heap/` and `Framing/`, kept so the corrected hypotheses stay justified |

## What depends on what

`../TypeSoundness/` imports `Framing/`, `Heap/`, `Builtins/`, `Typing/` and
`Machine/NotDone`. It does not import `Reachability/SorbetSafety`,
`Machine/Adequacy`, `Examples/` or `Controls/`; those are claims about the
semantics only.

## The heap probes

Some lemmas assume a fact about the heap the prelude boots, for instance that
no two class objects share a name. Those facts are decided by running them on
the real booted heap. `scripts/check-metatheory.sh` runs the probes in
[`Probes/`](Probes/) and fails if one stops holding, so a change to the prelude
that would falsify an assumption is caught there.
