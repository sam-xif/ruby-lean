# Metatheory

`books/Books/Metatheory/` holds theorems whose subject is the model itself: the
machine, `stepFn`, the heap and the builtins, with no type checker involved.
Some are results in their own right. Most are the lemma library that the
[type-soundness](type-soundness.md) proof is built on.

```sh
make metatheory    # build it, audit the axioms, run the heap probes
```

## Results

| Theorem | File | Statement |
|---|---|---|
| `Step.sound`, `Step.complete`, `Step.adequacy`, `Step.deterministic` | `Machine/Step.lean`, `Machine/Adequacy.lean` | An inductive relation `Step m m'` defines one transition of the control core of the language. It agrees with the executable `stepFn` in both directions, and the next state is unique |
| `invariant_sound` | `Reachability/TypeSafety.lean` | Type safety by reachability. If a predicate on machines holds initially, is preserved by every step, and excludes the states about to get type-stuck, then no run of the program ends type-stuck |
| `sorbet_invariant_sound` | `Reachability/SorbetSafety.lean` | The same, narrowed to the failures Sorbet's runtime would blame on the program |
| `done_inv` | `Machine/NotDone.lean` | A run finishes at exactly one place in the interpreter, so a finished run can be inverted |
| `ancestors_congr_grow` | `Heap/AncestorsGrow.lean` | Method lookup's walk up the ancestor chain gives the same answer after the heap allocates |
| `t5_loop_type_safe` | `Examples/T5Loop.lean` | A worked instance of `invariant_sound`: a loop that dispatches a user-defined method runs type-safe forever, proved without running it |

A machine is *type-stuck* when it has raised `NoMethodError`, `ArgumentError` or
`TypeError`, or a subclass of one, and nothing rescued it.

### The relation and the function

`stepFn` is a function, which is what makes the model executable and testable.
`Step` is an inductive relation, which is the usual way to present an
operational semantics and the more convenient thing to do induction on.
`Step.adequacy` says they are the same on the fragment the relation covers:

```lean
theorem Step.adequacy {m m' : Machine} (hf : InFrag m) :
    Step m m' ↔ stepFn m = .next m'
```

The relation covers the control core: literals, variables and assignment,
sequencing, `if`, `while`, `break`, `next` and `redo`. Theorems that need method
dispatch, classes or blocks are stated over `stepFn` directly, as
`invariant_sound` is, so they cover the whole model.

### Type safety without a type system

`invariant_sound` is the standard progress-and-preservation argument with the
type system removed. Any predicate that is an invariant of the step function and
excludes the bad states is enough:

```lean
theorem invariant_sound {program : Expr} (I : Machine → Prop)
    (init : I (Machine.init program))
    (cons : ∀ m m', I m → SmallStep m m' → I m')
    (safe : ∀ m, I m → ¬ aboutToTypeStick m) :
    ∀ r, ReachableResult (Machine.init program) r → ¬ typeStuck r
```

The type-soundness proof is an instance of this shape, with the invariant being
"the machine agrees with the checker's typing context".

## Layout

| Directory | Contents |
|---|---|
| `Machine/` | The step relation and its agreement with `stepFn`; every interpreter helper either advances the machine or reports why not |
| `Reachability/` | The bad-state predicate, `invariant_sound`, its Sorbet variant, and a certificate that decides the safety of one concrete run by executing it |
| `Heap/` | Which reads of the heap are unchanged by which writes: method tables under `def`, lookups and ancestor walks under allocation, class names. `HeapCert.lean` has the executable forms of the heap facts the proofs assume |
| `Builtins/` | The builtins do what their declared signatures say; when a builtin can be dispatched directly; reductions for the String pattern functions |
| `Framing/` | Appending a continuation frame below a running computation does not change what it does. One file per part of the interpreter, ending in `RootFrameStep` for a whole step |
| `Typing/` | Typing invariants of the machine that the soundness proof imports. `Lang/` defines a declaration table and a declarative judgment over the model's syntax; `Infer/` and `Judge/` prove what creating a fresh class or module does to the heap |
| `Examples/` | Concrete programs proved safe |
| `Controls/` | Counterexamples to earlier, false versions of lemmas in `Heap/` and `Framing/`, kept so the corrected hypotheses stay justified |

Declarations in this book are in the namespace `RubyCore.Proof`.

## The heap probes

Some lemmas assume a fact about the heap that the core library boots: for
example, that no two class objects share a name. Those facts are decided by
running them on the real booted heap. `make metatheory` runs the probes in
`books/scripts/probes/` and fails if one stops holding, so a change to the
prelude that would falsify an assumption is caught there and not by a proof
breaking somewhere far away.
