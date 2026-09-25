# Metatheory

Paths are relative to `ruby-lean/`.

`ruby-lean/RubyCore/README.md` §Mechanization names the **inductive `Step` relation** the
definition of record, with `stepFn` its executable witness. `RubyCore/Proof/`
realizes that programme in two layers (axiom-clean; see
`notes/model/implementation-notes.md` L13–L15, L51):

1. **The inductive control-core `Step`** (`Step.lean`/`Adequacy.lean`) — an
   effect-light fragment (literals, local/ivar/global var + assign, `seq`, `if`,
   `while`, `dowhile`, `break`/`next`/`redo`) with soundness, completeness,
   adequacy, determinism, and a heap-monotonicity preservation invariant. The
   idiomatic relational view; bridged to the full relation by
   `Step.subset_smallStep`.
2. **Type safety as reachability** (`TypeSafety.lean`) — the `invariant_sound`
   progress/preservation metatheorem of `ruby-lean/AGENTS.md`
   §Type safety as reachability §4,
   proved over the *full* transition relation `SmallStep m m' := stepFn m =
   .next m'` (so it covers dispatch/classes/blocks — real programs, not just the
   control core), plus the Direction-A execution certificate
   (`run_value_type_safe`) and a worked Direction-B invariant demo in
   `Demo.lean`.

Build and check:

```sh
lake build RubyCore.Proof.TypeSafety RubyCore.Proof.Demo
```

Theorems (all resting only on `propext`/`Classical.choice`/`Quot.sound` — no
`sorry`, no `native_decide`; audited with `#print axioms`):

| Theorem | Statement |
|---------|-----------|
| `Step.sound` | `Step m m' → stepFn m = .next m'` — every relation step is one executable step |
| `Step.complete` | `InFrag m → stepFn m = .next m' → Step m m'` — every in-fragment executable step is a relation step |
| `Step.adequacy` | `InFrag m → (Step m m' ↔ stepFn m = .next m')` — function–relation adequacy on the fragment |
| `Step.deterministic` | `Step m a → Step m b → a = b` |
| `Step.heap_monotone` | `Step m m' → m.heap.objs.size ≤ m'.heap.objs.size` — a preservation invariant proved by induction on the step relation (ObjIds never reused; the shape the eventual machine↔SOS fresh-allocation argument needs) |
| `invariant_sound` | `I (init p) → (∀ m m', I m → SmallStep m m' → I m') → (∀ m, I m → ¬ aboutToTypeStick m) → ∀ r, ReachableResult (init p) r → ¬ typeStuck r` — any inductive invariant (init/preservation/progress) proves no reachable outcome is a type-family `uncaught`, all inputs / unbounded fuel |
| `run_value_type_safe` | a run terminating in a value reaches a non-type-stuck outcome — the Direction-A execution certificate (the `q_learning` coverage story) |
| `T5.dispatch_progress` | a resolvable-method dispatch steps to the method activation (not `NoMethodError`) — the object-model invariant clause (§4.2) over the real `invoke` |
| `DispatchLoop.loop_type_safe` | **`while true do 1.succ end` is type-safe** (unbounded fuel) by an inductive object-model invariant — the first axiom-clean Direction-B proof of a dispatching program, without running it |
| `T5Loop.t5_loop_type_safe` | **the actual T5: `while true do x.m end` (user class `A`, method `m`) is type-safe** (unbounded fuel) by an inductive object-model invariant handling frame-store growth — axiom-clean, without running it |

`Demo.lean` exhibits the relation firing, a concrete 5-step reduction of `1; 2`
to the value `2`, adequacy on a real initial config, and the type-safety
pipeline: the Direction-A certificate on `1; 2`, and `while true do nil end`
proved type-safe via a hand-supplied inductive invariant. A relational dispatch
`Step` (folding `invoke` as a trusted oracle) is the next extension, but
`invariant_sound` does not depend on it (it ranges over `stepFn`).

## What was removed, and what the checker of record is

`RubyCore/` used to carry four successive attempts at *type-checking* on top of
this model, each superseded by the next and none of them the checker of record:

| Layer | What it was |
|---|---|
| `Types/` + `Proof/Static/` | `infer`/`inferOpen`/`check` — a nominal static checker and its soundness theorem (`check_sound`), plus the assertion language |
| `Cert/` + `Proof/Cert/` | type-checking as **certificate replay** (`validate`, `validate_sound`) |
| `Judgment/` + `Proof/Judgment/` | the inductive `Judge` relation, derivations-as-data (`validateJ`) and the Rails pilot |
| `HJudge/` + `HCtx/` | the Iris-seated higher-order denotation `HTy` (the only user of the `iris-lean` dependency) |

They were removed, together with the `rubycore` flags that drove them
(`--check`, `--check-tl`, `--assn`, `--assn-program`, `--certify`, `--certify-j`,
`--census-j`), the `plausible`-dependent witness search in `Search/`, and the
concolic exe whose consumer lives in another repository. What survives of them is
listed in the `RubyCore/Proof/` row of the [layout table](fragment.md#layout): the lemmas `Denote/Sem/` actually imports.

**The checker of record is `validateD`** — `Ratchet/Check/Check.lean`, with
`validateD_safe_boot` in `Denote/Bridge.lean` as its safety theorem, run by
`lake exe ratchetd` and gated by `scripts/run_typed_ratchet.sh`. The model's own
metatheory above is a claim about the *semantics*, and nothing downstream of it
depends on the removed layers.
