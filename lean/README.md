# RubyCore in Lean 4 — the executable model

The mechanization begun from [`../docs/semantics/lean-model-sketch.md`](../docs/semantics/lean-model-sketch.md):
a small-step machine over RubyCore with a fuel interpreter, packaged as a
difftest **SUT** from day one. The inductive `Step` relation (the definition
of record, PROJECT_PLAN §7) is not yet authored — `stepFn` comes first so the
model meets the differential engine immediately; `Step` will be written
against it and the adequacy theorems proved after.

## Layout

| File | Contents |
|------|----------|
| `RubyCore/Syntax.lean` | `Expr` (mirrors the harness S-expr heads 1:1) + JSON decoder for the versioned export (`lib/export.rb`) |
| `RubyCore/Heap.lean` | `Value`, `Object`, `Heap`, bootstrap heap **H₀** (metaclass knot as initial data), pure `classOf`/`ancestors`/`lookup`/const ops (artifacts 01–02) |
| `RubyCore/Repr.lean` | Ruby-faithful default `inspect`/`to_s`, pure `==`/`eql?` — the byte-exact strings the observation compares |
| `RubyCore/CRubyNames.lean` | **generated from the oracle**: per-class method-name sets + toplevel constants, so dispatch can detect "an unmodeled CRuby builtin would shadow this" and gate instead of mis-dispatching |
| `RubyCore/Machine.lean` | `Machine` config: control state, kont stack, frame **store** + id stack (sketch §1.2), stdout accumulator, `$!` |
| `RubyCore/Builtins.lean` | the axiomatized builtin methods, keyed `"Owner#name"`, registered in H₀'s method tables so shadowing is uniform |
| `RubyCore/Interp.lean` | `stepFn` (one transition; helpers deliberately non-mutual) + `run fuel` (`outOfFuel` ≠ `stuck` from day one) |
| `RubyCore/Obs.lean` | observation = (stdout, result inspect, exception (class, msg)) |
| `Main.lean` | the SUT executable: RubyCore-JSON on stdin → Observation-JSON on stdout; **exit 3 = Unsupported** (reason on stderr), exit 1 = model bug |
| `RubyCore/Proof/` | **metatheory** (off the default build target): `Step.lean` (inductive control-core `Step` + `Step.sound`/`Step.deterministic`), `Adequacy.lean` (`Step.heap_monotone`, `Step.complete`, `Step.adequacy`), `TypeSafety.lean` (`invariant_sound` type-safety-by-reachability + Direction-A certificate), `Demo.lean` (worked reductions + type-safety demos). See §Metatheory. |
| `RubyCore/Search/` | **witness finders** for type errors (off the default build target, dev-only `plausible` dep): `Random.lean` — Phase-1 random property-based search that *finds* counterexamples refuting `typeSafe?`, each certified via `Proof.runTypeStuck_unsafe`. See §Finding type errors. |

## Build & run

```sh
cd ruby/lean && lake build          # toolchain pinned in lean-toolchain (4.31.0)
echo 'puts 1 + 2' | "$(brew --prefix ruby)/bin/ruby" ../harness/desugar-dt/bin/export-json \
  | ./.lake/build/bin/rubycore
```

Through the difftest engine (`--sut lean` composes both fragment gates —
desugar's and the model's):

```sh
cd ../difftest
uv run python -m difftest run --tier 0 --sut lean       # bootstraptest corpus
uv run python -m difftest run --tier 1 -n 300 --sut lean --seed 1
```

## Fragment (L0, growing)

Modeled: literals, locals/ivars/gvars, sends, `if`/`while` (+`break`/`next`),
`def`/call with required params, `begin`/`rescue`/`else`/`ensure`/`retry`,
`return`, arrays/hashes/strings as mutable heap payloads, `raise`, `$!`
save/restore semantics, and the builtin slices listed in `Boot.builtinMethods`.
**L1 (blocks/procs/lambdas):** literal blocks + `yield`, `block_given?`,
`&blk` capture params, block-pass `&e`/`&:sym`, `proc`/`lambda`/`->`/`Proc.new`,
`Proc#call`, and the non-local control (`next`/`break`/`return`) with
proc-vs-lambda semantics and shared-scope locals (`impl-notes L16`).

Gated (`Unsupported`, exit 3): iterating builtins that yield (`Array#each`/
`map`, `Integer#times`, `Hash.new{}`), mixins (`include`/`prepend`), class
macros (`attr_reader`/`define_method`); **L2 object model done** — `class`/`module`
bodies, `Class#new`/`initialize`, `method_missing`, `super`/`zsuper`, singleton
methods + eigenclasses (`impl-notes L17`–`L19`), splat/kwargs, class variables, `Float` **formatting** (Ruby needs
shortest-roundtrip; float arithmetic works), `Integer#hash` (seeded),
vcall-vs-fcall `NameError` ambiguity, and anything CRuby defines that the
model doesn't (via `CRubyNames`).

Two fidelity policies worth knowing (both are what keeps the corpus at
0-disagree rather than quietly wrong):

1. **Lookup misses are split three ways** — exists-in-CRuby-but-unmodeled →
   `Unsupported`; genuinely absent → real `NoMethodError` (byte-exact
   message); bare zero-arg implicit send → `Unsupported` (RubyCore conflates
   vcall/fcall, whose error classes differ).
2. **`reprPure`** — a user `def` of `to_s`/`inspect`/`==`/`eql?`/`message`/`to_str`
   flips a flag; builtins that internally rely on *pure* default repr
   (`puts`, `p`, interpolation's `String()`, `Array#inspect`, …) then answer
   `Unsupported` for plain objects rather than printing the wrong thing.

## Regenerating `CRubyNames.lean`

```sh
"$(brew --prefix ruby)/bin/ruby" scripts/gen_cruby_names.rb > RubyCore/CRubyNames.lean
```

Rerun against the pinned oracle when the CRuby version bumps. It folds
modules the L0 ancestor chain omits (Kernel→Object, Comparable/Numeric→
numerics/strings, Enumerable→Array/Hash).

## Metatheory

The sketch and PROJECT_PLAN §7 name the **inductive `Step` relation** the
definition of record, with `stepFn` its executable witness. `RubyCore/Proof/`
realizes that programme in two layers (both off the default build target,
axiom-clean; see `implementation-notes.md` L13–L15, L51):

1. **The inductive control-core `Step`** (`Step.lean`/`Adequacy.lean`) — an
   effect-light fragment (literals, local/ivar/global var + assign, `seq`, `if`,
   `while`, `dowhile`, `break`/`next`/`redo`) with soundness, completeness,
   adequacy, determinism, and a heap-monotonicity preservation invariant. The
   idiomatic relational view; bridged to the full relation by
   `Step.subset_smallStep`.
2. **Type safety as reachability** (`TypeSafety.lean`) — the `invariant_sound`
   progress/preservation metatheorem of `type-safety-by-reachability.md` §4,
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

## Finding type errors (Direction A — witness search)

The metatheory above *proves* safety; this is the complementary direction —
**finding counterexamples** that refute it. `RubyCore/Search/` hosts the
witness finders (off the default build target; `plausible` is a dev-only
dependency the lib root and exe never import — `implementation-notes.md` L58).

```sh
lake build RubyCore.Search.Random     # runs the searches, prints verdicts
```

**Phase 1 — random (property-based) search** (`Random.lean`). Generates inputs,
runs the semantics, and reports any input whose run ends in an uncaught
type-family exception. Verified working:

| Program | Result |
|---|---|
| `nilDispatch` (`def f(x); x<5 ? 1 : nil; end; f(N).succ`) | `failed [n := 7]` — **witness found**, refutes `typeSafe?` |
| `alwaysSafe` (`N.succ`) | `success` — no false positive |
| `narrowNeedle` (stuck only at `N = 123456789`) | `success` — **missed**, even at 20× budget |

The search is **untrusted**: a reported witness is replayed through the trusted
`run`/`stepFn` and fed to the axiom-clean bridge `Proof.runTypeStuck_unsafe`,
producing a real theorem (`nilDispatch_unsafe`). A bogus witness dies at replay,
so the search needs no soundness argument — *the certificate is the trace*.

Two honest caveats, both first-class in the design:

- A `success` verdict is **not** a safety proof — it means "no witness within
  these bounds" (the `VERIFIED(k)`/UNKNOWN split of
  `../../bounded-effect-checking.md` §3). Proving safety is Direction B.
- Random search is **undirected**: `narrowNeedle` shows it cannot find a needle
  behind a narrow guard. That is exactly the gap **Phase 2** (concolic execution:
  concrete run + path condition + solver-flip) closes.
