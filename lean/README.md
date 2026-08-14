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
| `prelude/prelude.rb` | the **prelude**: the part of the core library modeled *in Ruby* (Enumerable, Comparable, `Range#each`, Hash's Enumerable overrides, `BasicObject#!=`, …). Authored here; read the rules at the top of the file before editing (L62/L63) |
| `RubyCore/Prelude.lean` | **generated** by `scripts/gen_prelude.rb` from `prelude/prelude.rb`: the desugared prelude as export JSON, decoded by the ordinary `Decode.program` |
| `RubyCore/PreludeBoot.lean` | the two-phase boot: run the prelude from H₀ (`preludeMode`), then the program under test on the resulting heap (`Machine.initOn`) |
| `RubyCore/Interp.lean` | `stepFn` (one transition; helpers deliberately non-mutual) + `run fuel` (`outOfFuel` ≠ `stuck` from day one) |
| `RubyCore/Obs.lean` | observation = (stdout, result inspect, exception (class, msg)) |
| `Main.lean` | the SUT executable: RubyCore-JSON on stdin → Observation-JSON on stdout; **exit 3 = Unsupported** (reason on stderr), exit 1 = model bug |
| `RubyCore/Proof/` | **metatheory** (off the default build target — build it with `lake build Metatheory`, or `scripts/check-proofs.sh` to also re-verify `#print axioms`; it had silently stopped compiling for 24 commits without either, L119): `Step.lean` (inductive control-core `Step` + `Step.sound`/`Step.deterministic`), `Adequacy.lean` (`Step.heap_monotone`, `Step.complete`, `Step.adequacy`), `TypeSafety.lean` (`invariant_sound` type-safety-by-reachability + Direction-A certificate), `Demo.lean` (worked reductions + type-safety demos). See §Metatheory. |
| `RubyCore/Search/` | **witness finders** for type errors (off the default build target, dev-only `plausible` dep): `Random.lean` — Phase-1 random property-based search that *finds* counterexamples refuting `typeSafe?`, each certified via `Proof.runTypeStuck_unsafe`. See §Finding type errors. |
| `ConcolicMain.lean` | the **`rubycore-concolic` exe** (off the default target): runs the real `stepFn` and emits the branch decisions taken + the authoritative outcome (incl. `typestuck`), so the concolic engine in `../concolic/` uses the semantics as its executor rather than a duplicate. Needs no `stepFn` instrumentation — branch decisions are observable at the configuration level. |

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

## Fragment (verified 2026-08-03 by probing the built binary)

Tier-0 baseline: **940/1304 bootstraptest agree, 0 disagree.**

**Modeled.** Literals, locals/ivars/gvars/**cvars**, sends, `if`/`while`/`dowhile`/
`for` (+`break`/`next`/`redo`), `def`/call with **all param kinds** (required,
optional, `*rest`, keyword, `**kwrest`, `&blk`, destructuring), `begin`/`rescue`/
`else`/`ensure`/`retry`, `return`, `case`/`when`, constant paths, `undef`/`alias`,
`defined?`, arrays/hashes/strings as mutable heap payloads, `raise`, `$!`
save/restore.

- **L1 (blocks/procs/lambdas):** literal blocks + `yield`, `block_given?`, `&blk`
  capture params, block-pass `&e`/`&:sym`, `proc`/`lambda`/`->`/`Proc.new`,
  `Proc#call`, and non-local control (`next`/`break`/`return`) with proc-vs-lambda
  semantics and shared-scope locals (`impl-notes L16`).
- **L2 (object model):** `class`/`module` bodies, `Class#new`/`initialize`,
  cref-scoped constants, `method_missing`, `super`/`zsuper` (**all param shapes**),
  singleton methods + eigenclasses, `include`/**`prepend`** mixins, `attr_*`,
  **`Kernel`/`Numeric` in the real ancestor chain** so `ancestors` is byte-exact
  (`L17`–`L19`, `L65`, `L70`).
- **The prelude — core library written in RubyCore** (`prelude/prelude.rb`,
  `L62`/`L63`): `Enumerable` (~36 methods: `select`/`reject`/`find`/`all?`/`any?`/
  `none?`/`count`/`sum`/`map`/`flat_map`/`each_with_index`/`each_with_object`/
  `group_by`/`partition`/`tally`/`take`/`drop`/`*_while`/`each_slice`/`each_cons`/
  `min`/`max`/`min_by`/`max_by`/`sort`/`sort_by`/`inject`/…), `Comparable`,
  **`Range#each`** (so Range is a full collection), Hash's Enumerable overrides
  (which return Hashes and yield `(k, v)`), `Integer#upto`/`downto`/`step`,
  `Object#===`/`tap`, `Proc#===`, and `BasicObject#!=` (which *must* dispatch `==`).
- **Reflective metaprogramming** (`L64`/`L65`): `define_method`/
  `define_singleton_method` (bodies that close over the defining scope),
  `class_eval`/`module_eval`/`instance_eval`/`instance_exec` (block forms),
  `alias_method`, `singleton_class`, `instance_variable_get`/`_set`/`_defined?`,
  `instance_variables`, `const_get`/`const_set`/`const_defined?`,
  `remove_method`/`undef_method`, `Class.new`/`Module.new` (incl. the block form)
  with anonymous-class naming on constant assignment.
- **Visibility** (`L71`): `private`/`protected`/`public` (bare mode + name forms),
  `module_function`, `private_class_method`, enforced at dispatch against the call
  site (`self.m` may call private, `x.m` may not, `send` bypasses,
  `public_send` does not); `respond_to?`/`method_defined?`/`defined?` honour it.
- **Non-local control** (`L69`): `catch`/`throw` (+ `UncaughtThrowError` raised at
  the throw site), `redo` in a block, `break`/`next` through a class body.
- **Payload-core subclassing** (`L70`): `class MyString < String` (and Array/Hash/
  Exception) allocate and initialize properly, including `super` in `initialize`
  and `raise C` running a user `initialize`.
- **Call-site keyword arguments** — every form; **reflection predicates**
  `is_a?`/`kind_of?`/`instance_of?`/`respond_to?` (load-bearing for the checker:
  executing the real predicate prunes impossible branches).
- **Numerics/misc:** `Float#to_s`/`#inspect` shortest round-trip (`L45`), seeded
  MT19937 `Random` (`L46`), `Math` + `Range` (`L48`), `Array#[]`/`String#[]` slice
  forms (`L68`), `dup`/`clone` (copying ivars, `L66`), `String#+@`/`-@` (`L72`).

**Gated (`Unsupported`, exit 3).** Ranked by the tier-0 gate histogram (2026-08-03,
356 gates) — re-measure with `difftest run --tier 0 --sut lean` then read
`cases.jsonl`; do not trust this list to stay current:

| Count | Gate |
|---|---|
| 38 + 10 | string `eval` / `instance_eval`/`class_eval` of a string (permanently out of scope) |
| 25 / 18 | `Rational` / `Complex` (the numeric tower) |
| 22 | `Integer#times` without a block (an `Enumerator`) |
| 20 | `Regexp` |
| 16 | `Struct` |
| 14 | dynamic (non-symbol) keyword key (decode-side) |
| 9 / 8 / 5 | `TracePoint` / `File` / `RubyVM` (out of scope by design) |
| 7 | optional/keyword/destructuring **block** params |
| 6 | toplevel `return` (desugar-side) |
| 5 | `Object#binding`, `Object#object_id` |

Also gated: `Enumerator` in every form (a blockless Enumerable call), `Method`/
`UnboundMethod` objects (`Object#method`), `private_constant`, `prepend` with a
`prepended` hook, `Proc`/`Range`/`Random` subclass allocation, class variables in a
singleton-class scope, and anything CRuby defines that the model doesn't (via
`CRubyNames`).

**The next lever is `Struct`, and it is blocked on repr, not on metaprogramming.**
`Class.new` + `define_method` + `attr_accessor` are all in place, so `Struct` could
be written in the prelude — but a struct's `inspect` is `#<struct S a=1>` and its
`==` compares fields, and a prelude definition of either flips `reprPure` (`L7`)
globally, making every `puts` in every program gate. The principled fix is to make
`p`/`puts`/interpolation **dispatch** `to_s`/`inspect` instead of relying on pure
repr (i.e. move them into the prelude too, with a printing primitive underneath),
which also retires the `reprPure` flag. That is the recommended next structural
step; `Rational`/`Complex` (43 cases) are blocked on exactly the same thing.

Two fidelity policies worth knowing (both are what keeps the corpus at
0-disagree rather than quietly wrong):

1. **Lookup misses are split three ways** — exists-in-CRuby-but-unmodeled →
   `Unsupported`; genuinely absent → real `NoMethodError` (byte-exact
   message); bare zero-arg implicit send → `Unsupported` (RubyCore conflates
   vcall/fcall, whose error classes differ).
2. **`reprPure`** — a user `def` of `to_s`/`inspect`/`==`/`eql?`/`message`/`to_str`
   flips a flag; builtins that internally rely on *pure* default repr
   (`puts`, `p`, interpolation's `String()`, `Array#inspect`, …) then answer
   `Unsupported` for plain objects rather than printing the wrong thing. (It is a
   *global* flag, which is why the prelude may not define any of those names — and
   why `Struct`/`Rational` wait on dispatching repr, see §Fragment.)
3. **A prelude method suppresses the shadow gate for its own name** (`L62`) — it
   *is* the model of that CRuby builtin, so `Array#select` resolving to the
   prelude's `Enumerable#select` is intended, not a mis-dispatch. The fidelity
   obligation moves into `prelude/prelude.rb`, where difftest checks it. A *user*
   method shadowed by a real builtin still gates.
4. **Blockless builtins defer to the prelude when given a block** (`L63`):
   `[3,1,2].sort { … }` would silently ignore the block, so such calls route to a
   prelude definition of the same name, or gate.

## Regenerating the generated files

`RubyCore/CRubyNames.lean` (oracle name tables) and `RubyCore/Prelude.lean` (the
desugared prelude) are both **generated and committed**. Regenerate the prelude
after every edit to `prelude/prelude.rb`:

```sh
"$(brew --prefix ruby)/bin/ruby" scripts/gen_prelude.rb > RubyCore/Prelude.lean
lake build
```

`scripts/cmp.sh 'p [1,2].select { |x| x > 1 }'` is the dev loop: it runs a snippet
through both CRuby and the model and reports AGREE / DIFF / GATE.

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
lake build RubyCore.Search.Random     # Phase 1: random search, prints verdicts
lake build rubycore-concolic          # Phase 2: the concolic executor + branch tracer
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
