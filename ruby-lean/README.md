# ruby-lean — the Lean project

One Lake package (`rubylean`), four libraries, and the layering is the point:

```
ruby-lean/
  RubyCore/     the executable model — `stepFn`, the heap, the builtins, the prelude
    Proof/      its metatheory (off the default target: `lake build Metatheory`)
                — plus the lemmas `Denote/Sem/` imports, which are on it
  Ratchet/      the certificate checker — its own copied `Expr`/`Ty`, `Deriv`, `validateD`
    Lang/       the copied language: `Expr`, `Ty` (nothing here is a judgment)
    Static/     the static vocabulary both sides are stated over — tables, `Ctx`, narrowing
    Judgment/   the syntactic judgments, and only these: `DJudge`, `InitJudge`
    Guards/     the decidable side conditions a rule's premises are written in
    Check/      the executable checker — `Deriv`, `validateD`, the caches
    Controls/   negative controls
  Semantics/    the one import bridge back to the real `stepFn` (a single file)
  Denote/       the denotation joining the two, and `validateD_safe_boot`
    Ty/         tier 1 — what a `Ty` *means*: `den`/`denB`, arrows, heap growth, joins
    Sem/        tier 2 — the `StateOk` invariant and its transport lemmas, in pockets:
                Core/ Heap/ Names/ Class/ Subclass/ Instance/
    Judgment/   tier 3 — the semantic judgment `SemSafeCtxA` and its composition contracts
    Rules/      the per-rule semantic obligations, by feature (Expr/ Method/ Class/ …)
    Clink/      the registry: a rule enters the judgment only with its proof attached
    Controls/   negative controls (`All.lean` is the list the gate builds)
    Examples/   worked derivations and the concrete corpus safety theorems
    Bridge.lean `djudge_certified` and `validateD_safe_boot` — the headline theorem
  corpus/       the annotated rungs (the ladder's source of truth)
  build/        derived from corpus/ by scripts/build_corpus.py — never edited
  prelude/      the core library modeled *in Ruby*
  scripts/      the untrusted pipeline, the gates, and probes/ (measurements)
  notes/        the working record: notes/model/ and notes/ratchet/
```

**`Ratchet/` imports nothing from `RubyCore/`.** The checker carries copied
`Expr`/`Ty` so it can be read and re-implemented without the 24k-line model in
scope; `Semantics/` is the single deliberate exception and `Denote/` is the one
library that sees both. That used to be a package boundary — the two were
separate Lake packages, `lean/` and `ratchet/` — and since the merge it is
`scripts/check-isolation.sh`, which `scripts/run_typed_ratchet.sh` runs first.

The three tiers under `Denote/` are a strict stack — `Ty/` → `Sem/` → `Judgment/`
and `Rules/` — and the delineation is the point: a file under `Sem/` says what it
means for a *machine* to conform to a `Ctx`, a file under `Rules/` says what a
*rule* owes, and neither is a syntactic judgment. Those live under `Ratchet/`,
which cannot see `Denote/` at all. See [`Ratchet/README.md`](Ratchet/README.md)
and [`Denote/README.md`](Denote/README.md).

For the checker's current state, the proof boundary, the pipeline and the gate,
read [`AGENTS.md`](AGENTS.md). The rest of this file is the **model**.

## The model

The mechanization begun from the design sketch now distilled into
[`RubyCore/README.md`](RubyCore/README.md) §Mechanization:
a small-step machine over RubyCore with a fuel interpreter, packaged as a
difftest **SUT** from day one. The inductive `Step` relation (the definition
of record, `RubyCore/README.md` §Mechanization) is not yet authored — `stepFn` comes first so the
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
| `RubyCore/Types/` | what is left of the type vocabulary the SUT still needs: `Ty.lean` (the type language), `Fragment.lean` (`--fragment`: is a program in the Sorbet fragment, with a reason per exclusion), `SigRead.lean` (`--sigs`: the signatures a program declares — stage 1 of the ratchet's pipeline), plus `Core.lean`/`Decls.lean`, the declaration table the surviving proofs are stated over. The checker built on top of these (`infer`/`inferOpen`/the certificate language) was removed — see §Metatheory. |
| `Main.lean` | the SUT executable: RubyCore-JSON on stdin → Observation-JSON on stdout; **exit 3 = Unsupported** (reason on stderr), exit 1 = model bug |
| `RubyCore/Proof/` | **metatheory** (`lake build Metatheory`, or `scripts/check-proofs.sh` to also re-verify `#print axioms`; it had silently stopped compiling for 24 commits without either, L119): `Step.lean` (inductive control-core `Step` + `Step.sound`/`Step.deterministic`), `Adequacy.lean` (`Step.heap_monotone`, `Step.complete`, `Step.adequacy`), `TypeSafety.lean` (`invariant_sound` type-safety-by-reachability), `Demo.lean` (worked reductions + type-safety demos), the `KontFrame*`/`HeapFacts` continuation- and heap-framing lemmas, and — in `Proof/Judgment/` and `Proof/Static/` — the class-freshness and declaration-table lemmas **the live checker imports** (`Denote/Sem/{ClassHeap,ClassGrowth,SubclassHeap}`), which are therefore on the default target by way of `Denote`. See §Metatheory. |


## Build & run

```sh
cd ruby-lean && lake build         # toolchain pinned in lean-toolchain
echo 'puts 1 + 2' | "$(brew --prefix ruby)/bin/ruby" ../desugar-dt/bin/export-json \
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

[`RubyCore/README.md`](RubyCore/README.md) §Mechanization names the **inductive `Step` relation** the
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
   progress/preservation metatheorem of [`AGENTS.md`](AGENTS.md)
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
listed in the `Proof/` row above: the lemmas `Denote/Sem/` actually imports.

**The checker of record is `validateD`** — `Ratchet/Check/Check.lean`, with
`validateD_safe_boot` in `Denote/Bridge.lean` as its safety theorem, run by
`lake exe ratchetd` and gated by `scripts/run_typed_ratchet.sh`. The model's own
metatheory above is a claim about the *semantics*, and nothing downstream of it
depends on the removed layers.
