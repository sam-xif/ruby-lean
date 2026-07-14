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
| `RubyCore/Proof/` | **metatheory PoC** (off the default build target): `Step.lean` (inductive `Step` + `Step.sound`/`Step.deterministic`), `Adequacy.lean` (`Step.heap_monotone`, `Step.complete`, `Step.adequacy`), `Demo.lean` (worked reductions). See §Metatheory. |

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
`map`, `Integer#times`, `Hash.new{}`), singleton methods (`def self.m`)/eigenclasses
(L2c; `class`/`module` bodies + `Class#new`/`initialize` + `method_missing` +
`super`/`zsuper` are done, L2a/b `impl-notes L17`–`L18`), splat/kwargs, class variables, `Float` **formatting** (Ruby needs
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

## Metatheory (proof of concept)

The sketch and PROJECT_PLAN §7 name the **inductive `Step` relation** the
definition of record, with `stepFn` its executable witness. `RubyCore/Proof/`
is a first, self-contained realization of that programme — evidence the
interpreter-first architecture admits real theorems — over an effect-light
**control-core** fragment (literals, local/ivar/global var + assign, `seq`,
`if`, `while`, `break`/`next`; see `implementation-notes.md` L13–L15 for scope
and the excluded heads). It is **not** on the default build target and is
expected to be reworked when L1/L2 change the machine shape.

Build and check:

```sh
lake build RubyCore.Proof.Adequacy RubyCore.Proof.Demo
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

`Demo.lean` exhibits the relation firing, a concrete 5-step reduction of `1; 2`
to the value `2`, and adequacy on a real initial config. The intended next
extension is `send` (fold `invoke`/`Builtins.run` in as a trusted oracle), then
`return`/frames and `begin` unwinding.
