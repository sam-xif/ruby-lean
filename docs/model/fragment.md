# The model: layout and fragment

RubyCore is a small-step machine (`stepFn`) plus a fuel-bounded interpreter
(`run fuel`), packaged from the start as a difftest system under test so it could be
compared with CRuby immediately. The written semantics, including why the inductive
`Step` relation is the definition of record, is `ruby-lean/RubyCore/README.md`. This
page covers the files, what the model supports, and how the generated files are
regenerated. Paths are relative to `ruby-lean/`.

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
| `RubyCore/Types/` | what is left of the type vocabulary the SUT still needs: `Ty.lean` (the type language), `Fragment.lean` (`--fragment`: is a program in the Sorbet fragment, with a reason per exclusion), `SigRead.lean` (`--sigs`: the signatures a program declares — stage 1 of the ratchet's pipeline), plus `Core.lean`/`Decls.lean`, the declaration table the surviving proofs are stated over. The checker built on top of these (`infer`/`inferOpen`/the certificate language) was removed — see [Metatheory](metatheory.md). |
| `Main.lean` | the SUT executable: RubyCore-JSON on stdin → Observation-JSON on stdout; **exit 3 = Unsupported** (reason on stderr), exit 1 = model bug |
| `RubyCore/Proof/` | **metatheory** (`lake build Metatheory`, or `scripts/check-proofs.sh` to also re-verify `#print axioms`; it had silently stopped compiling for 24 commits without either, L119): `Step.lean` (inductive control-core `Step` + `Step.sound`/`Step.deterministic`), `Adequacy.lean` (`Step.heap_monotone`, `Step.complete`, `Step.adequacy`), `TypeSafety.lean` (`invariant_sound` type-safety-by-reachability), `Demo.lean` (worked reductions + type-safety demos), the `KontFrame*`/`HeapFacts` continuation- and heap-framing lemmas, and — in `Proof/Judgment/` and `Proof/Static/` — the class-freshness and declaration-table lemmas **the live checker imports** (`Denote/Sem/{ClassHeap,ClassGrowth,SubclassHeap}`), which are therefore on the default target by way of `Denote`. See §Metatheory. |

## Fragment

Verified 2026-08-03 by probing the built binary. The current agreement numbers are in
the root `README.md`.

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
   why `Struct`/`Rational` wait on dispatching repr, see [Fragment](#fragment).)
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

