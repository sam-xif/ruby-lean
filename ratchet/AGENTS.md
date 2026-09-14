# AGENTS.md — `ratchet/`: the Sorbet-typed ladder

## Current state (2026-09-14)

The typed/safe gap is closed **by a theorem, not rung by rung**.
[`Denote/Typed/Bridge.lean`](Denote/Typed/Bridge.lean) proves

    validateD_safe_boot : validateD p d = true → bootOkB = true → StuckFree bootMachine p

axiom-clean, composing the checker's `validateD_typed`, the bridge `djudge_certified` (every
syntactic derivation is a certified one — it typechecks exactly while every rule has a clink)
and `dregistry_safe`. So **acceptance is the safety claim**: a rung is climbed when
`validateD` accepts it, and there is one reach number instead of two (§F32, closed).

**Fragment 49 rungs, reach 17**, **22 registered rules** (16 expressions + 6 list companions),
**0 owed**, **0 exempt**. Checker reach is 51; rung 018 is correctly rejected, the fragment's
prefix ends at 017. Agreement: **252 agree, 0 disagreements**. 44 rungs additionally carry a
worked theorem in `CorpusSafety.lean`, cross-checked against the stripped program — examples
and regression now, not the coverage story. The full gate is
[`scripts/run_typed_ratchet.sh`](scripts/run_typed_ratchet.sh), and it is RED when the
fragment claims something the bridge cannot back: a rule with no semantic proof, a shrunk
fragment, a worked theorem about the wrong program, or a moved floor.

The gate also checks Sorbet expectations, negative controls, floors, and the rules read
from each proof term. It must pass before committing. Use quiet mode; `--verbose` is only
for a failure whose captured error is insufficient. In a sandbox with a protected uv cache,
set `UV_CACHE_DIR=/private/tmp/ruby-ratchet-uv-cache`.

## The pipeline

Annotated `corpus/NNN-id.rb` → Sorbet signatures → annotation stripping → RubyCore JSON →
untrusted derivation emitter → Lean `check`, which returns a `DJudge` proof.
`build/` is generated. The corpus has 259 rungs; unsupported constructs remain explicit
coverage gaps. [`MainTyped.lean`](MainTyped.lean) reports checker reach;
[`SemLadder.lean`](SemLadder.lean) checks safety coverage and reports the unmet rungs.

## The proof boundary

[`Ratchet/Check.lean`](Ratchet/Check.lean) defines `DJudge`, `DJudgeAll`, `DJudgeSeq`, `DJudgePairs`,
and sixteen `DPrim` rows. [`Denote/Typed/Clink.lean`](Denote/Typed/Clink.lean) derives each
constructor's semantic obligation and registers only proved rules. **All four judgments
are fields of `DFam`**: no raw syntactic premise may bypass the registry — which is also what
lets `djudge_certified` be a mutual induction over all four (§F31 was the prerequisite).

The bridge deliberately runs *from* the syntactic judgment *to* `DJudgeC`, rather than the
checker returning a `DJudgeC` derivation: `Ratchet/` stays ignorant of `Denote/`, and
`DJudgeC dclinks` quantifies over every `DFam` closed under the clinks, so a second semantic
backend reuses the bridge unchanged instead of forcing a rewrite of `check`.

The semantic target is now `SemSafeCtxA`, with full incoming/outgoing context, locals, and
ivar indices. Its top-level specialization is equivalent to `SemSafeA = SemJudgeA ∧ SafeUnder`:
answer correctness and safety under a typed continuation. [`Compose.lean`](Denote/Typed/Compose.lean) proves the
continuation lifting; [`Run.lean`](Denote/Typed/Run.lean) exposes the same contract at
machine entries used by sequence and argument frames. Safety holds at every fuel.
`Context.lean` generalizes that run contract to distinct incoming/outgoing `Ctx`, local
environments, and ivar spines, with an equivalence to the existing fragment's target and
context-general local/assignment/sequence proofs. This is infrastructure for 052, not method
coverage: `defDecl`/`callSig` remain rejected. Before admitting definitions, check every body
against its parameter/return annotations, including uncalled bodies; require define-then-call
positive controls as well as declaration controls. Never treat a signature as its own proof.
`MethodEntry.lean` proves required-positional binding and the annotated parameter environment.
`Framed` now carries `FramePres`: uncaptured activations preserve inactive caller frames;
captured ones may still write through their captured chain. `MethodReturn.lean` restores the
caller frame and first-order local environment, and composes a body run through the real
method continuation. `MethodState.lean` proves full entry/return conformance and consumes
an annotated body proof through `enterUserMethod`; a real-boot identity-method example works
for every Integer argument. `MethodDispatch.lean` connects this contract to ordinary dispatch
and proves the actual `def` installation/lookup path, with visibility, shadowing, and hook
checks intact. `Sem/MethodHeap.lean` and `Sem/MethodInstall.lean` now preserve first-order
types and full conformance through fresh top-level definitions; reserving a name weakens
absence facts but grants no callable entry. A real-boot definition-step + installed-call
pilot now handles `add(x, y)` for every pair of Integers, consuming a body proof from the
annotations alone. `Primitive.lean` threads distinct incoming/outgoing contexts and ivar
spines through receiver/argument evaluation; all 16 rows require dispatch guards at the
final context. The existing `SemA.prim` is its top-level specialization. Literals, sequences,
and both conditional forms are also context-general; branches require matching outgoing
contexts/spines while joining local/result types. Arrays and interleaved hash pairs thread
all state indices as well; bare names require explicit absence/self guards. Thus all 16
expression proofs have context-general counterparts, with all three list companions.
`DJudge` and all three companions now carry those indices through `DFam` and the registry;
`djudge_context` proves the fundamental lemma at arbitrary contexts. The executable checker
now takes those incoming indices and returns every outgoing index with its derivation;
`CtxEq.lean` supplies proof-producing branch compatibility (unsupported syntax comparisons
decline). `certified_context` connects these results to semantics; the installed `add` pilot
now consumes a body certificate checked against its annotations, not a hand body proof.
`MethodCheck.lean` packages that proof as `CheckedBody`: required formal names/order,
first-order parameter/return annotations, exact return compatibility, and unchanged
context/spine are checked before the artifact exists. `checked_method_runSpec` consumes
it directly. Installed-signature/definition/call rules remain next. Explicit `return` needs an answer-contract extension. Neither boundary lemmas nor
declaration-only acceptance count as 052. `methodBootOkB` checks additional method-start
facts, and `methodInstallBootOkB` also checks top-level installation/lookup/hook facts;
these must join the validator's boot contract when methods are admitted.
The boot conformance hypothesis is `bootOkB = true`, checked at the real prelude boot;
`bootMachine` is phase two's fresh user-code machine, not the phase-one prelude evaluator.
`validateD_safe_run` additionally states safety over the executable `Semantics.run` itself.
Proofs use no `sorry`, `native_decide`, or new axioms.

Before authoring a rule, find its state-transport lemma. **That lemma determines the
premises and outgoing environment** (`Check.lean`, “Authoring a rule”). The composite
proofs exposed two missing facts: joins must not manufacture alias identity, and nominal
String membership needs a payload invariant. See
[`implementation-notes.md`, clink 74](implementation-notes.md) for the witnesses and fixes.

## Files to open

| Path | Role |
|---|---|
| `Ratchet/Ty.lean`, `Expr.lean`, `Deriv.lean` | Types, syntax, and certificate data |
| `Ratchet/CtxEq.lean` | Sound conservative syntax/context comparison for branch compatibility |
| `Ratchet/Check.lean`, `DerivControls.lean` | Derivation-returning checker and negative controls |
| `Ratchet/MethodCheck.lean`, `Denote/Typed/MethodChecked.lean` | Checked annotation/body artifacts and their method-entry contract |
| `Denote/Typed/JudgeA.lean` | Semantic judgment, continuation typing, literal/local rules |
| `Denote/Typed/Sequence.lean`, `Branch*.lean`, `BareName.lean` | Sequence, conditional, and bare-name obligations |
| `Denote/Typed/Array.lean` | First-order array evaluation, retention, and allocation |
| `Denote/Typed/Context.lean` | Context-indexed contract, specialization, literals, assignment, and frame composition |
| `Denote/Typed/MethodEntry.lean` | Required-positional method entry and annotated parameter-environment conformance |
| `Denote/Sem/FramePres.lean`, `Denote/Typed/MethodReturn.lean` | Caller isolation, local restoration, and method-continuation composition |
| `Denote/Sem/Reframe.lean`, `Denote/Typed/MethodState.lean` | Full frame-switch conformance and post-dispatch calls from annotated body proofs |
| `Denote/Typed/MethodDispatch.lean` | Actual definition/lookup/dispatch equalities and call safety from annotated bodies |
| `Denote/Sem/MethodHeap.lean`, `Denote/Sem/MethodInstall.lean` | First-order type preservation, name reservation, and full top-level installation conformance |
| `Denote/Typed/ArrayIndex.lean` | Array dispatch, integer indexing, bounds, and payload-class counterexample |
| `Denote/Typed/Hash.lean` | Interleaved key/value evaluation, duplicate keys, and allocation |
| `Denote/Typed/HashIndex.lean` | Hash dispatch, lookup, nil defaults, and default-value counterexample |
| `Denote/Typed/Primitive*.lean` | Primitive dispatch, allocation, argument composition, regression controls |
| `Denote/Sem/PrimHeap.lean`, `Denote/JoinState.lean` | Primitive heap invariants and sound binding joins |
| `Denote/Typed/Derivations.lean`, `CorpusSafety.lean` | Constructor-wise builders and 44 concrete safety proofs |
| `Denote/Typed/Bridge.lean` | `djudge_certified` (syntactic ⟶ certified) and `validateD_safe_boot` |
| `Denote/Typed/Safety.lean`, `RuleAudit.lean` | Syntax/proof cross-check and zero-exemption coverage gate |
| `Denote/Sanity.lean` | Executable boot conformance gate and its kernel soundness theorem |
| `scripts/run_typed_ratchet.sh` | Full pre-commit gate |

The material below is historical: it describes the deleted pre-answer-typed judgment.
Keep it as the investigation record, not as instructions for the current implementation.

# LEGACY — everything below describes the deleted judgment

**None of this is the current tree.** It documents `Ratchet.Judge`/`chk`, its 259-rung untyped
corpus, and the 48/83 semantic ladder, all removed in clink 68. It is kept because the
*learnings* are load-bearing and are cited from live code and from `found-issues.md`: the
seven rules that were false as stated, the nineteen stall points, the EMERGENCY EXIT's
diagnosis, the `kont_census` measurement that priced `KontOk` at 36 constructors, the
`context-splitting` redesign. Read it as history. Numbers in it are historical; do not plan
against them, and do not look for the files it names without checking they still exist.

## Checker status: **178 rungs of 259 — tier 13 complete, tiers 14–17 open**

`Ratchet/Validate.lean`'s `validate` covers **every tier of the ladder**, tier 13 whole, and a
good half of tiers 14–17: the eight literals,
`+`/`-`/`*`/`/` on `Integer`, `+` on `String`, the integer comparisons, the nullary total
queries (`to_s`/`zero?`/`length`/`nil?`), `!`, and `==` with an unconstrained argument (see
`EqSafe`), plus tier 3's locals (`var`/`vasgn`/`seq`, and a bare `vcall` gated on the
`BareNameError` table), tier 4's conditionals (`if'`/`ifNoElse`), tier 5's array and hash
literals with their `#[]`, tier 6's top-level `def` plus implicit-self calls, tier 7's
`class`/`new`/`@ivar`/instance dispatch/`self`/inheritance/`super`/singleton methods, tier 8's
modules, tier 9's `lambda`/`proc`/`#call`/`yield`/`&b` **and its builtin iterators**
(`each`/`map`/`select`/`sort_by`/`inject`, both `&` forms), tier 10's **metaprogramming**
(class reopening, `include`/`extend`/`prepend`, `method_missing`), tier 11's cross-products,
tier 12's **narrowing**, all of tier 13's **constants** (`casgn`/`const`/`cpath`/`cpath_asgn`,
class-body constants, `attr_reader`/`alias`/`private_constant`, nested namespaces under
qualified names, `Object#class`/`Module#to_s`, `Object#freeze`), tier 14's **optional, rest and
keyword parameters** (`Judge.callDefKw` and the split argument list), tier 15's **`String` and
`Regexp` rows** (a `Regexp` being opaque), tier 16's **`while`, the `next` guard, value-`===`
and `begin`/`rescue`** (with `raise` typed `.never`), and tier 17's **collection rows and
iterators** (`<<`, `compact`/`uniq`, `any?`/`all?`/`find`/`filter_map`/`flat_map`/
`each_with_index`) — **173 rungs**.

**The ladder was climbed on 2026-09-01, and the corpus grew the same day** — from 136 rungs to
**232**, by pointing it at a *target* instead of at the feature list (§2026-09-01: the Homebrew
slice). Tiers 1–12 are unchanged and still at every recorded target: 122 of their 136 rungs
climbed (121 then, plus `metaprog-method-missing-splat`, retargeted and climbed on the same day
by tier 14b's work — see §Ty language gaps), and the 14 that are not are permanent by design
(12 `unsafe_program`, 2 `ty_language_gap`). Tiers **13–19** are the new 96, and 8 of them were
already climbed the day they were written.

**Tiers 13–17 were then worked the same day**, in clinks 27–41 (`implementation-notes.md`):
tier 13 **complete** (12/13, six clinks), and tiers 14–17 taken from 1/15, 3/19, 4/15 and 0/23 to
**9/15, 13/19, 10/15 and 11/23**. So the headline was **177 of 232**, with **34 rungs differing
from their recorded target** (down from 81) and 21 permanent negatives — one fewer than before,
because a flagged `Ty` gap turned out not to be one (§Ty language gaps, clink 40).

**Clink 64 found and fixed a reachable soundness bug** (`found-issues.md` §F23), which is what
moved the denominator to **256**: `Judge.while'` and `Judge.iterBlock` both check the body's
**outgoing** environment (`Γb = Γ`, `capIntact … Γb'`), and a `next` leaves the iteration *in the
middle* — so `while …; x = "s"; next if c; x = 2; end; x + 1` was certified `Integer` against a
CRuby `TypeError`. Fixed by a `nxtPrefixOk body` premise on both rules (*a `next` may only occur
before anything has assigned*, so the escape environment **is** the incoming one the outgoing
premise pins). Both witnesses are corpus rungs and both are now rejected; `ctl-next` still climbs.
Permanent negatives: **26** — the other three are §F24 and §F25, the same question asked at
`break` and at `raise`. `validate` **already** rejects all three witnesses, and the *controls* are
what tell the two apart: §F24's break-free controls validate `true`, so the `break` is what is
being refused; §F25's raise-free control is rejected too, so `begin`/`rescue` is simply not typed
yet. All three are on file as the regression pins for the day a `break` rule or a `Judge.begin'`
is written — `nxtPrefixOk` covers neither.

**Clink 46 made it 178 of 235**, and the three new rungs are a *soundness* fix rather than
coverage: the semantic ratchet found `Judge.vasgn` accepting a type-stuck program
(`found-issues.md` §F1), and two of the three are the permanent negatives that pin the fix
(§Closure captures go stale). Permanent negatives: **21**.

**`Ty` grew one constructor**: `hashOf (key val)` (clink 41), the first grammar change since
tier 9's `clos`, discharging §Frontier item A. Uniform rather than keyed, because the target reads
its tables with a variable key; invariant, because clink 39's `Array#<<` had just shown that
invariance is what keeps `arrayOf .never`-means-provably-empty honest.

Tiers **1–3, 5, 7, 8, 10 and 13** are now at every recorded target.

**What a constant cost** (clink 32 has the table). Constants live in **`Ctx.consts`**, keyed
by absolute path (`"::LIMIT"`, `"::Box::SIZE"`), because the three obvious homes each fail for
a checkable reason: a syntactic pre-pass table cannot know a type and is order-blind
(`X + 1; X = 10` raises `NameError`), `Env` is replaced at every call so a method body would
not see one, and a fourth threaded index on `Judge` would re-index every rule and every
derivation. `Ctx` is carried into method bodies for free — which is the right semantics, not a
trick — and grows at `JudgeSeq.cons`, which is why order-sensitivity holds for the same reason
`foo(); def foo; end` has no derivation. The one signature change is that **`Ctx.afterStmt`
takes the statement's type**, since that is what a `casgn` binds.

The tier's real surprise is **four new premises on rules already on file**
(`classStmt`/`moduleStmt`/`constCls`/`constBuiltin` all gained `constGet? κ n = none`), every
one of them because a `casgn` can rebind a name a class declaration owns: `X = 5; class X; end`
raises `TypeError` and `class X; end; X = 5; X.new` raises `NoMethodError`. Both are controls,
both sound rejections. A class-body constant's type is *guessed* syntactically by `constLitTy?`
and *discharged* by `classStmt`'s `JudgeConsts` premise **at the definition site** — lazily at
each read is unsound, because `κ.classes` only grows and a reopened class can retype an
initializer. Nested declarations enter `CTable` under their **qualified** name (`"M::Box"`,
which is the string CRuby's `Box.name` answers), and the whole cost of a namespaced class is
naming: dispatch was already a table lookup on a string.

What that means is different above and below the tier-12 line. Above it a rung isolates a
feature and a `false` names a missing rule. Below it the corpus is Homebrew's own code, and a
whole-file `false` says only that *something* in a 1,700-line program is out of the fragment —
the same shape of answer `homebrew/slice-verdict.md` reaches from the other side (`reject` with
basis `uncertified`). Tiers 13–17 exist to make that answer decomposable: they are the syntactic
forms the slice uses and the corpus did not, one rung each, **measured rather than guessed**.

- **21 permanent negatives** (`unsafe_program`) — programs that really raise
  `NoMethodError`/`ArgumentError`/`TypeError`, kept as the soundness regression tests. A `true`
  on any of them is a bug, not progress. Seven came in with tiers 13–19, one per new tier, plus
  `slice-adversarial` (§Tier 19); two more with clink 46's soundness fix
  (`lambda-capture-reassigned-unsafe`, `lambda-captures-own-target-unsafe`), and those two are
  the first that were a *regression* test for a bug the ladder actually shipped rather than a
  control written alongside a rule.
- **3 `Ty` language gaps**, each naming a specific missing constructor: an optional/rest arity
  spine (`proc-arity-leniency`, `metaprog-method-missing-splat`) and a length-indexed array
  (`narrow-nilable-and-union`). See §Ty language gaps. **The slice asks for all three again**,
  which is the strongest evidence the ladder has produced that they are real: the length-indexed
  array is `String#match`'s captures, `arr.first`, and every `a, b = s.split("-")` in
  `identify.rb`.

### Closure captures go stale, and `Judge.vasgn` did not know it (clink 46)

**The first soundness bug this ladder shipped, and the second ladder is what found it.**
`Judge.lambdaLit` records the creation-site environment into the type
(`.clos idx (envToSpine Γ) …`). A Ruby block captures locals **by reference**, so that spine
is a claim about a *binding*, not about a value — which is exactly what `Ty.sameAs` is, and
`Judge.vasgn` already knew it about `sameAs` (it applies `killAliasesTo Γ' x`, and its
docstring enumerates the three ways an alias goes stale). It did the same job for no
`Ty.clos`. So:

```ruby
x = 1
f = lambda { x }
x = "a"
f.call + 1        # CRuby: TypeError.  validate, before clink 46: true, type Integer.
```

`validate` returned **`true` on a type-stuck program** — the one thing the permanent negatives
exist to make impossible. `capIntact` is a different guard: it stops a block *body* from
retyping a captured local, not ordinary code after the literal.

**The fix is two functions and one premise** (`Ratchet/Ty.lean` §Stale closure captures).
`killClosOver`/`killClosOverSpine` widen to `.any` every binding — and every ivar-spine entry —
whose type records a capture of the assigned name at a *different* type, and `vasgn`/
`vasgnAlias` apply them beside `killAliasesTo`. Both are the **identity on a closure-free
environment**, which is why 177 derivation terms in `Ratchet/Rungs.lean` needed no edit.

The premise is the other half, and it is the half `killClosOver` cannot do: `x = lambda { x }`
puts the stale record in the type being **bound**, so there is nothing left to widen and the
rule's own type index would be wrong. `capStale x τ τ = false` is an `autoParam` premise
(`:= by rfl`), which is what let it be added without touching a derivation either — the same
trick `Judge.varAlias`'s docstring recommends for a `Bool` side condition.

**Precision is kept where it is sound.** `x = 1; f = lambda { x }; x = 2` still types: the
recorded capture is `x : Integer` and that is still true, so `capStale` says nothing is stale.
That is the same boundary `capIntact` draws.

Three corpus rungs (tier 9) and two `CheckRungs.lean` controls pin it — the two unsafe programs
as permanent negatives, the same-type reassignment as the precision control, and the controls
as the place where the rejection is labelled *sound* by running the program and confirming it
is genuinely type-stuck. **None of these existed before**, and that is the point: the corpus
ladder read 232/232 and 140/140 with the bug in place. See `found-issues.md` §F1 and
`implementation-notes.md` clink 46.

**Tier 12 (clinks 13–17, 25, 26) is where `nilable` and `union` stop being write-only.**
Narrowing lives *inside* `Judge.if'` — each branch is typed in `narrowEnvs κ.classes c Γc` and
`narrowSpine κ.classes c Ic`, both **total** functions that are the identity on every condition
they do not recognize, which is why folding narrowing into the existing rule did not disturb a
single derivation already on file. Three recognized conditions (`if x`, `if x.nil?`,
`if x.is_a?(C)`), which apply to a **local or an instance variable** (`narrowCond?` returns the
`VarKind`); four type-level refinements (`truthyTy`/`falsyTy`/`isNilTy`/`nonNilTy`) resting on
the single fact that Ruby's only falsy values are `nil` and `false` — which is why
`falsyTy .int = .never` is *precise*, not reckless — plus `isATy`/`notATy`, which project a
union member-by-member using complete ancestor lists. Two rules beyond `if'` carry refinements:
`JudgeSeq.guard` (the `return 0 if x.nil?` idiom — narrowing by *elimination of a branch that
leaves*, and therefore a fact about statement order, so it belongs to `JudgeSeq`), and the
`ifNoElse` twin. Clink 16 also **reversed clink 6's ivar-spine agreement premise** into a
`joinSpine`, which is what makes an ivar typed differently on two constructor paths describable
at all. Clink 14 records that **`subTy` is still unused** after two clinks predicted narrowing
would bring it due: refinement needs class *membership* (the ancestor walk), not `Ty`
subsumption.

**Tier 10 turned out to be less exotic than its name.** `metaprog-class-reopening` was not
metaprogramming at all — `extendClasses` shadowed instead of merging, which was simply *wrong*
about what a `class` statement does (clink 21). `include`/`extend` are two fields on `Cls` and
one step in the lookup (clink 22). `prepend` is the one that forced a structural change: the MRO
became a **list** (`mroList?`/`searchMro`/`afterInMro`), because a prepended module's "next" is
the class that prepended it and no `super?` walk can find it — and `super` is now literally
"keep going from where I was found" (clink 23). `method_missing` needed a table whose
*completeness* is the soundness condition rather than the coverage one (`ObjectMethod`, clink
24) — the one place on this ladder where that inversion holds.

`Judge` threads an environment (`Judge Γ e τ Γ'`); see `implementation-notes.md` clink 2
for why the output environment is not optional. Tier 4 added the two **joins** — `joinT`
on types and `joinEnv` on environments — which is where `Ty.union` stops being inert;
clink 3 has the argument that producing a union is sound *because nothing consumes one*,
and why `joinEnv` is a soundness requirement rather than a precision nicety (it is what
stops the checker certifying `corpus/042-if-does-not-leak-reassignment`, whose recorded
target was wrong and is now `false`). Tier 2's last two rungs, `bool-and`/`bool-or`, came
in with tier 4 for free: Ruby's `&&`/`||` desugar to a temporary local plus a `seq` and
an `if`, so they were never sends at all (clink 1 predicted this; clink 3 cashes it out).

Tier 5 reuses tier 4's join twice over and adds nothing structural: `a[0]` is
`send a "[]" [0]` — Ruby has no index syntax — so indexing is two `PrimSig` rows, and an
array literal's elements are typed by the *same* `JudgeAll` that types a send's arguments.
What is new is the type language pulling its weight: `elemTy` joins the element types
(`[1,"a",true] : arrayOf (union Int (union String Bool))`), `Array#[]` returns
`nilable elem` because an out-of-range index is `nil`, and a hash literal is the bare
`.cls "Hash"` with a premise (`JudgePairs`) that carries no type at all — the first place
"these subterms must be well-typed" and "and here is the type" come apart. Clink 4 has the
three prices this charges, each a recorded negative control.

**Tier 6 is the shape change.** `Judge` gained two indices — `DefTable` (methods already
defined, *threaded* through `JudgeSeq` so `foo(); def foo; end` has no derivation) and
`AsmTable` (instantiations currently assumed) — plus `Ty.never`, a bottom type. There are
**no signatures**: Ruby writes no parameter types, so `Judge.callDef` types a method's body
once per *call-site argument shape*, in an environment made of just its parameters at just
those types. Recursion is broken by assume-then-verify, where the candidate return type is
found by a first pass that types the recursive call at `.never` and is then **discharged by
a second pass that must reproduce it** — the first pass is a hint, and `chk_sound`'s proof
visibly never uses its derivation. `chk` takes fuel from here on, which is a completeness
knob and not a soundness one. Clink 5 has all of it, including the three controls (one per
premise added) whose rejections are *sound* rather than conservative.

**Tier 7's object model is where the type language starts describing objects.** `Ty.inst n
ivars` carries an instance's **ivar spine**, because an object's observable type is not its
class name: `Point.new(1,2)` and `Point.new("a","b")` are both `Point`s and `getX` answers
differently, and Ruby writes no ivar types, so the instantiation is the only moment the
information exists. `Judge` bundled its input-only components into one `Ctx` (classes,
methods, assumptions, the type of `self`) and grew a *second* threaded state, the spine:
`Judge κ Γ I e τ Γ' I'`. Dispatch reads both halves of what it needs off the receiver's type.
The one genuinely load-bearing invariant is that **a method may not retype an instance
variable** (`callMethod`'s outgoing spine must be its incoming one) — without it a caller
keeps a stale type after a setter runs, and clink 6's most important control is the program
that then raises. That premise is also what makes spines *complete*, which is what makes
`ivarRead`'s `nil`-for-never-assigned sound rather than a guess.

**Tier 7's hierarchy** (clink 7) is three rules about "which class?" having a non-obvious
answer. `mroGet?` walks `Cls.super?` and reports **where it landed**, which is what `super`
needs: `super` delegates from the class the running method was *declared* in, not the
receiver's, so `Ctx` carries a `frame`. The spine threads *through* a `super` call, so
`@sides` can be set by the parent inside the child's object. Singleton methods are a separate
table (`Cls.smethods`) whose bodies are judged with `self` typed `.clsOf n`, which is what
makes a bare `new` inside `def self.origin` mean "allocate one of me". `subTy` is *still*
unused — inheritance turned out not to need it, because dispatch is by walk rather than by
subsumption.

**Tier 8 (modules) cost two rules**, and the cheapness is the finding: `M.foo` for a
`def self.foo` is `callSMethod` unchanged, because a module already *was* what tier 7 made a
class object be — a thing with a singleton method table behind `Ty.clsOf`. Only `moduleStmt`
(a statement type) and `selfSCall` (the bare-name form, where `self` is a `.clsOf` rather than
an `.inst`) were missing. What tier 8 genuinely needed was a *guard*: `Cls.isModule`, because
a module cannot be allocated — `M.new` raises `NoMethodError`, and without the flag it would
fall through to the zero-argument allocator. No rung writes `new` on a module, so that guard
lives entirely in a negative control.

**Tier 9's callable values** (clink 9) needed a new idea, and it was *not* `Ty`'s arrow spine:
an arrow needs parameter types and **Ruby writes none**, so `f = lambda { |x| x + 1 }` has no
principal type without type variables. Instead `Ty.clos idx captured` makes a callable's type
a **reference to its code** plus the locals it closed over, and a call instantiates the body at
the call site's argument types — `Judge.callDef`'s move lifted to a value. `idx` indexes a
whole-program block table collected *before* checking (`collectBlocks`), which is why tier 9
needed no new threaded state; `captured` is in the type because two identical block literals
share a table entry but need not have closed over the same environment. `lambda-returns-lambda`
is currying with no arrow type anywhere in the derivation. The cost that showed up along the
way: `Expr`'s derived `BEq` does **not** kernel-reduce (nested inductive), so this package
carries its own structural `exprEq` — see clink 9 for the two non-obvious constraints on
writing one.

**Tier 9b** (clink 10) is the same block literal in a different position: passed to a method
rather than being the value. `Ctx.blockTy` carries it, because Ruby passes a block **out of
band** from the argument list — so `callDefBlk` puts it in two places at once, `blockTy` for
`yield` and `paramEnvB` for a `&b` parameter. Lambda-local `return` is handled by
`bodyResult`, a function on the body's *whole shape*, because the obvious rule for `.ret` is
unsound (`def f; return "a"; 2; end` would validate at `Int`); a control holds that in place
by execution. `vcallDef` closes the top-level-bare-name gap `bareName` had recorded since
tier 6.

**Tier 11 (clink 11) adds no feature — it adds *combinations*.** It exists because a
corpus-driven ladder measures what the corpus asks for, and nothing in the corpus combined a
class with a block, so `A.new.a { |v| v }` had no rule and nobody noticed until a human wrote
ordinary Ruby. Two blockers, both restrictions introduced deliberately in earlier tiers: no
rule covers an explicit-receiver send *carrying* a block (`callMethod` wants `blk = none`,
`callDefBlk` wants an implicit receiver), and behind it `closCall` requires
`κ.selfTy = none`. **Sketching one of these rungs also found a real unsoundness** in the
committed tier-9 rules — a block captures locals by reference, and the call rules discarded the
body's outgoing environment, so `a = 1; t { |x| a = "s" }; a + 1` validated and raised. Fixed
by the `capIntact` premise. The general rule, now rediscovered three times (ivars in clink 6,
branch environments in clink 3, captured locals here): **a callee may not retype state its
caller can still see.**

What is different from the pre-restart version this replaced: the checker is no longer
the specification. `Ratchet/Judge.lean` is — a hand-authored typing judgment with one
constructor per rule — and every rung in the covered fragment has a **derivation term**
on file in `Ratchet/Rungs.lean` that Lean's kernel checks, plus
`Ratchet/Proof/ChkSound.lean`'s `chk_sound : chk e = some τ → Judge e τ` tying the
executable checker back to it. And `40` is now the *only* number
`scripts/run_ratchet.sh` reports, because there is no longer a second, softer way for a
rung to count: certificates are gone (§Claim-free).

## 2026-09-01: the Homebrew slice — 136 → 232 rungs, tiers 13–19

The instruction: *the ratchet is climbed but it is not good enough. Expand it with the
syntactic forms in the Homebrew slice files we have not yet covered, then each slice file
(with realistic main scripts that exercise their contents), and finally the entire linked
slice.* Three stages, added as **seven new tiers**.

The change of method is the point. Tiers 1–12 were written from a feature list, and
§Frontier's honest complaint about tier 11 — "a corpus-driven ladder is blind to its own
cross-products" — generalises: it is also blind to whatever the *target* happens to be
made of. So tiers 13–19 are written from `homebrew/PLAN.md` §2's slice: `version.rb`,
`version/parser.rb`, `pkg_version.rb` and `vulns/{semver,cvss,purl,identify,vulnerability}.rb`.

### The syntactic gap, measured

A node-head census of the **linked slice's** desugared AST against every corpus rung's,
before this pass. Twelve heads (and three parameter kinds) appear in the slice and appeared
in the corpus **zero times**:

| slice count | head | tier that now covers it |
|---|---|---|
| 155 | `cpath` (`A::B`) | 13 |
| 105 | `kwargs` (call-site keywords) | 14 |
| 58 | `regexp_lit` | 15 |
| 54 | `casgn` | 13 |
| 11 | `next` | 16 |
| 8 | `pkey` | 14 |
| 4 | `begin` (rescue/else/ensure) | 16 |
| 3 | `alias` | 13 |
| 3 | `splat` | 14 |
| 2 | `popt` | 14 |
| 1 | `pkwrest` | 14 |
| 1 | `while` | 16 |

Plus three that the corpus had but at a rate that hid them: `sym` (299 vs 2), `return`
(98 vs 2), `flt` (32 vs 1) — and **85 `__as_string` calls**, i.e. string interpolation,
which is not a head at all and which the corpus contained none of. Tiers 13–17 are one
rung per form, 85 rungs, ordered so that no rung depends on a form introduced later.

Reproduce the census against the current corpus with the linked program
(`ratchet/slice/slice-whole.rb`) — the rung *is* the measurement's input.

### What the measurement bought immediately

**Eight of the 85 were already climbed**, with no rule written, and each is a finding
rather than a freebie (derivations and reasoning: `Ratchet/Rungs.lean`, the tier-13–17
section):

- `param-block` — `def run(&b)` types today. §Frontier item 11's "the cleared
  implementation rejects any `def'` using `Param.block`" is **stale**: tier 9b's
  `callDefBlk`/`paramEnvB` already bind it.
- `ctl-unless`, `ctl-ternary`, `ctl-or-assign`, `ctl-safe-nav` — all four are sugar, and
  the desugarer has already turned them into `if`/`seq`/`vasgn`. The last two are the
  interesting ones: `x ||= 5` types `Integer` rather than `T.nilable(Integer)` *only*
  because tier 12's `falsyTy .nilT = .never` reads the then-branch as dead, and `x&.length`
  is clink 17's **aliasing** machinery driven by a temporary nobody wrote by hand.
- `str-interpolation` — the best of them. `"hello #{name}"` does not desugar to a `to_s`
  chain; it desugars to a temporary plus `if String === __dt_t1 then __dt_t1 else
  __dt_t1.__as_string end`. So the rung climbed with **no `__as_string` row at all**:
  `caseEqQuery` refines the else-branch to `.never`, `primNever` types the send there, and
  the join is `String`. Its twin `str-interpolation-nonstring` (an `Integer` in the braces)
  is *not* climbed, because there the else-branch is live — the two sit next to each other
  in the corpus for that contrast.
- `sym-literal`, `sym-compare` — the second is a negative finding: `Object#==`'s
  unconstrained-argument row (tier 2) already covers symbol comparison, so a checker
  growing a `Symbol#==` row would be adding one it does not need.

### Tiers 18 and 19: the slice files, and the whole slice

Eight per-file rungs and three whole-program ones. Their Ruby is **not** written in
`scripts/generate_corpus.py`: it is composed by `scripts/build_slice_rungs.py` out of
Homebrew's own source — boot stubs, then `linker` over the file's require-closure, then a
driver from `slice/drivers/` — and committed under `slice/*.rb`, so regenerating the corpus
needs no vendored checkout. Each driver makes **real calls only**; no value is printed that
the file would not compute.

They are ordered by dependency, which is also roughly by size: `semver.rb` (219 lines
composed) through `vulnerability.rb` (1,734) to the whole linked slice (2,176). Every one
of the eleven **runs in the model and agrees with CRuby**, which is the precondition for a
rung existing at all (§Architecture) and is not free at this size.

Tier 19's three rungs are the same linked program under three drivers, and the pair that
matters is `slice-whole` (target `true`) and `slice-adversarial` (target **`false`,
`unsafe_program`**). The second is `homebrew/slice-driver/probes/adversarial-inputs.rb`:
the same entry points, with only the advisory Hash and the version String varying over
shapes a caller can actually supply, reaching five type-family raises — four
`ArgumentError` from `Version.new("")` and two `TypeError` from `Integer#[]` — two of them
from a *schema-conformant* advisory. So the whole-slice program is type-safe **only under a
precondition on its inputs**, and having both rungs on the ladder is the sharpest statement
it makes about what a `validate` verdict does and does not claim.

### One bug found on the way, in the harness rather than the checker

`version/parser.rb` guards with `return if match.blank?` and `return @block.call(version)
if @block.present?`. The shared boot stub (`rspec_harvest.BLANK_STUB`) is upstream's
`Object#blank?` alone — `respond_to?(:empty?) ? !!empty? : false` — which is right for
Array/Hash/String/Symbol and **wrong for `nil`**, which upstream declares blank and the
stub reports as *present*. With only that row, a non-matching regex reaches `nil.captures`
and an absent block reaches `nil.call`: `RegexParser#parse` is unusable. It went unnoticed
because the harvested corpus difftests *agreement*, and both executors were wrong together.
Fixed for the ratchet's rungs by `build_slice_rungs.py`'s `BLANK_NIL_STUB` (the
`nil_class`/`false_class` rows, verbatim from upstream), added there rather than in the
shared harness so the harvested corpus's programs do not change underneath it. That the two
stub sets now differ is recorded here on purpose.

### Everything this pass found outside the checker is in [`found-issues.md`](found-issues.md)

Six model gates, one silent divergence, two boot-stub bugs and a performance cliff, each
with a minimal reproducer that was actually run. The headlines: **the model does not
enforce `sig`s**, so a sorbet-runtime `TypeError` CRuby raises is simply absent (A1) — the
wrong direction for a reachability argument, on a target that is `# typed: strict`
everywhere; **`<=>` dispatch from a builtin collection operation** is unmodeled, so
`Version`s cannot be `sort`ed (B2/B3); and the `blank?` stub bug above is C1. Rungs were
routed around all of them rather than smoothed over, per §Frontier item 15 — a rung must
not attach a type to a program the model cannot execute.

## Semantic denotation status (`Denote/`): **built, first-order fragment proved, arrow specified**

**A detour from the ladder, and it moves no rungs.** `Ratchet/Judge.lean` says what the
checker *derives*; `Denote/` says what a `Ty` **means** — a predicate over the real
`RubyCore` heap and values, so that "why is `Judge` right?" becomes a question with a
statable answer instead of a docstring. Maintained separately from the syntactic judgment:
`Denote/` imports `Ratchet/Ty.lean` and `Semantics/`, imports no `Judge`, and nothing else
in the package imports it. Its own design record is [`Denote/notes.md`](Denote/notes.md).

It generalises `CheckRungs.lean`'s `expectedClasses` — a `Ty → List String` reading a type as
"the class names its values can have", whose docstrings say three times that it cannot look
inside an array, an object, or a Proc. A denotation that recurses closes all three.

- **`Denote/Val.lean`** — the probes: immediate shape, nominal-through-the-heap
  (`classNamed?`/`isAName`, so `.cls "Foo"` is the machine's own `is_a?` at the *current*
  heap and a class the program has not defined yet has no instances), payload projections.
- **`Denote/Apply.lean`** — `applyIn`: how you *call* a Proc value from inside a proposition.
  Values are not syntax, so it pre-binds them as locals in a pushed frame and evaluates
  `__den_f.call(__den_a0, …)`. Plus `Returns`, `Reaches` (the reflexive-transitive closure of
  `Interp.stepFn`), and the closure-scope readers `frameLocal`/`closSelf`/`closLocal`.
- **`Denote/Den.lean`** — the master `denM : Ty → Machine → Value → Prop` (mutual with the
  arrow-spine walk `denApp` and the binding-spine walk `denSpine`), the heap-only view
  `den : Ty → Heap → Value → Prop`, `FirstOrder`, and **`denM_heap_only`**: the machine
  argument is irrelevant for every arrow-free/`clos`-free type, so the brief's
  `Ty → Heap → Value` signature is met exactly where it is meaningful. Every `Ty`
  constructor has an arm, `sameAs`/`ivar0`/`never` included.
- **`Denote/DenB.lean`** — the computable core `denB : Ty → Heap → Value → Bool`, plus
  `closB` (machine-indexed, because `clos` *is* decidable once you have frames).
  `denB_sound` at every type; `denB_iff` (an `↔`) on `FirstOrder`.
- **`Denote/Ext.lean`** — **`Ext`**, "the same machine, later, having allocated" (same frames,
  same stack, a heap that only grew), plus one lemma per probe across it. This is what makes
  the denotation usable by a rule that allocates; see §Semantic ratchet status. The first file
  here to import `RubyCore.Proof.*`.
- **`Denote/Grow.lean`** — **`denM_ext`**: a type's meaning survives an allocation. One
  induction, and the arrow case is free because `denM`'s arrow arm was defined to quantify
  over `Later`-futures.
- **`Denote/Local.lean`** — the other machine change: **`Machine.setLocal`**. `denM_setLocal`
  is the transport, and unlike `denM_ext` it has a **side condition** — `capStale`, the same
  function `Judge.vasgn` widens bindings with. Also the `setLocal`/`getLocal` lockstep
  (`getLocal_setLocal_self`: the value `x` names after the write is the value written, which
  is why `setLocal.owner` and `getLocal.go` have to be shown to stop at the same frame).
- **`Denote/Arrow.lean`** — `ArrowFlat` (the uncurried arrow), `ArrowExt` (it at every
  `Ext`-future, which is what `denM`'s arrow arms actually say) and `denM_arrowOf` proving the
  latter equals the spine denotation; `ArrowStable` (the arrow at every *reachable* machine —
  the honest target for a call-it-later arrow, stronger than both, and not what the checker
  infers today); `ClosArrow`, the shape of the bridge a `Judge.closCall` soundness proof would
  need.
- **`Denote/ArrowCheck.lean`** — the arrow's computable half, stated in the only sound
  direction: a true arrow passes every sample (`arrowCheck_of_arrowFlat`), so **a failing
  sample refutes the arrow** and is the counterexample. Same move as
  `../bounded-effect-checking.md`'s bounded search and `../type-safety-by-reachability.md`'s
  witness direction, applied to arrows.
- **`Denote/Sanity.lean`** — **the ladder is not vacuous.** Every obligation begins
  `∀ m, StateOk κ Γ I m → …`, so an unsatisfiable `StateOk` would make all 83 vacuously true —
  a live risk from the moment `strLit` added two components that are claims about the *heap*.
  `stateOk_boot` exhibits the model: `StateOk ctx0 [] .ivar0` at the **real prelude-booted
  machine**, axiom-clean. Conditional on one `Bool` (`bootOkB`) rather than `decide`d, because
  the booted heap is the output of `Interp.run 200_000` over the whole prelude and kernel
  reduction of that is not on the table; the `Bool` is a `#guard`, i.e. a build gate, and
  `native_decide` was rejected for the axiom it costs. Verified against a decoy (a misspelt
  class name fails the guard).
- **`Denote/Examples.lean`** — **33 `#guard`s that run real programs under the real `stepFn`
  from the real prelude-booted heap** and ask the denotation about the value produced. The
  build is the gate: if the denotation and the semantics disagree, `lake build Denote` fails.
  They cover what `expectedClasses` could not — `[1,2,3] : arrayOf int` but not
  `arrayOf float`, `[] : arrayOf never` (the "provably empty" reading, confirmed),
  `hashOf String Float` on a real hash payload, `Box.new(1) : inst "Box" {@x: int}` and the
  lazy-nil ivar, a lambda's captured `x = 7` read out of `Machine.frames`, and both halves of
  the arrow (`(Integer) → Integer` survives; `(Integer) → String` is refuted).

Axiom-clean throughout (`propext`/`Classical.choice`/`Quot.sound` only); every proof file
ends with its own `#print axioms`, as `Ratchet/Proof/ChkSound.lean` does.

**Not built, on purpose** (see `Denote/notes.md` §What is deliberately not built): no `subTy`
soundness, no narrowing soundness — each now *statable*, which is the point of having built
this first. The one item on that list that has since been **taken up** is `Judge` soundness:
`Denote/notes.md` parked it because it needs an evaluation relation for `Ratchet.Expr` while
the only executable one is over `RubyCore.Expr`. `Denote/Sem/Trans.lean` supplies the
translation and §Semantic ratchet status is the ladder that climbs it.

## [`context-splitting.md`](context-splitting.md) — the `Ctx` redesign *(**built, steps 1–5**)*

Positive facts that grow, negative facts that shrink, lexical scope that does neither — and
`Judge` threading the first two out as `κ'` the way it already threads `Γ'`/`I'`. Written
2026-09-09 after L268 measured that `StateOk` transports across `afterStmt` in **neither**
direction and §F20 showed the same defect is a *reachable soundness bug*.

**All five migration steps are on file** (clink 61), each measured, **and no rung moved in
either direction at any point**:

* **step 2** — `Ctx` split into `Pos`/`Neg`/`Scope`, made cheap by a `@[reducible]` accessor
  layer so every `κ.classes` in the rules and proofs reads as before;
* **step 1** — `Neg` seeded whole-program and keyed by receiver port. **§F20 closed**; negative
  controls **145 → 148**, one per witness shape. §11's first open question answered: the keying
  pays for the seeding *exactly*, on all 254 rungs and not just the six §10.1 priced;
* **step 3** — `Judge` threads `κ'`. `Judge.out_afterStmt` (`cases h <;> rfl`) is the proof that
  the threaded judgment derives exactly what the `afterStmt` one did — the signature changed and
  **no derivation term moved**;
* **step 4** — `SemJudge` claims outgoing conformance at **both** `κ` and `κ'`. It is *not* the
  "move the conclusion to `κ'`" §8.1 asks for: moving it weakens the premise every non-declaring
  rule lives on;
* **step 5** — **`JudgeSeq.cons` discharged**, axiom-clean. Semantic ratchet **47 → 48 of 83**.

Getting step 5 corrected the document's central claim (its own **§12**, `found-issues.md` §F21).
§3 prices the down-transport at "antitone, one line" on §10.3's grounds that the facts are
"keyed and immutable-per-key". They are not: `consts` is keyed and **mutable** (`extendConsts`
is `envSet`), and `BaseChainsOk`/`DeclClassOk` have κ-dependent *antecedents* that fire on fewer
inputs as the context grows. The *up* transport was removed by step 1 — its components read
`Neg` now, which `afterStmt` does not touch — and the down one splits three ways: **free** where
`Pos`'s lists genuinely grow (`mergeCls` **prepends**), **invariant** for everything reading
`Neg`/`Scope`, and **owed** for the rest, which `Ratchet.ctxKept` states decidably and all 178
derivations discharge by `rfl`. Three more of the antitone guards were fixed by applying §2's own
test to them and moving them into `Neg` (`wholeCls`, `boundConsts`) — strictly more conservative,
and measured to cost nothing.

Contains: the three pieces of evidence, the split, why every transport then goes the right way,
where the disjointness actually is (**between** the polarities, not within one — same-polarity
facts conjoin for free), what it buys the seal (footprints over **frames**, not over the heap —
the capture graph is a proved DAG, the object graph is not), what it explicitly does not buy,
a six-step migration, four rejected alternatives, and §12's correction. **Step 6 (footprints and
the seal) is untouched**, as its own piece.

## The clink registry (`Denote/Clink/`): **the judgment is generated from the proofs — 48 rules registered, growth gated**

**Reshaped 2026-09-11.** This replaces the framing the section below describes, and the
replacement is structural rather than presentational: **a rule enters the judgment only as a
`Clink`, and a `Clink` cannot be constructed without its semantic proof.** Not by convention
— by typing.

### What was wrong, in three sentences

The judgment was an independent inductive (`Ratchet.Judge`, 83 constructors) and the semantic
side was a *report* (48 obligations discharged, the gap printed by `lake exe semladder`). So a
rule could be authored, used by `validate`, and counted as a climbed corpus rung with no
justification at all; **seven of the undischarged rules turned out to be false as stated**
(§F19/§F23/§F24) while already being in the judgment and already reachable by a certificate;
and the only theorem that would have tied the 48 proofs to anything was one 83-case mutual
induction, so it could only close at 83/83, so it never closed, so nothing forced the
pairing. `implementation-notes.md`'s EMERGENCY EXIT (clink 64) is what that dead end looks
like from inside: three consecutive sessions of verified work moved the number 47 → 48 → 48 →
48.

### The device

A rule is written **once**, with the judgment family abstracted — `form : Fam → Prop`, where
`Fam` is the eight-member mutual family as a record of predicates. Instantiating that one
`form` twice gives both readings, and they cannot drift because there is only one of them:

| reading | type | who supplies it |
|---|---|---|
| syntactic | `form synFam` | the `Judge` constructor itself |
| semantic | `form semFam` | **a proof, and it is a field (`Clink.sem`)** |

This is `Denote/Sem/Obligations.lean`'s substitution reified: that file derived
`Obl.<Family>.<rule>` by replacing one constant with another inside the constructor's type;
`Denote/Clink/Derive.lean` replaces it with a *projection of a parameter*, which is the same
operation made first-class. `register_clink Judge.vasgn` reads the constructor, derives
`form`, demands `Sem.Judge.vasgn`, and declares the clink — so `syn` and `sem` are each
kernel-checked against a statement neither of them chose.

The judgment is then **generated from the registry**, impredicatively (Böhm–Berarducci, in
`Prop`):

```lean
JudgeC R |>.judge κ Γ I e τ κ' Γ' I' := ∀ F : Fam, Closed R F → F.judge κ Γ I e τ κ' Γ' I'
```

### What that buys, and each of these is a file you can read

* **`registry_sound` is unconditional and one line** — instantiate `F := semFam`, discharge
  closure from the clinks' own `sem` fields. It holds at every registry size and held at size
  1. There is no 83/83, no `AdequacyHyps`, no terminal clink. (`Denote/Clink/Spec.lean` §3,
  `Registry.lean` §2, axiom-clean.)
* **An unregistered rule is not in the judgment** — not an undischarged obligation, not a rung
  owed. So the §F19 failure mode is gone rather than reported better: a rule whose obligation
  is *false* has no proof, hence no clink, hence never enters `JudgeC`.
* **A derivation is a term, polymorphic in `F`** — you use the rules you are handed (`hF c hc`),
  so a derivation *is* a witness that only registered rules were used. No closure lemma and no
  monotonicity is needed, and there could not be a generic one: a Horn rule mentions the
  judgment contravariantly in its premises. Worked examples, one line each, in
  `Denote/Clink/Controls.lean` §1, which also runs `registry_sound` on one to get `SemJudge`
  out.
* **Growth is gated by `lake build`.** `register_clink` refuses a rule with no proof
  (`Controls.lean` §2 captures the refusal with `#guard_msgs`, so the gate going quiet is a
  build failure); the 35 legacy unclinked constructors are frozen **by name** in
  `Registry.lean`'s `legacyUnclinked`, and a `#guard` fails if anything not on that list is
  unregistered. A rule added from now on therefore *must* arrive with its semantic proof. The
  list only ever shrinks, and proving a legacy rule needs no edit to it.
* **The ratchet is now sound to ratchet on.** `SemLadder.lean`'s `clinkFloor` (48) is a floor
  on *proofs*, and the exit code is non-zero only if the registry **shrank** — not "while
  rules remain", which under the old framing was a permanent red light.
* **Restating the semantic reading is a new registry, not a rewrite.** `Clink` is
  parameterised by both families (`Clink (S T : Fam)`), so the answer-typed migration
  (`answer-typed-schema.md` §3.1, `SemJudge` → `SemJudgeA`) changes the *target* and leaves the
  mechanism alone — and it makes the cost per-rule and honest: a clink whose `sem` field does
  not carry over stops building, by name, instead of a report continuing to say "48
  discharged" about a superseded statement.

### The number, and what it is not a fraction of

```
$ lake exe semladder
  Judge          32   registered   35 not in the judgment
  ...
  total          48   registered   35 not in the judgment
CLINK RATCHET OK (48 registered, all proved by construction; 35 rules not in the judgment
                  -- that is coverage, not debt)
```

The right column is **coverage**: what `JudgeC` cannot type. It matters because
`Ratchet/Validate.lean` and `Ratchet/Deriv.lean` still target `Judge`, so it bounds what can
be certified *soundly* — and that, not a fraction, is the thing to reduce.
`Denote/Adequacy.lean` now says exactly what targeting `Judge` assumes
(`semJudge_of_judge_of_adequate`), which is how the assumption became visible.

### Layout

```
Denote/Clink/Spec.lean      Fam, synFam/semFam, RuleF, Clink, Closed, JudgeC, the 10
                            unconditional soundness/admissibility theorems
Denote/Clink/Derive.lean    register_clink: the constructor -> form -> the clink, and the
                            refusal when there is no proof
Denote/Clink/Registry.lean  build_clink_registry, `clinks`, registry_sound/_syn, the report,
                            the growth gate + legacyUnclinked
Denote/Clink/Controls.lean  worked derivations, the captured refusal, the two `rfl`s that
                            pin what the field types are, the positive control
```

**Deleted, and what replaced it:** `Denote/Ladder.lean` (the 48/83 report and its `isDefEq`
check — the check is now `Clink.sem`'s type, enforced at declaration instead of counted in a
report) and `Denote/Adequacy.lean`'s `AdequacyHyps`/`StuckFreeTarget` (the 83-conjunction and
the parallel stuck-freedom statement — the conjunction is `Closed clinks semFam`, proved in
one line for any registry).

## Semantic ratchet status (`Denote/Sem/`): **historical — the 48/83 framing was replaced by the clink registry, see above**

> **SUPERSEDED, 2026-09-11 — read §The clink registry above first.** Everything below is the
> record of the 48/83 ladder: its evidence is still good (the 48 proofs are the `sem` fields
> of the 48 clinks, and the stall points, measurements and refutations are all still on file),
> but its *framing* — a numerator of proofs over a denominator of rules authored, with the gap
> as debt — is gone, and the three sessions that ended in the EMERGENCY EXIT below are why.
> Do not plan against a number in this section.
>
> **ALSO BEING RESHAPED, 2026-09-11.** The two-ladder framing this section describes is being
> replaced by a single **answer-typed** judgment plus an inductive invariant, because
> `SemJudge` has no progress content at all and that is now proved, not argued
> (`Denote/Sem/NoProgress.lean`'s `not_semJudgeImpliesStuckFree`). The work order is
> **[`../docs/semantics/answer-typed-schema.md`](../docs/semantics/answer-typed-schema.md)** —
> seven layers, an explicit delete list, and a migration that says where the ladder gets
> *restated* rather than climbed. The diagnosis and the built decomposition layer are
> `../docs/semantics/answer-typed-judgments.md` §1–§5 and §10; the worked end-to-end
> prototype is `Denote/Proto/`. **Read the schema before touching anything under
> `Denote/Sem/`.**

> **EMERGENCY EXIT INVOKED (clink 64).** The ladder counts **one rule at a time**; 26 of the 35
> remaining rules come out **together**, at the end of a layer that is several sessions long, and
> 7 more are false as stated with repairs that cross into `Ratchet/`. Three consecutive sessions
> (clinks 62, 63, 64) delivered verified work — `BuiltinsSeal`, `enterUserMethod`, stages 2 and 4,
> `dispatchMiss`, two stall points closed, **a reachable soundness bug found and fixed (§F23)** —
> and the number moved 47 → 48 → 48 → 48. A ratchet insensitive to that is measuring the wrong
> unit. The recommended repair is a **ladder** change and not a proof change: count **conditional
> rungs** (`StepSound → Obl.Judge.if'` is a real, checkable theorem, and the layer hypothesis is
> already a named `Prop` in `Denote/Sem/StepWalk.lean`). Full statement and evidence:
> `implementation-notes.md` §EMERGENCY EXIT.

> **Clink 63 (2026-09-10) proved `enterUserMethod` — the layer's parked helper — and stage 2's
> block-iterator trio. The ladder is unmoved at 48/83, as expected: none of it is a `Judge`
> rule.** The recorded diagnosis (*hand-split the ~7 conditions*) was measured and **does not
> work**; `Denote/Sem/notes.md`'s **nineteenth stall point** is why. `Interp.enterUserMethod`
> threads the machine through nine `let`s and its activation push is a flat record literal whose
> nine fields are each a *projection* of the pre-push machine, so a goal-side peel leaves `?mid`
> under a projection and `generalize … at h` cannot name it either — every machine-producing
> subterm is guarded by a `match`, a hand-written `match` is a **fresh matcher constant**, and
> `generalize` then abstracts nothing and reports **no error**.
>
> The fix is a **mirror gated by `rfl`**: `Denote/Sem/StepAct.lean`'s `enterUM` is the same
> function with its five machine-touching stages named, `enterUM_eq` is `rfl` (so fidelity is a
> kernel check), and the walk then closes in **18 s** against three previous non-terminating
> attempts. Chosen over refactoring `Interp/Dispatch.lean` itself because that breaks
> `KontFrameDispatch`'s `enterUserMethod_frame`, which the climbed `Judge.vasgn` rung sits on.
> **The rule generalises** — `finishSend`, `invokeDispatch`, `startArgs`, `tryReflect` and
> `evalExpr` are let-chains of the same kind.
>
> Also landed: **`PreAct`** (`Step` plus the two heap facts a frame push reads — every installed
> method still installed, every Proc still there — with both folds and `destructureBind`), the
> **six `methodIn` bridges** (`lookup`/`methodOn`/`lookupAbove`/`superFound`/`userInit?`/
> `moduleHook`, one arm lemma between them), and `Step.missNoMethod`/`visError`/`iterStep`/
> `startIter`/`tryIterator`, plus **`tryMixin`** and **`defineAttr`** (on `CapMono.defineMethod`:
> installing a method can only *hide* a capture edge). **Stage 2 is complete except
> `enterClassBody`** (deprioritised — declaration family). The dispatch spine cannot close before
> **stage 4**, since `dispatchMiss` routes through `tryReflect`.
>
> **Stage 4 is complete** (`Denote/Sem/StepReflect.lean`): all fifteen `reflect*` helpers,
> **`tryReflect` and `dispatchMiss`** — *the miss path is closed*. `reflectVisibility` was the last
> and its measurement is the sharpest: hand-peeling its leaves left a **28 s timeout**, and
> `Step.visRun_eq` (the shape in a `rfl` hypothesis, clink 62's rule for the fifth time) closes the
> same walk in **2.3 s**.
>
> **And `invokeDispatch` is still blocked — the twentieth stall point.** `Builtins.run` answers
> four ways and three carry a machine, but the layer's 600-arm walks (`builtins_run_locals`,
> `builtins_run_cap`, `Step.builtins`, and the eighteenth stall point's `Sealed` result) are stated
> over **`.ok` alone**. A builtin that *raises* therefore leaves the locals layer with nothing to
> say, and every dispatcher's error path is unreachable. It is a second pass of the same two walks,
> not a design problem — `Denote/Sem/notes.md` prices three ways to pay for it — but it was
> **invisible**, because `Step.builtins` reads like "the layer is done". Two relation-level
> corrections came out of it, both found by the type checker: **`PreAct` is false across
> `defineMethod`** (which *replaces*, so the walks are `Step` and their second write **establishes**
> the new fact rather than transporting the old), and **`PayKeep`** — payloads preserved — is the
> right interface for `eigenclassOf`, which writes an `eigen` field and so is not heap-growth.
>
> Most of the session's costs were **closer shape, not semantics**, and the new one
> generalises: `refine`/`exact` refuse to postpone an implicit argument a later `rfl` would
> determine, so a lemma meant for a closer list states that pair as one existential and takes
> `⟨_, by assumption, by rfl⟩` — where the `by` on the `rfl` is load-bearing.

> **Unblocked 2026-09-08 (L266). The blocker was model fidelity, and it is fixed.**
> `Sealed`, the frame-graph invariant the locals layer is built on, was not inductive over
> `stepFn`: `Symbol#to_proc` allocated a closure with `captured := 0`, a capture edge into the
> toplevel. Probing against CRuby (`found-issues.md` §A6a) showed that edge does not exist in
> the reference — `:upcase.to_proc.binding` raises, `source_location` is `nil` — so the repair
> was in the *model*, not the invariant. `Closure.captured` is now an `Option` (matching
> `Frame.captured`, which always was one), the two `:sym.to_proc` sites take `none`, and
> `Sealed.clos`/`FramesWF.clos` are quantified over the captured id so a capture-free closure
> discharges them vacuously. `not_BuiltinsSeal` is **retired**; `toProcSealsB` `#guard`s the
> repair in its place.
>
> **L267 then closed the invariant and proved half the layer.** `Sealed.meth`/`FramesWF.meth`
> — the `MethodDef` arm, the third clause `enterUserMethod`'s push needs — are built, so
> `Sealed` is the closed three-clause invariant (stack, closures, methods) the enumeration
> predicted, with the control state *not* in it. And the `Builtins` layer's **frame half** is
> proved: `LocalsSame` grew `captured` and `frames.size`, the existing 600-arm walk carried
> them with no change, and `builtins_run_seal`/`builtins_run_framesWF` now leave a caller
> owing **only the heap clauses**. What remains of `BuiltinsSeal` is exactly "`Builtins.run`
> installs no capturing closure and no capturing method" — true, but a second traversal of the
> same six hundred arms, and it cannot ride the first (see `Denote/Sem/notes.md` §The
> `Builtins` layer, half proved).
>
> **The ladder did not move across any of this (47/83), and that is expected** — removing a
> refutation, closing an invariant and proving half a layer are not `Judge` rules. The census
> at §Where the remaining 36 rules sit still holds: all 36 are behind one of four unbuilt
> layers, none smaller than a clink. Read `HANDOFF.md` first.
>
> **L269 (clink 62) proved `BuiltinsSeal`, and with it the eighteenth stall point is closed.**
> `Denote/Sem/BuiltinsCap.lean`'s **`CapMono`** — the heap's capture edges did not grow — is the
> heap-side predicate; `Sealed.of_capMono`/`FramesWF.of_capMono` discharge
> `builtins_run_seal`'s two remaining hypotheses from it; and the walk itself is on file, one
> module per dispatcher, all six proved and axiom-clean in seconds each (19/48/3/7/5/5 s), with
> `BuiltinsCapRun.lean`'s **`builtinsSeal : BuiltinsSeal`** and `builtinsFramesWF` joining them to
> `FrameLocal.lean`'s frame half. **`Sealed` survives `Builtins.run`.** Next in the locals layer:
> `Sealed.push`/`pop`/`alloc_closure` at the *interpreter*'s frame pushes, `ClosuresOk`'s
> exactness, then the `stepFn` walk.
>
> Two definitional decisions, neither forced: `CapMono` is **existential in the object id**
> because `Object#dup` *refutes* the id-keyed form (it pushes a copy of the source's payload, so
> `p.dup` on a Proc puts the same edge at a fresh id), and `CapAt`'s class arm is keyed on the
> **`methodIn` lookup** rather than on membership in `cp.methods`, because the membership form is
> easier to establish and `Sealed.meth` cannot consume it — the sixth stall point's rule one layer
> down.
>
> **The transferable result is the tactic**, eight measurements in `Denote/Sem/notes.md` §The
> second walk. The two that matter most: *put the arm's shape in a `rfl`-provable hypothesis and
> leave the conclusion first-order*, which took the walk from "unfinished after 35 minutes" to
> 17 s per dispatcher because it is what makes **failing** cheap; and *a `simp` in a 600-arm walk
> is a search, not a step* — `simp at h` alone took `runNumerics` past 14 GB of proof term without
> terminating, and `dsimp only at h` in its place closes the same file in 5 s.
>
> **The ladder's ceiling under a no-`Ratchet/` constraint is 76 of 83, not 83** (clink 62's
> re-audit, `Denote/Sem/notes.md` §The remaining 35). **Seven obligations are false as stated,
> not unproved** — `defStmt` (confirmed by construction: the obligation is premise-free, and
> `DefsOk` at the incoming `κ` demands the body `defineMethod` just replaced), `arrayLit`/
> `hashLit` (the seventh stall point's remnant, witness `corpus/242`), `casgn`/`cpathAsgn`
> (the seventeenth stall point *and* §F22), and `if'`/`ifNoElse` (the eleventh). None of the
> seven is an *unsoundness*, so the standing "fix a genuinely unsound rule" exception does not
> reach them; each repair is a `Judge` premise, a cref in `Ctx`, or a move to `joinT`. They are
> a precondition on the target, not a stall in the work.
>
> **The ladder still reads 48/83, and clink 62 does not claim otherwise.** It also filed
> `found-issues.md` **§F22** — `constAsgnOk`'s guard list is not the set of class names a `Ty` can
> carry, and `Regexp` is outside it, which is a *third* independent reason `Judge.casgn`'s
> obligation is false (not reachable; §F10's pattern read from the assignment side).

**A second ladder, parallel to the first, measuring the other thing.** `run_ratchet.sh`
measures *reach*: how many corpus programs `validate` types (177 of 249). This measures
*justification*: how many of `Ratchet/Judge.lean`'s **rules** have been discharged as a proof
obligation over the semantic denotation, proved from the real `stepFn`. A program can climb
the first ladder with none of the second done — which is exactly the gap `Denote/notes.md` was
written to describe, and this is the answer to it.

Run it with **`scripts/run_denote.sh`** (or `lake exe semladder` for just the number).
Discharged so far, all axiom-clean:

* **The nine leaf reads.** The seven literals (`intLit`, `fltLit`, `strLit`, `symLit`,
  `truLit`, `flsLit`, `nilLit`) plus both local reads (`var`, `varAlias` — the first rungs
  that *consume* a `StateOk` component rather than only re-establishing one).
* **Two more one-step reads** (clink 48, `Denote/Rules/Read.lean`): **`selfExpr`**, which
  spends `SelfTyOk` and nothing else, and **`ivarRead`**, which is why `SelfSpineOk` now says
  the spine is **complete** (an ivar it does not mention reads as `nil`) — the invariant the
  rule's own docstring named, and without which its `.nilT` default is false of the semantics.
* **The second allocating literal**, `regexpLit` (clink 48, `Denote/Rules/Regexp.lean`):
  `strLit`'s shape plus a *gated* arm — a pattern `Rx.parse` rejects steps to `.unsupported`,
  which is not a `.value`, so the obligation's hypothesis is unsatisfiable and the case costs
  nothing (`evals_of_unsupported`). It grew `CoreOk` by the `Regexp` row that structure's
  docstring predicted.
* **All four `.const` rules** (clink 50, `Denote/Rules/Const.lean`): `constCls`,
  `constBuiltin`, `constExc` and `constEnv` — the whole family whose expression head is
  `Expr.const n`. Leaf rungs, so the content is which component says the value is in the type,
  and they cost two definitional corrections. **`ConstScopeOk`** is the new component: `denM
  (.clsOf n)` resolves a name through the *toplevel* table while the machine runs CRuby's
  two-phase lexical rule, and nothing made those the same value. **`ConstsOk` was restated
  over `constGet?`** rather than over `Ctx.consts`' entries — the sixth stall point's own
  recommendation, arriving at the first component that could be shown to need it (the old form
  was *unsatisfiable* at any context with a nested constant). `CoreOk` grew `coreNamed`, an
  implication rather than an existence claim, because the model has no `IOError`.
* **`seq`**, a delegation that is definitional (`SemJudgeSeq` *is* `SemJudge` at a `.seq`), and
  **`JudgeSeq.last`** (clink 48) — the singleton sequence, which `evalExpr` runs by rewriting
  `ctl` and pushing **no** continuation, so it is one step away from its statement's own run
  and does *not* need the wall below.
* **`Judge.vasgn`** (clink 54, `Denote/Rules/Vasgn.lean`) — the **first compound rung**, and
  the one the fifth stall point was measured on. It is short, because everything hard is
  elsewhere: `RubyCore.Proof.stepFn_frame` (the interpreter's frame rule, over the whole of
  `stepFn`, axiom-clean) and `Denote/Sem/Decompose.lean`'s **`run_split`** (a run under an
  appended continuation splits at the state that delivers the inner run's value to it). The
  attempt also produced `found-issues.md` **§F5** — `Judge.vasgn` recorded the right-hand
  side's type verbatim, and an *alias* type recorded that way claims something about a second
  local that the premise does not carry.
* **`Judge.callNever` and `Judge.primNever`** (clink 54, `Denote/Rules/Never.lean`) — the first
  two of the **call family**, on `Denote/Sem/Send.lean`'s **`run_args`** (the argument walk:
  `run_split` at each `.argsK`). Both conclude `Ty.never`, the empty type, so both are
  discharged by contradicting the run. Opening them needed `SemJudge` to carry **`Plain`** —
  the fact that a `.splat`/`.kwargs`/`.fwd` is argument-list syntax and not an expression,
  which the *syntactic* `JudgeAll` implies structurally and the semantic one did not, and
  without which every call rule's obligation is false.
* **`Judge.constPath` and `Judge.constPathCls`** (clink 54, `Denote/Rules/Path.lean`) — `A::B`
  in both its forms, on two new `StateOk` components: **`ConstPathsOk`** (`ConstsOk` is about *lexical* resolution; this one is about the
  keyed entry `constKeyIn owner n` against what the interpreter finds inside the class named
  `owner`) and **`NestedClassesOk`** (`ClassesOk` resolves a nested class through the *toplevel*
  lookup at its full path; this is the other direction — that looking `B` up inside `A` finds
  it). Their three outcomes are the shape every dispatch-like rung will have: the hit is typed,
  the gate is `.unsupported`, and the miss is a `raiseErr` — a jump at an empty continuation,
  which never returns a value.
* **The three dispatch rungs** (clink 55, `Denote/Rules/Query.lean`, `CaseEq.lean`,
  `ClsToS.lean`) — `Judge.isAQuery` (`recv.is_a?(C)`), `Judge.caseEqQuery` (`C === v`, what
  `case v when C` desugars to) and `Judge.clsToS` (`C.to_s`): the first rules whose runs go all
  the way through a **dispatch** — receiver, arguments, lookup, builtin. What made them
  tractable is that none of the three has to know *which* value the builtin computes, only its
  shape (a `Bool`, a `Bool`, a `String`), so no signature table is involved; `Judge.prim` is
  where that stops being true. Their heap facts are **`QueryOk`** (indexed by the receiver's
  class) and **`ClsQueryOk`** (indexed by the receiver *object*, because `classOf` of a class
  object is its eigenclass) — each row measured at the booted machine before being written
  down, and each conditional on the context declaring no method of that name, which is the
  shape both of this clink's soundness findings took.
  **`SemJudge`'s first conjunct is now `Framed m m'`**, and that is the structural result of
  the clink: `m'.stack = m.stack` plus **"once a class, always a class"**. A send evaluates its
  receiver *before* its arguments, so a rule with a `.clsOf` receiver premise establishes the
  receiver's class-ness at one machine and reads it at another, with an arbitrary evaluation in
  between — a transport no `StateOk` component can supply, because `StateOk` describes one
  machine. Proving it over `stepFn` instead was rejected on price (it would have to hold for
  every bid in `Builtins`, including the ones no rung reaches) and the conjunct is discharged
  per-rule and composes by `Framed.trans`, exactly as frame balance already did.
  Both rules were **unsound as written** — `found-issues.md` **§F7**: their
  `smroGet? κ.classes n mname = none` guards ask about singleton methods on `n` itself while
  the dispatch walks `n`'s *eigenclass chain*, so an inherited `def self.===` or a reopened
  `Module` gets past them (corpus 243). Fixed the §F6 way, with `nameFree` premises.
  **§F8** is filed and not fixed: `Judge.classOf`'s conclusion (`.clsOf n`, the *exact* class)
  is stronger than its receiver premise (`.inst n I`, an *is-a* test that a subclass instance
  passes), so it is false of the denotation read on its own — and probably true of every
  derivable judgment, `Judge` having no subsumption rule.
* **`Judge.classOf`** (clink 56, `Denote/Rules/ClassOf.lean`) — `x.class`, and the rung that
  was **false** until the denotation was fixed. `denM (.inst n I)` was `isAName` — *is-a* — so a
  declared subclass's instance satisfied `.inst "C"` while the conclusion `.clsOf "C"` is the
  exact class object (`found-issues.md` §F8). The fix is §F12 and it is a change to the
  **denotation**: `.inst` now means `isExactInst`, "a live object whose `realClassOf` is the
  class the name resolves to", which is what the judgment always meant (it produces an `.inst n`
  only by allocating exactly `n` or from a `self` whose class `κ.frame.recvClass` names exactly,
  and `joinT` of two `.inst`s is a union rather than an upcast). `Ty.cls` **keeps** the is-a
  reading, because `rescueBind?` needs it — the two nominal arms now say different things
  deliberately. It cost four sites and moved nothing else: all 41 rungs, the 33 `#guard`s, the
  177 derivations and the 145 controls were unaffected. It also removes the central obstacle to
  the whole dispatch family, every member of which types a callee's body out of the receiver
  type's own table.
* **Three reachable soundness bugs, found by sizing obligations** (clink 56) — the first
  programs on this ladder that `validate` **accepted** and CRuby raises `TypeError` on. All
  three came out of writing down what `isAAnswer`'s answers would have to assume:
  **§F9** (`class Integer; include M; end` makes `5.is_a?(M)` true, while the answer came from
  a static table — and `isATy` turns a negative answer into `Ty.never`, so a wrong one certifies
  *anything* in the branch), **§F10** (`Foo = Integer`: narrowing read the constant's **name**,
  and a constant is not its name), and **§F11** (`rescue StandardError => e` binds a *subclass*
  instance — the one place the judgment uses subsumption — and `PrimSig`'s `excMessage` row
  dispatched on the supertype). Fixed by `mixinFreeChain`, `narrowNameOk` and
  `primDispatchOk` respectively, all precision-preserving on the corpus (mismatches stayed at
  35). `Ratchet/Ty.lean`'s `falsyTy`/`isNilTy` were corrected in the same pass, in the same
  direction: **a `.never` catch-all is a claim, not a default**.
* **`Judge.newInstNoInit`** (clink 57, `Denote/Rules/NewInst.lean`) — `C.new` for a class with
  no `initialize`, and the first rung that allocates through a class the *program* declared. Its
  dispatch fact cannot be a `ClsQueryOk` row (16 of the 87 boot class objects do not resolve
  `new` to `Class#new`), so it is keyed on the context's own table: **`DeclClassOk`**, vacuous
  at `ctx0` like `ClassesOk`/`DefsOk`, with a clause for each thing `Class#new` reads. The rule
  was **missing the allocator's premise** — a declared `def self.new` wins over `Class#new`, and
  `validate` enforced that only by consulting `smroGet?` first — which is the fourth premise
  this pair of clinks has found the checker supplying by accident of control flow.
* **Narrowing's type-level half, complete** (clinks 56–57, `Denote/Sem/Narrow.lean`) — all six
  of the twelfth stall point's lemmas, axiom-clean. `isATy`/`notATy` are where the file stops
  being about `Ty` alone, and finishing them forced three more guards, each of them a way a
  static answer could be wrong: `coreConstFree` (§F10 for the names the *chain* is written in),
  gating `isAAnswer`'s **positive** answer as well (the alternative is proving transitivity of
  the ancestor walk, which a `StateOk` component has no business assuming), and a third
  conjunct on `isExactInst` — **no eigenclass**, because `obj.extend M` makes `obj.is_a?(M)`
  true while `M` is in no declared chain. `builtinAncestors` also lost its `.arrayOf`/`.hashOf`
  rows: those `denM` arms read the payload and say nothing about the class, so a *negative*
  `is_a?` answer about them is a claim the judgment cannot make.
* **`Judge.raiseCls`** (clink 58, `Denote/Rules/Raise.lean`) — `raise C`, and a rung that was
  **mis-filed**: it concludes `Ty.never`, so it belongs to the `callNever` family (discharge by
  contradicting the run), not to the frame-push wall. The `raiseNewK` interception is what made
  it look otherwise — `raise C` with a user `initialize` allocates, pushes `.raiseNewK` and
  enters the method, so a value *does* come back from an arbitrary body — but `applyKont` at
  `.raiseNewK` turns any value into a raise, so the kont is **value-opaque** and `run_split`
  covers the activation without looking at the body. Two reusable pieces:
  `pushK_of_kont_append` (a machine whose continuation *ends* with `Kout` is a `pushK`, read off
  the continuation rather than transcribed) and the observation that
  `RubyCore.Proof.enterUserMethod_frame` is an **equation**, so the activation needs no shape
  lemma at all.
* **`JudgeSeq.guard` and `JudgeSeq.nextGuard`** (clink 58, `Denote/Rules/NarrowInv.lean`) — the
  two guard clauses (`return e if c`, `next if c`), and the **first narrowing rungs**. All of
  narrowing soundness is built for them: three run inversions over two shared send skeletons,
  the two state transports (`EnvOk_refineOne_else` pointwise, so `refineOne`'s alias arm is
  free; `SelfSpineOk_ivarSet`), `narrow_else_fact` (the branch's fact for every shape in one
  conclusion), and `stateOk_narrow_else`. What lands is the *guards* and not `if'`/`ifNoElse`,
  for a reason that is a design fact about guard clauses: a guard's then-branch **escapes**
  (`.nxt` emits a `nxtJ` no `ifK`/`seqK` consumes; `doReturn` answers a jump whatever happens),
  so the run never returns a value there, the then-premise is never spent, and only the *else*
  component of `narrowEnvs` is read — where the `&&` shape refines nothing.
  Three more findings came out of it, and with §F10 they are **one pattern stated five ways**: a
  narrowing reads *syntax*, so every fact it relies on about what that syntax means has to be a
  premise. **§F14** (reachable, accepted: `class NilClass; def nil?; false; end` sends a `nil`
  down the else branch where `nonNilTy .nilT` is `never`) — the tested name must be unclaimed;
  **§F16** — it must *name a class*, because `C === x` puts it in the receiver and `String#===`
  is equality; **§F15** — and the refinement must not *manufacture* a `Ty.sameAs`, which
  `joinT` can, recording an alias claim the environment never made. `narrowNameOk` is six
  conjuncts now, each one a program that used to be certified.
* **`found-issues.md` §F18** (clink 59) — a *reachable* soundness bug found while sizing
  `Judge.casgn`, which is the rule with **no premise at all**: `extendConsts` records a
  constant's type from a **top-level `casgn` statement**, so an assignment buried inside a
  larger expression rebinds the constant while `κ.consts` still carries the old type.
  `X = 1; y = (X = "s"); X + 1` was certified `Integer` against a `TypeError`, and
  `y = (String = 5); String.new` is the same hole through `constBuiltin`'s
  `constGet? κ n = none` premise instead of `constEnv`'s lookup. Fixed by `constAsgnOk`, and
  the shape is §F17's: **agreement, not absence** — the first assignment of a name resolves
  nowhere yet, so absence is what the common case has. Corpus-neutral.
* **`Judge.ivarAsgn`** (clink 59, `Denote/Rules/IvarAsgn.lean`) — `@x = e`, and the rung that
  brings **mutation** into the ladder. Every transport before it was `Ext` (allocation) or
  `setLocal` (a rebinding); a write to an object's `ivars` is neither, and `Ext` is *false* of
  it. `Denote/Sem/Mut.lean` is the third relation: frames, stack, globals, heap size and every
  shape field (`klass`/`eigen`/`payload`/`frozen`) pinned, `ivars` free. It is a separate
  relation rather than a widening of `Ext` because `Ext` grows the heap and `Mut` does not, so
  the nine shape-only `StateOk` components each get a `.mut` twin beside their `.ext` one.
  The transport's shape is worth recording: `denM_ivarWrite`'s hypothesis is stated at the
  machine **before** the write, because stating it after is circular — and the induction closes
  the gap, since at the moved spine entry the type owed is a *strict subterm* of the type being
  inducted on. Read the other way, that is why the guard `ivarAgree x τ τ` is not vacuous: a
  `Ty` cannot contain itself. The step's other two arms (`self` frozen, `self` an immediate)
  raise `FrozenError` and so produce no value, discharged by having no case.
  **§F17** is the finding, and it is **reachable** (`validate` accepted it): the rule moved the
  `self` spine's `@x` entry and said nothing about the other five places a type can mention
  `@x` — `κ.selfTy` mentions every ivar the class has, so `@o : C[@x : Integer]` with `@o`
  holding `self` is falsified by `@x = "s"`. `ivarAsgnOk` checks **agreement**, not absence:
  absence rejects every in-method assignment, and agreement at `I'`'s *own* `@x` entry rejects
  type-changing reassignment. Arrows are exempt because they are `Later`-quantified and the
  write is a `Later`; `Ty.clos` is not, which is §F1's split one component over.
* **`found-issues.md` §F19 — four reachable soundness bugs, one function** (clink 60; corpus
  rungs **251–254**). `bodyResult` rewrites a body that is exactly `return e` to `e`, so a call
  to it is typed as `e`'s type. That is right for a **lambda**, whose `return` is local to it
  (rung 105, `lambda-explicit-return`), and wrong for a **proc** or a **block**, whose `return`
  returns from the *enclosing method* — the call never comes back, and the method's recorded
  return type is a lie a caller then spends. Its docstring said the rewriting was "applied only
  at `closCall`, because only a lambda rung asks"; by the time it was read it sat at four rules,
  and `closCall` cannot tell a lambda from a proc. All four doors were reachable and certified
  `Integer` against a `TypeError` under CRuby *and* the model: `proc { return e }.call`
  (`closCall`), `arr.map { |y| return e }` (`iterBlock`), `m { return e }` + `yield`
  (`yieldExpr`), and `arr.map(&p)` at a proc (`iterClosPass`). Fixed by **`procRetOk`**, one
  premise on `Judge.lambdaLit` — the only rule that turns a block literal into a callable
  `Ty.clos` and the only one that can see whether the head was `lambda` or `proc` — so a
  `proc { return e }` gets **no type** at all; `iterBlock`/`yieldExpr` lose the rewriting
  outright (a block literal is never a lambda) and `iterClosPass` needs no change, since with
  `procRetOk` in place a `&`-passed closure with a `.ret` body can only be a lambda, where it is
  sound. Corpus-neutral: mismatches stayed at **35**. Found by the *census* rather than by
  search — sizing the fourteenth stall point's jump-freeness conjunct means asking which rules
  could discharge it, and `lambdaLit` is the one that cannot. **The pattern is new**, and it is
  not §F17/§F18's: *a syntactic shortcut is scoped to the rule that justified it, and copying it
  to a second rule re-opens the justification.*
* **The seal is not inductive, and one builtin is why** (clink 60,
  `Denote/Sem/StepLocal.lean`'s `not_BuiltinsSeal`; `Denote/Sem/notes.md`'s **eighteenth stall
  point**). Item (1)'s locals half is built up to `Sealed`/`FramesWF`/`StepInv` and the
  `Builtins` layer is uniform for `LocalsSame` — so carrying the **seal** across `Builtins.run`
  looked like the free step before the interpreter walk. It is **false**: `Symbol#to_proc`
  allocates a `Closure` with `captured := 0` (the toplevel frame — `Closure.captured` is a
  `FrameId`, so there is no way to spell "captures nothing"), which is exactly the field
  `Sealed.clos` reads, and `b = 0` is the frame every toplevel narrowing rung is about. Not a
  model bug: that closure's body is `__recv.s(*__rest)`, assignment-free, so `Sealed` is
  strictly stronger than the truth here — and not repairable at `Sealed.alloc`, since the
  allocation happens at a machine the seal really holds at. Admitting an inertness escape in
  `clos` is the easy half and insufficient, because `callClosure` then pushes a **block frame**
  whose `captured` is that closure's and the unconditional `stack` clause breaks. So the
  invariant has to be **joint over the frame graph and the control state**, which is the
  fifteenth stall point's own prediction arriving with a number on it; `ClosuresOk`'s exactness
  also needs a third escape the plan did not name — a closure a *builtin* created, from source
  that is in neither the program nor the prelude (grep: this is the only one). Working lesson,
  the second time it has paid: **write the layer's target down as a named `Prop` before proving
  the layer under it.**
* **The 36 remaining rules, re-audited** (clink 60, `Denote/Sem/notes.md` §Where the remaining
  36 rules sit) — **none of them is one rung's work.** Each is behind one of the two items
  above, `Judge.prim`'s ~200 `PrimSig` rows, or a stated falsity (`arrayLit`/`hashLit`). Two
  corrections the audit forced: **`JudgeSeq.cons` belongs to item (2)** (its second premise is
  at `κ.afterStmt e σ` while its own hypothesis is at `κ` — the sixth stall point read from the
  consumer's end), and **`Judge.if'` is not the cheapest remaining rung** despite `semladder`
  listing it first. All six narrowing type-lemmas are proved and
  `stateOk_narrow_then`/`stateOk_narrow_else` are assembled, but `if'` is blocked *twice*: by
  the `&&` sandwich's `thenOnly` refinement (item 1) and by the **eleventh stall point**, where
  `joinEnv` synthesizes an alias nobody promised and the obligation is false as written — whose
  two recorded repairs each re-open something already climbed (`Judge.vasgn`'s §F5 premise) or
  move `joinT`'s output types and therefore the syntactic ratchet.
* **The remaining ladder is two items, not five** (clink 58; re-audited clink 59, and
  `casgn`/`cpathAsgn` moved *into* item (2) — see `Denote/Sem/notes.md`'s seventeenth stall
  point: `Judge.casgn` has no premise and no context growth, but `applyKont`'s `.casgnK` writes
  into `currentFrame.defmod`'s own table, and `ConstScopeOk` compares resolution against
  `Object`'s table alone, so a class body's first constant makes the *conclusion*'s `StateOk`
  false. The component is on both sides of the implication, so the fix is a weakening, and
  every obvious weakening breaks the three `.const` rungs that consume it — which is the
  eighth stall point again). The fifteenth stall point's two
  halves are **entangled with the call decomposition**: the locals claim wants to be an
  induction on the expression, but `noLocalAsgn` must admit `.send`, which may dispatch a user
  method — so it needs "a callee's run leaves the caller's frame's locals alone", the same
  activation-level statement the call family needs and the one that needs jump-freeness to
  state. So: **(1) one layer** — `frameK`-decomposition + jump-freeness + the two syntactic
  invariants, built together, gating `if'`/`ifNoElse`, the ~21 call rules, `while'`, `begin'`
  and (through their argument transport) `arrayLit`/`hashLit`, with no useful smaller first
  step; **(2) one judgment redesign** — the declaration family, because `StateOk` is
  **anti-monotone in `κ`** (`MethodsExact`/`NameFreeOk` are upper bounds), so a rule that grows
  the context cannot have its obligation stated at the old one and `Judge`'s conclusion has no
  outgoing context. `Judge.prim`'s ~200 `PrimSig` rows and `AsmsOk`'s frame-shape mismatch sit
  outside both.
* **Superseded** (clink 57's framing of the same wall): the **fifteenth stall
  point, syntax-directed run invariants** (`Denote/Sem/notes.md`). `Judge.if'`/`ifNoElse` need
  "a `noLocalAsgn` expression's run leaves the frame's locals alone" (`found-issues.md` §F13 —
  `noLocalAsgn` is syntactic and `f.call` on a closure that assigns is the gap); every call rule
  needs "a `Judge`-derivable expression contains no `.ret`, so its run emits no return jump"
  (the fourteenth stall point). Both are a property of the **run** derived from a property of
  the **syntax**, both want one induction over `stepFn` carrying a syntactic predicate through
  the machine, and together they gate ~17 of the 40 undischarged rules. The rest sit behind the
  judgment redesign the declaration family needs.
* **`JudgeRescues.cons`** (clink 48), the one `cons` rule in the family that the wall does not
  block: `JudgeRescues` threads no outgoing state, so its premise is about the same run its
  conclusion is. It is the first consumer of **`Denote/Join.lean`** — "a join is an upper
  bound" (`denM_joinT_left`/`_right`), which `if'`, `ifNoElse`, `arrayLit`, `hashLit` and
  `while'` will all need, and which carries the `LawfulBEq Ty` instance `Ratchet/Ty.lean`'s
  `deriving` clause does not provide.
* **The six companion base cases** — `JudgeAll`/`JudgeKw`/`JudgePairs`/`JudgeRescues`/
  `JudgeConsts`/`JudgeNested` at the empty list (`Denote/Rules/Nil.lean`; each is first in its
  *own* family's constructor order, four of the six are vacuous, and the file says so) — and
  **both class-body `cons` rules** (`JudgeConsts.cons`, `JudgeNested.cons`, clink 48), which
  are list bookkeeping plus `classMethods?`'s injectivity. Three of the seven companion
  families (`JudgeRescues`, `JudgeConsts`, `JudgeNested`) are now **complete**.

**The three companion `cons` rules, and the seventh stall point resolved** (clink 53,
[`Denote/Rules/Args.lean`](Denote/Rules/Args.lean)) — `JudgeAll.cons`, `JudgeKw.pair` and
`JudgePairs.cons`, which completes **six of the eight families**. Two definitional
corrections paid for them, both anticipated by the stall point: `SemJudgeAll` used to claim
every argument's type at the machine the *whole list* left behind, which would have needed a
transport across the evaluation of every later argument (none exists — `denM_ext` wants a heap
that only grew, and evaluating an arbitrary expression can mutate an object), so `DenAllAt`
states each element's type at *its own* post-machine and the transport moves to the consumer,
where `PrimSig`'s no-mutator property becomes an explicit obligation rather than an invisible
dependency; and `SemJudgePairs` now **interleaves** (key, value, key, value — Ruby's order and
`evalExpr`'s), where the old concatenated reading was an evaluation the machine never performs.

**And the filing was wrong about the wall**, in the direction that costs rungs: these three
were also thought to be behind the fifth stall point, and they never were. `EvalsAll`'s `cons`
arm is `∃ m₁, Evals m e v m₁ ∧ EvalsAll m₁ es vs m'` — each element's run is under an *empty*
continuation, so the hypothesis is already the premises' hypotheses. The companion families are
compositional by definition; the wall belongs to their **consumers**. Same mistake, same
direction, as the one clink 48 corrected for `JudgeSeq.last`.

**The two rules that reason from *absence*, climbed** (clink 52,
[`Denote/Rules/Bare.lean`](Denote/Rules/Bare.lean),
[`Denote/Rules/Lambda.lean`](Denote/Rules/Lambda.lean)) — the ninth stall point's own two
rules, and the first rungs whose proofs walk **forward** through dispatch
(`startArgs`/`finishSend`/`invoke`/`dispatchMiss`) rather than inverting a two-step run.
`Judge.bareName`'s whole content is that the run **does not return**: a bare `x` raises
`NameError`, so its `.any` and its unchanged outgoing `Γ`/`I` are vacuous, and the obligation
is that `Evals` is unsatisfiable (`Doomed`/`evals_doomed` are the inversion a non-returning
rung uses in place of `evals_pure`). `Judge.lambdaLit` is the ladder's first **higher-order**
conclusion — a `.clos` recording what the Proc captured — and a third allocating rule
(`CoreOk` grew `procBasic`).

Each needed one more piece of "and nothing more" than clink 51 supplied, and **each piece was
named by an interpreter test rather than guessed**: `BareNameFree` (`lookup` answers *nothing*
— `NameFreeOk` admits `builtin.isSome`, and a builtin named `x` would enter `Builtins.run`),
`MissFree` (no *user* `method_missing`, because `dispatchMiss`'s last question before raising
is exactly that, and it tests `builtin.isNone` with no `undefined` escape — so the component
does not invent a check the machine does not perform), and `FrameInRange` gaining the
conjunct its docstring always claimed (the frame stack is **non-empty**: `closSelf` reads the
captured frame by *id* while `SelfTyOk` reads `currentFrame`, which is `default` at `[]`).
`MissFree`'s absence was a **wrong answer**, not a gap — `found-issues.md` §F4, fixed in the
rule by a `nameFree κ "method_missing"` premise.

**The captured spine is a lookup** (clink 52, the tenth stall point). `denSpine` walked every
`ivarCons` entry while every consumer (`ivarGet?`, `envGet?`) reads the **first** match, and
`Judge.closCall` types a lambda's body in `paramEnv … ++ spineToEnv cap` — so a parameter
shadowing a captured local is a duplicate key **by design** and `validate` really does answer
`<closure#1>{x: String, x: Integer}`. `Obl.Judge.lambdaLit` was therefore false, and `EnvOk`
at any binding of such a closure was *unsatisfiable* — vacuity, the failure mode
`Denote/Sanity.lean` exists to police, and the third time a component keyed differently from
its lookup has produced it. `denSpineFrom` carries the keys already bound and skips a shadowed
entry; two new `Examples.lean` guards pin it against the real semantics.

**The frame lemma** (clink 51, [`Denote/Sem/Frame.lean`](Denote/Sem/Frame.lean)) — *`StateOk`
describes the whole state of the world, and nothing more*, which is two claims and they are
worth keeping apart. The **conformance** frame rule (`frameOnly`/`StateOk_frame`: `ctl` and
`kont` are the whole frame, and a change confined to it cannot disturb the description) was
already proved and is now named. The **exactness** half is new and is what three stalled rungs
were asking for: every component was a *lower* bound, so a rule reasoning from **absence** had
no hypothesis that could reach its conclusion. `MethodsExact` is the general upper bound —
every method installed anywhere is an axiomatized builtin, a prelude definition, or a name
`κ` records — measured **zero** exceptions at the booted heap before it was stated;
`NameFreeOk` sharpens it where a rule needs *absence* rather than non-authorship, localised to
the receiver's chain because the heap-global form is false (the prelude defines `T.proc`, a
singleton method off every ordinary chain); and `SelfLive` closes the gap both need — nothing
had said `self` is a real object, and `Heap.get` is total. `StateOk` is now **twenty**
components and `Denote/Sanity.lean` still exhibits a model of all of them, so the upper bound
cost no vacuity. The **interpreter's** frame rule (`KontFrame`/`EvalsDecompose`) is *stated, not
proved* — and in clink 52 it was **refuted**: `not_KontFrame` exhibits the machine, because
`stepFn` has one reader of the continuation below the head (`throw` scans the whole stack for a
matching `catch` tag) and the fifth stall point's measurement had checked only the *writers*.
Both statements need `CatchFree K`, which every use site the ladder has supplies for free
(the konts a rule pushes are literals); `KontFrameCatchFree` is the corrected target. The
decomposition needs the same hypothesis for a sharper reason — a sub-run can return under the
empty continuation and *not* under `K` (`catch(:t) { x = begin; throw :t; rescue
UncaughtThrowError; 1; end; … }`). Nothing here assumes either version.

**Its `Builtins` half is proved, and `Interp/Support` and most of `Interp/Dispatch` with it**
(clinks 52–53, `../lean/RubyCore/Proof/KontFrame.lean` + `KontFrameDispatch.lean` — the first
files this investigation adds outside `ratchet/`, because a theorem about `stepFn` belongs next
to `stepFn`). That was the part the fifth stall point could not size: `grep` finds **zero**
reads of `kont` in the whole 24k-line `Builtins/` directory, so the layer is transparent by
construction, and **119 axiom-clean theorems** now cover it end to end — every leaf, both fuel
walks, the `$~` write, the allocating folds, all six dispatchers and `Builtins.run` itself —
plus all of `Interp/Support.lean` (`callClosure`, the first frame-pusher, included) and most of
`Interp/Dispatch.lean`. **`destructureBind` is no longer a `partial def`**: the one item on the
path that was blocked *in principle* (an opaque constant has no equation lemmas) now has a
fuel-bounded recursion, verified by the difftest suite at **1304 tier-0 cases, 0
disagreements**, and its framing lemma is proved.

What is left of the wall: `Interp/Reflect.lean`, `Send.lean`, `Kont.lean` (`applyKont`/`unwind`
— the two *conditional* statements, since `kont = []` is the pass-through point),
`evalExpr`/`stepFn`, and `CatchFree` threading through the `throw` arm. The tactic lessons that
made the difference are recorded in `Denote/Sem/notes.md` — chiefly that `simp_all` must be a
per-goal last resort, that a lemma keyed on a lambda is invisible to `simp` but visible to
`rw`'s *conditional* form, and **the shape problem**: Lean collapses nested record updates into
one flat literal, so a machine that *is* `pushK K m'` does not unify with `pushK K ?m` and
needs a keyed variant per callee.

They rest on two lemmas in `Denote/Rules/Core.lean`: `denM_ctl`/`StateOk_reCtl` (conformance
and the denotation cannot see `ctl`/`kont` — the arrow arms survive because `applyIn`/`sendIn`
overwrite both, so the run a call denotes is the same run) and `evals_pure` (the two-step
inversion). The working procedure for climbing a rung is
[`Denote/Sem/notes.md`](Denote/Sem/notes.md), which also records the **eleven** stall points and
a map of which of three walls each of the 53 remaining rules sits behind — the tenth (a spine
read as every entry against consumers that read the first; **resolved** in clink 52, and it was
a live vacuity rather than a hard rung), the eleventh (a `def` changes a `classPayload?`, so it
is not an `Ext` *or* a `Later` — the two run-quantifying components do not transport across a
declaration, and honestly should not) —
the eighth (a table keyed by path against a rule keyed by name; **resolved** in clink 50 by
restating `ConstsOk` over its lookup function) and the ninth (a rule with a *negative* premise
about a table needs conformance to be an **upper** bound, and every component is a lower one —
which stopped `bareName` and `lambdaLit`, both **resolved and climbed** in clinks 51–52) found
in clink 50, and the fifth — the
continuation-framing wall — **measured** there and smaller than its first estimate: a
dependency chain of one-line lemmas over ~30 helpers, not a line count proportional to the
interpreter. Two found in clink 48: a **declaration statement** makes the incoming `κ` stale, so
`defStmt`/`casgn`/`classStmt`/`moduleStmt` have **false** obligations for a reason that is the
judgment's shape rather than a bug in a rule (the checker is right on the reproducer); and an
**argument list is not a snapshot**, so `SemJudgeAll`'s "every type at the final machine" is
unprovable as stated and is one mutating `PrimSig` row away from being a soundness bug.

**`strLit` — the allocation stall — is broken** (clink 45), and it cost a definitional change
plus two new `StateOk` components. A string literal allocates, so it is the first rule whose
post-machine differs from its pre-machine in the *heap*, and `denM`'s **arrow** arm is the one
part of a type's meaning that does not survive that (it quantifies over runs, and a run from
an extended heap allocates at shifted ids). Fixed where the problem is: both arrow arms — and
`AsmsOk`, same shape — now quantify over `∀ m₂, Ext m m₂`. **`Ext`** (`Denote/Ext.lean`: same
frames, same stack, a heap that only grew) is the "coarser seed" clink 44 said any such fix
would need — reflexive and transitive, so the arm is monotone by construction (`Ext.refl`
recovers the old reading, making this a strengthening), and blind to `ctl`/`kont`, which is
exactly what a `Reaches`-indexed arrow could not be. It is weaker than `ArrowStable` (stable
under allocation, not under execution) and that gap is recorded. `denM_ext`
(`Denote/Grow.lean`) transports a type's meaning across an `Ext`; `StateOk_ext`
(`Denote/Sem/State.lean`) transports conformance, and `StateOk_reCtl` is now a corollary of it.
`StateOk` gained **`HeapSaturated`** and **`CoreOk`** — the first *imported* from the model's
own metatheory (`RubyCore/Proof/AncestorsGrow.lean`: `ancestors` is fuel-bounded by
`objs.size + 1`, so a push moves the **fuel**), which makes `Denote/Ext.lean` the first file
here to depend on `RubyCore.Proof.*`. The surprise on the way: `Heap.get` is **total**, so
`.ref n` at a heap of size `n` is a dangling reference reading as a bare `BasicObject` — which
is why `Ext` carries two fresh-id clauses, and why no value-boundedness invariant was needed.

**A third, and the ladder found it without a rung** (clink 48, fixed in clink 49;
`found-issues.md` §F3). The
sixth stall point says a rule cannot re-assert conformance with the incoming `κ` after a
statement that *declares* something — and a **call** runs statements too. So every call rule
(`vcallDef`, `callDef`, `callMethod`, `selfCall`, `closCall`, `iterBlock`, …) carries a stale
`defs` table out of a body that redefined a recorded method:
`def bar; 1; end; def foo; def bar; "s"; end; 1; end; foo; bar + 1` is certified `Integer`, and
**both executors raise `TypeError`** — the §F1 shape exactly. Reading the obligation is what
produced the program; no search was involved.

**A second soundness bug, found the same way** (clink 48, fixed in clink 49;
`found-issues.md` §A5/§F2).
`Judge.lambdaLit` has no premise that the name `lambda` is free, and in CRuby a toplevel `def`
shadows `Kernel#lambda` — so `def lambda; 5; end; f = lambda { 1 }; f.call + 1` is certified
`Integer` and raises `NoMethodError`. The twist is where it lands: the **model** special-cases
`lambda`/`proc` before any method lookup, so against the model the rule is *right* and its
obligation is still climbable; the wrong answer is about Ruby and arrives through the model
divergence. First entry where the two soundness statements come apart — and the gate that would
have caught it is `run_agreement.sh`, which never saw the program. The checker needs
`Judge.bareName`'s premise shape either way.

**`vasgnAlias` is discharged, and it is the rung the soundness fix was for** (clink 47).
`Judge.vasgn`'s twin — `__dt_t1 = x`, right-hand side a `.var` — is the first rule on the
ladder that **writes** to the frames, and its proof is where `capStale` earns its keep: the
function `Judge.vasgn` uses to decide which bindings to widen is the *side condition* of
`denM_setLocal` (`Denote/Local.lean`), the transport of a type's meaning across a rebinding.
The checker's guard and the semantic transport are one predicate, which is what it means for
the fix to be the right one rather than one that happens to reject the counterexample.

Three definitions moved to make it close, each a correction rather than a convenience:

* **`Later`** (`Denote/Ext.lean`) is now what the **arrow** and **`AsmsOk`** quantify over —
  heap grew, frames *rebound*, no frame pushed or popped — because `Ext` pins the frame array
  and an assignment does not. `denM`'s `clos` arm deliberately does **not** get the quantifier:
  it reads `Machine.frames` and must not be monotone under a rebinding, since that is the fact
  §F1 turned on. Each rung that needs the arrow to survive one more step kind widens `Later` by
  one clause, and the destination is `ArrowStable` (the arrow at every *reachable* machine).
* **`StateOk.frameInRange`** — there *is* a current frame. `getLocal`/`currentFrame` are total,
  so a machine with an out-of-range stack head is not an error, it is one where every local
  reads `nil` and `setLocal` is a no-op; and "the value `x` names after `x = e` is the value
  assigned" is false there.
* **`EnvOk`'s identity conjunct is `Value` equality, not `Value.identEq`.** The model's own
  `equal?` is wrong in both directions at `Float` — it calls `0.0` and `-0.0` the same object
  and `NaN` and itself different ones — so the first reading made the obligation false at a
  local holding `NaN`, for a reason with nothing to do with aliasing. Recorded in
  `found-issues.md`; the denotation should not inherit a model quirk.

**`Judge.vasgn` itself is still not discharged, and no longer for a soundness reason.** Its
right-hand side is an arbitrary expression, so it runs under a *pushed* continuation while its
premise is about a run under the empty one — the continuation-decomposition wall below, which
is a fact about `RubyCore`'s machine and gates every compound rung. Discharging `vasgnAlias`
is the sharpest available statement of the split: the rule is sound and provably so; the
general one waits on a machine lemma, not on assignment.

**The bug that made this necessary** — and the semantic ladder is what found it
(`found-issues.md` §F1, the first entry in that file about the checker rather than about the
model). `Judge.lambdaLit` records the creation-site environment into the type
(`.clos idx (envToSpine Γ) …`); a Ruby block captures **by reference**, so that spine is a
claim about a *binding*, exactly like `Ty.sameAs` — and `Judge.vasgn`, which already kills
aliases to the assigned name (`killAliasesTo`), kills no `Ty.clos`. So:

```ruby
x = 1
f = lambda { x }
x = "a"
f.call + 1          # CRuby: TypeError.  validate: true, type Integer.
```

`validate` returned **`true` on a type-stuck program** — the one thing the permanent negatives
exist to make impossible, and no corpus rung wrote the shape. The obligation named the rule
without needing a witness: `Obl.Judge.vasgn`'s conclusion asks for `EnvOk` at the post-machine,
whose `clos` arm reads `closLocal m' cl` — the captured *frame*, which `setLocal` wrote
through. **Fixed in clink 46** (§Closure captures go stale): `killClosOver`/`killClosOverSpine`
plus a `capStale x τ τ = false` premise, three new corpus rungs and two new controls — and
clink 47 added a fourth guard, `capStaleCtx`, for the three `Ctx` fields (`selfTy`, `blockTy`,
`consts`) that can hold a frame-sensitive type and that no rule can rewrite, since `Ctx` is an
input.

**The wall in front of `vasgn` and every other compound rule** — `Denote/Sem/notes.md`
§The fifth stall point. `Evals` runs an expression under `kont := []`; a `.vasgn` runs its
right-hand side under `[.asgnK …]`, so the premise is about a different run and consuming it
needs a **continuation-decomposition lemma**. The lemma is true (`stepFn` is head-local in
`kont`: all thirteen `kont :=` sites are pushes, and `applyKont`/`unwind` read only the head)
and it is *large* — measured, the obvious one-liner closes 12 of `evalExpr`'s 43 arms, five of
the rest delegate into ~1700 lines of `Interp/{Dispatch,Send,Reflect}.lean`, and the builtins
behind those are kont-transparent only by inspection. It is a fact about `RubyCore`'s machine
rather than about `Denote/`, it gates **every** compound rung, and the shortcut (quantifying
`Evals` over continuations) would weaken all 83 obligations at once.

**The obligations are derived, not transcribed.** `SemJudge` and its seven companions were
given *exactly* their syntactic twins' signatures, which makes a rule's obligation its own
constructor type with one constant swapped:

```
Judge.intLit      :  ∀ {κ Γ I n},  Judge κ Γ I (.int n) .int Γ I
Obl.Judge.intLit  :=  ∀ {κ Γ I n},  SemJudge κ Γ I (.int n) .int Γ I
```

Three consequences, and they are the reason it is done this way:

- **The denominator is live** — read out of `Judge`'s constructor list on every build. Add a
  rule to the checker and 83 becomes 84, listed as undischarged, the same day. The opposite of
  the corpus norm (§Architecture: "a ratchet whose number depends on a live sample is not a
  ratchet") for the opposite reason: the rule set is not a sample of the specification, it *is*
  the specification.
- **An obligation cannot be weakened**, because there is nothing to edit. A rung that will not
  close means fixing a `StateOk` component, a `SemJudge` definition, or the *rule* — those are
  the options.
- **A rung cannot be claimed by naming something easier.** The ladder counts a rule only when
  a declaration `Sem.<Family>.<rule>` exists **and** its type is defeq to the derived
  obligation. Verified against a decoy.

- **`Denote/Sem/Trans.lean`** — `toRuby : Ratchet.Expr → RubyCore.Expr`, 48 arms, no default
  case. This is what makes any of it possible: `Denote/notes.md` recorded "no `Judge` soundness
  theorem, because it needs an evaluation relation for `Ratchet.Expr` and the only executable
  one is over `RubyCore.Expr`". The copy stays (§Isolation is why); it gets a function across
  instead. Also closes `Denote/Den.lean`'s stated `Ty.clos` `idx` gap — `closTblOk` can now
  compare a live Proc's body against the table entry.
- **`Denote/Sem/State.lean`** — `Evals` (evaluate one expression with an empty continuation,
  so its value is the run's result), **`StateOk`** — thirteen conformance components, one per
  `Ctx` field, the threaded `Γ` and `I`, and the two heap facts `strLit` forced
  (`HeapSaturated`, `CoreOk`) — and **`StateOk_ext`**, which transports all thirteen across an
  allocation. Two components are `True` with docstrings saying why rather than by omission.
  `EnvOk` gives `Ty.sameAs` its first meaning outside the checker's bookkeeping (two locals
  hold the same object, by the model's own `equal?`); `AsmsOk` makes the conditionality of a
  non-empty `κ.asms` visible in every obligation's statement.
- **`Denote/Sem/Judge.lean`** — the eight `SemJudge*` definitions. `SemJudge κ Γ I e τ Γ' I'`
  = for every conformant `m`, if evaluating `e` returns `v` in `m'` then the frame stack is
  where it started, `v` is in `τ`'s denotation **at `m'`**, and `m'` conforms to `(κ, Γ', I')`.
- **`Denote/Sem/Obligations.lean`** — the deriving command, and the 83 `Obl.*`.
- **`Denote/Ladder.lean`** — the count and the `isDefEq` gate; `semantic_ladder_status` logs it
  live.
- **`Denote/Adequacy.lean`** — `AdequacyTarget` (the eight adequacy statements, written out)
  and `AdequacyHyps` (the conjunction of all 83, generated from the same list). Adequacy is one
  mutual induction, so it has **no partial credit** — 80 of 83 cases proves nothing — while
  each rung is independent and stays climbed. That asymmetry is why the ladder counts rungs and
  states the theorem, rather than the reverse; `Denote/Adequacy.lean` argues it.

**A rung is one rule, not one unit of work**, and the report says so. `Obl.Judge.intLit` is two
`stepFn` unfoldings; `Obl.Judge.prim` quantifies over the whole `PrimSig` relation, so it owes
~90 separate facts about CRuby's builtins. Both count as one.

**Not on this ladder: stuck-freedom.** `SemJudge` is partial correctness about the *value*.
Whether a well-typed program can reach a `NoMethodError`/`ArgumentError`/`TypeError` — the
`../type-safety-by-reachability.md` property — is a second axis, stated (`StuckFree`,
`StuckFreeTarget`) and deliberately uncounted: one number should mean one thing.

## Semantics status: **imported, and wired up for the covered fragment**

`Semantics/Interp.lean` imports the real `stepFn` (and its whole dependency closure —
`Heap`/`Machine`/`Builtins`/`CRubyNames`/the booted prelude) from `../lean/RubyCore/`
via a local Lake `require`, and provides `Ratchet.Semantics.run`/`typeStuck`/
`resultClassName`/`outcomeLabel` over it — see §Architecture and the file's own docstring
for why this one piece is imported rather than copied, unlike `Expr`/`Ty`.

It is now **wired into the corpus for the 13 rungs the judgment covers**, by the separate
`checkrungs` executable (`CheckRungs.lean`, `scripts/run_check_rungs.sh`) rather than by an
`expect_stuck` field on every rung: for each rung it decodes the committed `program` JSON
a second time with the real `RubyCore.Decode.program`, runs it under the real `stepFn`
from the real booted heap, and checks the value's actual class against the class the
hand-derived `Ty` names, plus `typeStuck = false`. All 13 confirm. Seven hand-written
**negative controls** run the same way (`1 + true`, `"a" + 1`, `1 + 1.5`, …), each
required to be rejected by `chk` and labelled by what the semantics says: four are
genuinely type-stuck (sound rejections), three are safe programs `chk` conservatively
declines for lack of a rule (honest incompleteness, printed rather than hidden).

What is still *not* wired: rungs 14+ (nothing to cross-check yet — `chk` cannot type
them) and any per-rung `expect_stuck` recorded in the corpus JSON itself. Whether that
field is ever worth adding, given `checkrungs` derives the same information by running the
program, is an open call.

## 2026-08-31 rebuild: real `Expr`/`Ty`, real desugared Ruby

The first version of this harness used a from-scratch, invented `Expr`/`Ty`/corpus —
useful for proving the certificate-checking mechanism out quickly, but disconnected from
real Ruby. This version **ports `Expr` and `Ty` verbatim from the real model**
(`../lean/RubyCore/Syntax.lean`, `../lean/RubyCore/Types/Ty.lean` — see the provenance
note at the top of `Ratchet/Expr.lean`/`Ratchet/Ty.lean` for exactly what was kept vs.
trimmed) and sources every corpus program from **real Ruby run through the real
desugarer** (`harness/desugar-dt/bin/export-json`), not hand-authored ASTs. The
semantics (`stepFn`/the interpreter) was initially left out entirely; it is now
imported (not ported — see §Semantics status) but not yet wired into the corpus.

Consequence for the certificate format: since `Expr` derives `BEq` (ported unchanged,
including its docstring's own reason — "added for the certificate language... keyed on
the subterm a claim is about"), the certificate is not a parallel type-annotated shadow
tree (what the first version built). It's a **flat list of claims**, each pairing an
actual `Expr` subterm with the `Ty` it's claimed to have, matched against the real
program by structural equality (`Ratchet/Cert.lean`). A claim should be needed only
where `chk` cannot synthesize a subterm's type structurally.

## 2026-08-31 (later): every rung expects validation

The corpus originally mixed two different things under `expect_validate: false`:
programs that really are unsafe, and programs that are perfectly safe real Ruby but
that the (then-existing) `chk` implementation was too conservative or too incomplete
to certify — most of tiers 7–8 (classes/modules) fell in the second bucket purely for
lack of a dispatch mechanism, not because anything about them was actually unsafe.
That conflated "this must never validate" (a soundness invariant) with "nobody's
written the rule for this yet" (a to-do item), and buried both under the same boolean.

The fix: **`expect_validate` is `true` for every rung unless one of three named
reasons says otherwise** (`Ratchet/Corpus.lean`'s `falseReason`, §Permanent negatives).
Reclassifying the existing 89 rungs against this rule found that most of the
"conservative" ones were fixable with either an existing `Ty` constructor via the
claims escape hatch (`Ty.union` for mismatched `if` branches, `Ty.any` as an array
element type, a claim on an otherwise-unmodeled `==`) or a design principle the old
`chk` simply didn't apply consistently (claim-fallback at every node kind, not just
`send`; the *precise* reading of "type-safe" as "never reaches the specific
NoMethodError/ArgumentError/TypeError family", not "never raises anything" or
"syntactically uniform branches") — see §Design notes for the details of each. Three
rungs whose *program* was safe but whose *certificate* was deliberately dishonest
became a new category (`dishonest_cert`) distinct from unsafe programs, since
rejecting them is a cert-consistency invariant, not a program-safety one. Exactly one
rung turned up a case the existing `Ty` grammar genuinely cannot state a claim for at
all (`cert_language_gap`, since renamed `ty_language_gap` — §Ty language gaps) — the one case this reclassification
was designed to surface rather than paper over, per the instruction that prompted it:
if something can't be expressed in the cert, flag it, don't just mark it `false`.

Also added: tier 9, metaprogramming (`method_missing`, class reopening,
`include`/`extend`/`prepend`), deliberately last on the ladder, and the direct
motivation for finding the one language gap above.

## 2026-08-31 (later still, second pass): claims deleted, agreement gated

Two instructions, one theme — stop letting the ladder count things nobody checked.

**1. Every rung is now difftested against CRuby.** `scripts/run_agreement.sh` runs the
real difftest engine (`../difftest`, `replay --sut lean`) over `corpus/`: each `.rb`
under CRuby and under the Lean semantics, comparing stdout, the final value's `inspect`,
and the escaping exception. `scripts/run_ratchet.sh` runs it *before* the ladder and
aborts on any disagreement. **114/114 agree, 0 disagree** — including all 22 of the new
tier 9. This was the missing leg: the corpus already guaranteed its JSON was real
desugarer output, but nothing said the model this package types actually runs these
programs the way Ruby does, and a type over a program the model gets wrong is a
statement about a fiction. It also keeps the seven `unsafe_program` targets honest —
they have to really raise, on both sides.

**2. Certificates are gone.** `Cert.lean`, `Judge.claim`, `chk`'s claim-fallback, and
every `cert` field in the corpus JSON: deleted. The rationale and the fallout are in
§Claim-free; the short version is that a claim was trusted, so a "claim-assisted" rung
was a rung nobody had checked, and the honest headline is **14**, not 23. `Judge` is now
`Expr → Ty → Prop` with no trusted leaf at all, `validate : Expr → Bool`, and
`Rungs.lean` no longer needs `empty_cert_lookup` to argue its derivations are
claim-free — there is nothing to be free of. Proofs still go through unchanged in
substance (`chk_sound`, `validate_sound_syntactic`, axiom-clean), and `checkrungs` still
reports 13/13 + 7/7.

The corpus rewrite that fell out of (2) is the useful part: ~34 rung descriptions said
"an explicit claim supplies its type" where they now say what rule the checker actually
needs — `Object#== : (any) → Bool`, `Integer#zero?`, `String#length`, a
union-producing `joinTy`, element-type inference for arrays, signature *inference* for
`def` (including the recursive case, where the signature is needed to check the body it
comes from), ivar types from `initialize`'s writes with read-with-no-write = `Nil`. Four
rungs lost their `-with-claim` suffix, and `fun-dishonest-return-claim` — safe program,
lying certificate — became the ordinary `fun-zero-arg`, since there is no cert left to
lie. The `cert_language_gap` reason became `ty_language_gap`: that gap was always in
`Ty`, and both flagged rungs still stand.

## 2026-08-31 (later still): tier 9, blocks/procs/lambdas — 22 rungs

The instruction: *add uses of lambdas, `proc { … }` and block literals, in various and
complex combinations, increasing in complexity.* Added as a **new tier 9**, inserted
*before* metaprogramming (which moved to **tier 10**) so metaprogramming stays last on
the ladder as designed — blocks are a core language feature, not a reflective one.

What the pass found, from running every rung under real Ruby 4.0.5 first and through the
real desugarer second:

- **All three callable literals are one node.** `lambda { … }`, `->(x) { … }` and
  `proc { … }` desugar to `send none "lambda"/"proc" [] (block …)` — the same `block`
  node an iterator call carries as its `blk` child. There is no lambda expression in
  `Expr`. So the claim for a callable literal is just an arrow spine on the `block`
  node, identical in shape to a `def'`'s, and typing tier 9 is: type `block`, type its
  eliminators (`call`, `#[]`, `yield`, `&b`), and give the builtin iterators
  receiver-directed rules.
- **The iterators differ in what they return**, which the corpus now pins one rung
  each: `each` → the receiver, `map` → `arrayOf`(block return), `select`/`sort_by` →
  `arrayOf`(receiver's element type). A single "block rule" would get three of five
  wrong.
- **A second cert language gap, found from the opposite direction.**
  `proc-arity-leniency` (`proc { |x, y| x }.call(1)`, legal Ruby returning 1) needs the
  same missing optional/rest arity constructor `metaprog-method-missing-splat` asks for.
  Its lambda twin `lambda-arity-mismatch` really raises ArgumentError on the same call
  shape — so the gap is sharp: today's arrow spine must either reject the legal proc or
  accept the illegal lambda. §Ty language gaps.
- **`->(x) { return x * 2 }.call(3)` cannot be written at top level** — the desugarer
  exits 3 on `top-level return`. Wrapped in a method, which is the more honest rung
  anyway: it is inside a method body that lambda-local `return` differs from the proc
  and bare-block reading.

Two rungs already passed claim-assisted (`block-pass-symbol-to-proc`,
`block-sort-by-length`) — both because their claim happened to land on the outermost
send, i.e. the checker was trusting the answer, not computing it. *Superseded the same
day*: claims are gone (§Claim-free), so tier 9 is 0/22 and the whole tier is a demand
list. Structural was and is 14.

## 2026-08-31 (night, second): tier 3 — the environment threads — 24 → 30

`Judge` grew from `Expr → Ty → Prop` to `Env → Expr → Ty → Env → Prop`. The **output**
environment is the part that is not obvious and is argued for in `implementation-notes.md`
(clink 2): a Ruby assignment is an expression with a value *and* an effect, so a rule
shape with only an input context forces `seq` to special-case `vasgn` as a statement
head — a lie about the grammar. `prim` threads across receiver-then-arguments in Ruby's
evaluation order, `JudgeSeq` is its own inductive so non-emptiness and "the last
statement's type" are structural, and `Rung` gained an explicit `outEnv` so a derivation
cannot get the environment wrong and still compile.

The rung worth reading twice is `bare-undeclared-var`. The blanket rule ("a bare name is
`.any`, since an unbound one raises `NameError`, which is outside the type-error family")
is unsound: `proc`/`lambda` are bare names too, and raise `ArgumentError` with no block.
So the rule is gated on a one-row `BareNameError` table and stays sound only while no
rule types a `def'` — both recorded in the rule's own docstring as tier-6 obligations.

## 2026-08-31 (night): tier 2's `send` fragment finished — 14 → 24

Ten more rungs, all of them ordinary `send`s, plus a derivation term for `nested-arith`
(which `chk` already answered but which had none on file). The design content is four
new *kinds* of `PrimSig` row — a constrained comparison, a nullary total query, `!` (an
ordinary send, so unary operators need no new `Expr` node or rule shape), and `==`, the
ladder's first rule polymorphic in an argument type and its first *conditional* row, with
the new `EqSafe` side condition on the receiver in place of an unfalsifiable wildcard.
Six negative controls came with them. Full rationale, including why `objEq` has no
sound-rejection control and why `bool-and`/`bool-or` are not tier-2 work at all, is in
**`implementation-notes.md`** (clink 1) — that file is now the running log of
non-obvious choices, one clink per section.

Renames that fell out: `Rungs13.lean` → `Rungs.lean`, `Check13.lean` →
`CheckRungs.lean`, the `check13` exe → `checkrungs`. And `run_ratchet.sh` now runs
`checkrungs` inline between the agreement gate and the ladder, so one command covers all
three legs.

## 2026-08-31 (evening): the first 13 rungs, typed by hand

The instruction that produced this pass: *work through how to type the first 13 rungs
manually, author the judgments by hand, and build high confidence they are correct.* So
the rebuild started from the specification rather than the checker, and stops dead at
rung 13 — no rule was written speculatively for a rung not yet reached.

Four artifacts, in dependency order, each answering a different way the exercise could
have produced confident nonsense:

1. **`Ratchet/Judge.lean` — the judgment.** `Judge : Cert → Expr → Ty → Prop` with one
   constructor per literal, one `prim` rule for an explicit-receiver block-less `send`,
   and `PrimSig`, the primitive signature table *as a relation* (five rows: `Integer`
   `+ - * /`, `String#+`). Read as a spec, each constructor is a one-line, checkable
   assertion about what the real semantics does. Deliberately absent (and each absence
   is a note in the file): no `Env` — `Judge` relates *closed* terms, because no rung
   below 14 mentions a variable and growing a `Γ` changes every rule's shape, so it
   should wait for the rung that forces it; no subsumption rule, since with no
   parameters and no `.any` there is nothing for `subTy` to do and an unexercised
   subsumption rule is a rule nobody has had to justify; no `if`/join, `def`, or
   dispatch.
2. **`Ratchet/Validate.lean` — the decision procedure.** `chk` decides exactly that
   fragment, with the uniform claim-fallback at every node kind (§Design notes' first
   principle), written with explicit nested `match`es rather than `do`/`<|>` so every
   route to a `some` is visible on the page. `validate c p := (chk c p).isSome`.
3. **`Ratchet/Proof/ChkSound.lean` — the tie between them.** `chk_sound : chk c e =
   some τ → Judge c e τ`, and `validate_sound_syntactic` in the shape the runner
   observes. Axiom-clean (`propext`, `Quot.sound`; the `#print axioms` lines are part
   of the file). This is *not* the semantic soundness theorem — that one still needs the
   semantics in its statement — but it is the reduction that makes the `Bool` worth
   reading: trusting `validate` on this fragment now means trusting the ~13 constructors
   of `Judge`/`PrimSig`, not `chk`'s control flow.
4. **`Ratchet/Rungs.lean` + `CheckRungs.lean` — the confidence.** Thirteen `Rung` records,
   each carrying a hand-written **derivation term** (a wrong `ty` does not compile), plus
   `chk_agrees_with_hand_derivations` — one `rfl` per rung, the `Judge ⇒ chk` direction
   that `chk_sound` does not give. `CheckRungs.lean` then closes the two gaps no proof in
   this package can: that each hand-written `Expr` really is what the desugarer emitted
   (decoded from the committed corpus JSON and compared with `==`), and that running the
   **real semantics** yields a value of the class the derived `Ty` names (§Semantics
   status).

Three things the exercise turned up that were worth writing down rather than smoothing
over:

- **`10 / 2` is the cleanest place in the corpus where the two readings of "type-safe"
  come apart.** `PrimSig.intDiv` does not claim division never raises — `10 / 0` raises
  `ZeroDivisionError` — only that it never reaches the
  `NoMethodError`/`ArgumentError`/`TypeError` family and returns an `Integer` when it
  returns. A checker built on the stronger reading would have to reject `10 / 2`.
- **`-5` needs no unary rule.** The desugarer emits `int (-5)`, one negative literal, not
  `send (int 5) "-@" []` — a fact about the desugarer that a hand derivation would get
  wrong in the other direction, and the reason rung 008 is `intLit` again.
- **`Ty.bool` covers both boolean classes.** `true` really runs to a `TrueClass` and
  `false` to a `FalseClass`; `Ty` does not distinguish them, so `CheckRungs.lean`'s
  `expectedClasses` maps `.bool` to both. Recorded because it is the one place the
  cross-check has to be *loosened* to pass, and a loosened cross-check should be
  deliberate.

## Claim-free (2026-08-31)

This package used to carry a **certificate**: a rung's JSON held a list of claims —
(subterm, `Ty`) pairs — and both `Judge` and `chk` had a leaf that admitted whatever a
claim asserted. It is **gone**: `Cert.lean` is deleted, `Judge.claim` is deleted, `chk`'s
fallback is deleted, and every `cert` field is out of the corpus JSON.

Why. The leaf was unsound in general, and not subtly: a claim on the program's root node
made `validate` answer `true` having checked nothing. The report tried to contain that by
splitting each tier into "structural" and "claim-assisted", but a claim-assisted rung is
a rung nobody checked, and a ladder whose rungs can be climbed by asserting the answer is
measuring the wrong thing. Nothing above tier 2 needs the escape hatch *yet* — the rungs
it was covering (`5.zero?`, `"abc".length`, function signatures, method signatures) all
want real rules, and the corpus is now written as demands for those rules instead of as
answers to them.

What it cost, honestly: the headline dropped from "23 validating" to **14**, which is
what it always was. Three rungs changed meaning and are recorded where they live:
`unknown-method-with-claim`/`str-length-with-claim`/`array-index-with-claim`/
`hash-index-with-claim` lost the suffix and became demands for real builtin rules
(`unmodeled-builtin-zero-p`, `str-length`, `array-index`, `hash-index`);
`fun-dishonest-return-claim` — a safe program whose *certificate* lied, targeting `false`
so that a self-inconsistent cert could never validate — has no cert to lie any more and
became `fun-zero-arg`, an ordinary `true` target; and the `cert_language_gap` reason
became **`ty_language_gap`** (§Ty language gaps), since the gap was always in `Ty`, not in
the cert format.

What might bring claims back: a *declaration* is not a claim. A user-written signature
(a Sorbet `sig`, an RBS file, an inline annotation) is part of the program's own text and
can be checked against the body, which is a different thing from a certificate asserting
a type nobody verifies. If declarations arrive, they arrive as syntax with a conformance
check, not as a trusted lookup table.

## Isolation

`Ratchet/` (the checker) imports nothing from `../lean/RubyCore/` — own `Expr`/`Ty`,
copied text, not linked; if this package's copy and the real model's ever diverge,
that's a deliberate fork to notice and resolve, not a build error to silently paper
over. `Semantics/` is the one deliberate exception (§Semantics status): it `require`s
`../lean` as a local Lake path dependency and imports the real `RubyCore.Interp`
directly, because hand-copying `stepFn`'s ~24k-line dependency closure the way
`Expr`/`Ty` were copied would trade a small, auditable diff for an enormous,
unmaintainable one. `Ratchet/` does not import `Semantics/` (or vice versa) — see
§Architecture for exactly where the line is drawn. **`Denote/` is the one library that
imports both** (`Ratchet/Ty.lean` + `Semantics/Interp.lean`), because a denotation is by
definition a statement relating the two languages; `Denote/` proper imports no `Judge` and no
`Ratchet/Expr.lean`; `Denote/Sem/` does import both, because the semantic judgment is a claim
*about* `Judge`'s rules and its obligations are derived from that inductive
(§Semantic ratchet status). Nothing outside `Denote/` imports any of it. Own `lakefile.toml`, own
`lean-toolchain` (pinned to the same `v4.32.2` as `../lean/`, which the `require` now
makes an actual constraint, not just a coincidence).

## Architecture

- **`Ratchet/Expr.lean`** — `Expr`/`Param`/`KwEntry`/`VarKind`/`TargetKind`, ported
  verbatim from `RubyCore/Syntax.lean`, plus its `Decode` namespace: the real
  `Export::VERSION` 4/5 JSON wire-format decoder. This is the *only* decoder in this
  package for program syntax.
- **`Ratchet/Ty.lean`** — the `Ty` inductive ported verbatim from `RubyCore/Types/Ty.lean`
  (`int`/`bool`/`nilT`/`sym`/`cls`/`any`/`clsOf`/`nilable`/`float`/`arrayOf`/`union`/
  `arrow0`/`arrowCons`), plus the pure helpers (`arrowOf`/`arrowParts?`/`subTy`/`subTys`/
  `joinTy`/`mkNilable`/`Env`/`envGet?`/`envSet`). **Not ported**: the metatheory around
  them (`subTy_trans`, `SubEnv`/`subEnvB` and their proofs, lambda-capture pinning,
  `FrameCtx`) — no soundness theorem needs them yet (see the file's own docstring for
  the rationale, and §What is deliberately not built here below).
- **`Ratchet/Judge.lean`** — `Judge : Expr → Ty → Prop` (mutual with `JudgeAll`
  over an argument list) and `PrimSig`, the primitive-signature table as a relation. The
  **specification**: what `validate` is deciding, one human-checkable constructor at a
  time. Covers rungs 1–13 and nothing else, on purpose — see §2026-08-31 (evening).
- **`Ratchet/Validate.lean`** — `primSig?`, `chk`/`chkAll`, and
  `validate : Expr → Bool` (`= (chk p).isSome`). The decision procedure for `Judge`'s
  fragment; every node kind with no rule answers `none`, with no fallback of any kind
  (§Claim-free).
- **`Ratchet/Proof/ChkSound.lean`** — `primSig?_sound`, `chk_sound`/`chkAll_sound`,
  `validate_sound_syntactic`. Axiom-clean; the file ends with its own `#print axioms`.
- **`Ratchet/Rungs.lean`** — every climbed rung as a `Rung` record carrying a
  hand-written `Judge` derivation term, plus `chk_agrees_with_hand_derivations` (one
  `rfl` per rung) and `validate_all_rungs`.
- **`corpus/NNN-id.rb` + `corpus/NNN-id.json`** — each rung is real Ruby source (the
  `.rb`, for human reading) plus a generated `.json` (`{id, tier, description, program,
  expect_validate, false_reason}`) where `program` is a **committed snapshot** of
  `export-json`'s actual output for that `.rb` file, not re-derived live at test time —
  deliberately, per the same norm `certify/`'s own LLM-arm cache follows ("a ratchet
  whose number depends on a live sample is not a ratchet"). Regenerate with
  `python3 scripts/generate_corpus.py`; **never hand-edit the `.json` files**.
  `expect_validate` is a **target**, not necessarily what `validate` answers today —
  `true` for every rung except the twenty-two named in §Permanent negatives, each with a
  `false_reason` (`"unsafe_program"`/`"ty_language_gap"`) explaining why.
- **`slice/*.rb`** + **`slice/drivers/*.rb`** + **`scripts/build_slice_rungs.py`** — tiers
  18 and 19. These eleven rungs' Ruby is **Homebrew's own source**, so it is not written
  inline in `generate_corpus.py`: `build_slice_rungs.py` composes each one out of boot stubs
  (imported from `difftest/tiers/tier0/rspec_harvest.py`, plus `BLANK_NIL_STUB` —
  §2026-09-01), `linker` over the file's require-closure, and a driver from
  `slice/drivers/`, and writes it to `slice/<name>.rb`. Those composed programs are
  **committed**, so regenerating the corpus needs nothing; only *re-composing* needs the
  gitignored `homebrew/vendor/brew` checkout. Run it as
  `cd ../difftest && PYTHONPATH=.. uv run python ../ratchet/scripts/build_slice_rungs.py`
  (the difftest venv is where the linker's dependencies live).
- **`Main.lean`** / **`scripts/run_ratchet.sh`** — the runner. `scripts/run_ratchet.sh`
  does two things in order: the **agreement** gate (next bullet), then the ladder.
  `Main.lean` is the ladder half — it loads every corpus entry, runs `validate`, and
  reports per-rung and per-tier results against the recorded `expect_validate` (one
  number per tier now, §Claim-free), a dedicated always-shown list of `ty_language_gap`
  rungs (§Ty language gaps), plus a count of rungs where today's answer differs from the
  target (still large, by design — see §Checker status). `Main.lean` imports
  `Ratchet.Rungs` but not `Semantics/`: the ratchet's headline number stays a pure
  statement about `validate`.
- **`scripts/run_denote.sh`** — the **semantic ratchet** (§Semantic ratchet status): the
  denotation's `#guard` gate, then `semladder`'s discharged/total over `Judge`'s rules.
  Parallel to `run_ratchet.sh`, measuring justification rather than reach; exits nonzero while
  rules remain, same convention.
- **`scripts/run_agreement.sh`** — **every rung, under CRuby and under the Lean
  semantics, compared.** Delegates to the real difftest engine
  (`../difftest`, `replay --sut lean`), which runs each `.rb` both ways and compares the
  full observation: stdout, the `inspect` of the final value, and the escaping
  exception's (class, message). This is what makes a rung's *type* mean something — a
  program the model executes differently from Ruby is a program whose type is a
  statement about a fiction — so `run_ratchet.sh` runs it first and aborts on any
  disagreement. Currently **254/254 agree**. Needs `uv` and a CRuby; skip with
  `RATCHET_SKIP_AGREEMENT=1`. Note the division of labour with `checkrungs`: this compares
  *the model against Ruby* over the whole corpus, `checkrungs` compares *a hand-derived type
  against the model* over the 129 covered rungs.
- **`CheckRungs.lean`** / **`scripts/run_check_rungs.sh`** (the `checkrungs` exe) — the evidence
  behind the covered rungs, and the **one file allowed to see both sides**: it imports
  `Ratchet/` *and* `Semantics/`, decodes each rung's JSON twice (once into
  `Ratchet.Expr` to compare against the hand-written derivation's subject, once into
  `RubyCore.Expr` to run), and cross-checks the derived `Ty` against the class the real
  semantics produced. Also runs the seven `PrimSig` negative controls. `expectedClasses`
  here is the only place in the package that gives a `Ty` an extensional reading —
  `Semantics/` returns a class-name `String` precisely so it never needs to know about
  `Ratchet/Ty.lean`.
- **`Semantics/Interp.lean`** — `Ratchet.Semantics.run`/`typeStuck`/`resultClassName`/
  `outcomeLabel`, over the real, **imported** (not copied) `RubyCore.Interp.stepFn` and
  its full dependency closure — see §Semantics status. The one place this package's
  `lakefile.toml` declares a `require` on `../lean`.

## The ladder (19 tiers, 235 rungs, 129 climbed)

**Every rung's target is `expect_validate = true`, with exactly twenty-two, named
exceptions** (§Permanent negatives below) — see the 2026-08-31 (later) note for why
this is stricter than the first cut of this corpus was, and `Ratchet/Corpus.lean`'s
module docstring for the two reasons a rung is allowed to target `false` at all.

**Every rung also agrees with CRuby**, checked by `scripts/run_agreement.sh` before the
ladder is reported: 254/254 (§Architecture) — including the eight slice files and the
2,176-line linked slice.

1. Literals (8 rungs) — all eight climbed.
2. Arithmetic/string/bool `send`s (20 rungs) — **all 18 non-negative rungs climbed**, via a hardcoded builtin
   dispatch table (`PrimSig`) now fourteen rows deep: arithmetic, the integer
   comparisons, the nullary total queries (`5.zero?`, `"abc".length`, `5.to_s`), `!` (an
   ordinary send, not syntax), and `Object#==`, whose argument is unconstrained because
   `1 == "a"` is safe Ruby — its receiver instead carries the `EqSafe` side condition.
   The tier's last two rungs, `bool-and`/`bool-or`, are `&&`/`||`, which desugar to
   `seq`/`vasgn`/`if` and so were climbed with tier 4, not here.
3. `var`/`vasgn`/`seq` (6 rungs) — **all six climbed.** Real Ruby scoping (mutable
   locals, not the `let` of a from-scratch toy language): the judgment threads an
   environment (`Judge Γ e τ Γ'`) and `envSet` overwrites, so re-binding a local at a
   different type is correct rather than an error. `bare-undeclared-var` is climbed via
   the one-row `BareNameError` table, *not* a blanket "a bare name raises NameError"
   rule — which would be unsound, since `proc`/`lambda` are bare names that raise
   `ArgumentError` (`implementation-notes.md` clink 2).
4. Conditionals (9 rungs) — **all nine at target** (`implementation-notes.md` clink 3).
   Two rules (`if'`, `ifNoElse`) rather than one over `Option Expr`; the condition's type
   is discarded because Ruby's `if` never raises over it; a total `joinT` that produces a
   **normalized** `Ty.union` where the ported `joinTy` answers `none` — which is where
   `Ty.union` stops being inert, and is sound because *nothing consumes a union*; and a
   pointwise `joinEnv`, which is a soundness requirement, not precision:
   `if-does-not-leak-reassignment` is an unsafe program whose recorded target used to be
   `true`, and is now `false` with a matching negative control.
5. Arrays/hashes (8 rungs) — **all eight at target** (`implementation-notes.md` clink 4).
   Indexing (`#[]`) is just a `send` — the real `Expr` has no index constructor — so the
   tier costs two `PrimSig` rows and two `Judge` rules. `arrayOf`'s single element type
   comes from `joinT` over the elements (`array-heterogeneous`); the empty literal is
   `arrayOf .any` by vacuity, not by a join unit (`Ty` has no bottom type);
   `Array#[]` is `nilable elem` because `[1,2,3][99]` is `nil`; and a hash is the
   unparameterised `.cls "Hash"`, so `Hash#[]` can only be `.any`. `arrayOf`'s invariance
   is not yet load-bearing — there is no rule for `Array#<<` or `#[]=` — and the tier that
   adds one inherits the obligation.
6. Top-level functions (9 rungs) — **all nine at target** (`implementation-notes.md`
   clink 5). There turned out to be no signature to infer: `Judge.callDef` types the body
   once per call-site argument shape, in `paramEnv`'s fresh parameters-only environment, so
   `fun-returning-array`'s return type comes wholly from the body and its parameters wholly
   from the call site. `fact` is handled by assume-then-verify — a first pass types the
   recursive call at the new `Ty.never` to *find* a candidate, a second pass must reproduce
   it — and the control that shows the second pass is load-bearing is in `CheckRungs.lean`.
   `bareName` grew the `defGet? D m = none` premise clink 2 predicted it would need.
7. **Classes (16 rungs).** Real, varied class-based Ruby (construction, ivars,
   inheritance, `super`, singleton "factory" methods, instances in arrays/hashes).
   **All 16 climbed** (`implementation-notes.md` clinks 6 and 7). The object model:
   `Ty.inst` carries an instance's ivar spine, `newInst` manufactures one by judging
   `initialize` at the call's argument types, `callMethod`/`selfCall` dispatch off the
   receiver's type, and `selfExpr` keeps the spine so `x.myself.getX` still reads an ivar.
   Then the hierarchy: `mroGet?` walks `Cls.super?` and reports the definition site,
   `Ctx.frame` is what lets `super` delegate from that site rather than from the receiver's
   class (and the ivar spine threads through the super call, so a parent constructor sets the
   child's ivars), and `Cls.smethods` plus `.clsOf`-typed `self` handle `def self.origin` and
   the bare `new` inside it.
   Wants a declaration table over class bodies, ancestor-chain dispatch, and ivar types
   inferred from `initialize`'s writes — with `class-ivar-lazy-nil` pinning the corner
   (an ivar read with no write is `nil`, not an error). See §Design notes.
8. **Modules (10 rungs).** **All ten climbed** (`implementation-notes.md` clink 8), and the
   cheapest tier on the ladder: `M.foo` for a `def self.foo` is tier 7's `callSMethod`
   unchanged. Only `moduleStmt` and `selfSCall` were missing. The real work was
   `Cls.isModule`, which stops `M.new` — a guard that no rung exercises and that lives in a
   negative control.
9. **Blocks, procs and lambdas (22 rungs).** **19/22 — every rung it targets**; see clink 18
   for the iterators (`IterSig`, a table split in two so half a row is read before the block's
   body and half after).
   Original note: Ruby's callable literals, in one place
   and increasing in complexity: `lambda {}`/`->(){}`/`proc {}` (all three desugar to
   the *same* shape — an ordinary `send none "lambda"/"proc" [] (block …)`, so a block
   literal is the only callable node there is), the elimination forms (`call`, `#[]`,
   `yield`, a reified `&b` param), the receiver-directed iterator rules
   (`each`/`map`/`select`/`inject`/`sort_by`, which differ in *what* they return:
   receiver, block-return, or element type), block-locals in a do/end body, both
   `blockpass` shapes (`&:to_s`'s Symbol#to_proc coercion and `&some_lambda`), closure
   capture, nested blocks, two-param folds, an `if` inside a block body, higher-order
   arrows in both return position (`->(x){ ->(y){ x + y } }`) and param position
   (`def apply(f, v)`), and lambda-local `return`. **10/22 climbed** (clinks 9 and 10): the
   creation/elimination core, with a callable's type being `Ty.clos` — a reference to its
   block plus its captured locals — and *not* the arrow spine, which needs parameter types
   Ruby never writes; then `yield` (via `Ctx.blockTy`), `&b` parameters, and lambda-local
   `return` (via `bodyResult`, on the body's whole shape — the obvious rule is unsound).
   What is left is exactly one thing: the **iterator rules**, a genuinely new, higher-order
   kind of `PrimSig` claim, plus the two `blockpass` forms that need it and the one rung
   wanting `|x; y|` block-locals. 19 of 22 target `true`; the three that don't are the tier's
   real findings — `block-bad-arith` and `lambda-arity-mismatch` (genuinely raising
   programs) and `proc-arity-leniency` (§Ty language gaps).
10. **Metaprogramming (6 rungs) — LAST on the ladder, as intended.** **5/6 — every rung it
   targets** (clinks 21–24). Original note: `method_missing`,
   class reopening, and `include`/`extend`/`prepend`. Five of six are ordinary safe
   Ruby needing only dispatch design (§Design notes has the subtleties: self-context
   `vcall` resolution, mixin ancestry, prepend-ordered MRO with `super`, a
   method_missing fallback route). The sixth (`metaprog-method-missing-splat`) is one of
   this ladder's two found **ty_language_gaps** — see §Ty language gaps.

11. **Cross-cutting (10 rungs).** No new feature — *combinations* of features that already
   have rules, added because a corpus-driven ladder is blind to its own cross-products.
   **8/10 climbed — every rung it targets** (clinks 11, 19, 20). Two clinks did it: `Ty.clos`
   gained the **creation site's `self`** (so a closure's body is judged where it was written,
   not where it is called — which is what `@f.call(v)` inside a method needs), and three
   block-carrying call rules appeared (`callMethodBlk`/`callSMethodBlk`/`selfCallBlk`), each its
   block-less twin plus `callDefBlk`'s two moves. `xc-inherit-implicit-block` — an
   implicit-receiver send carrying a block, inside a method, dispatching to an *inherited*
   method — needed nothing new at all, which is the outcome a cross-product tier is supposed to
   have.
12. **Narrowing (12 rungs).** No new feature either — the capability that makes `nilable` and
   `union` *usable*. **9/12 — every rung it targets** (clinks 12–17, 25, 26). The three not
   climbed: two permanent negatives and one `Ty` language gap (`narrow-nilable-and-union`,
   retargeted — see §Ty language gaps).
   **Aliasing** (clink 25) is the piece clink 17 deferred: `Ty.sameAs (name) (τ)` carried in the
   **environment**, because the environment already threads — which makes every place that could
   invalidate an alias a place that already *writes* to it. The invalidation argument is four
   cases, and one of them (a branch that invalidates in one arm only) falls out of the existing
   `joinT` for free. `Module#===` came with it, guarded differently from `is_a?` because
   `Module#===` does not go through `obj.is_a?`. Clink 26 added `NarrowSides` — a **one-sided**
   refinement, which `&&` needs and which is soundness rather than caution (control (nnn) is the
   sharpest test on the ladder of `Ty.never`'s dead-branch reading) — and closed a gap open since
   clink 13: `narrowCond?_sound`, which ties the recognizer to `NarrowCond`, decorative until
   then. The corpus came first, deliberately as
   pressure (clink 12); the four climbed are the ones whose condition tests a local *directly* —
   `if x`, `if x.nil?`, `if x.is_a?(Integer)`, `if x.is_a?(Dog)` — so they need no aliasing.
   The tier's original finding stands for the remaining eight: **narrowing cannot be a
   syntactic rewrite** — `case v when Integer` desugars to a temp plus `Integer === __dt_t1`
   with the branch bodies still using `v`, so refinement needs an *aliasing* story;
   `if x && x > 1` puts a whole `seq` in the condition position; `return 0 if x.nil?` narrows by
   *elimination of a branch that leaves*. Also still owed: narrowing an **ivar** (which needs
   `if'`'s `I₁ = I₂` premise to become a join) and narrowing inside a block body. Of the two
   things clink 12 said this tier brought due, one arrived as a *guarded* row rather than the
   wildcard `nil?` it predicted (`NilQSafe`), and the other — `subTy` — **did not arrive at
   all**: `narrow-union-subclass` needs the ancestor walk, not subsumption (clink 14).
   One recorded target now looks wrong: `narrow-nilable-and-union` targets `true` but is
   provably not certifiable, because `arr[0]`'s `nilable` survives into the else-branch — see
   clink 14's last section.

**Tiers 13-19 are the Homebrew slice** (§2026-09-01), and they are written from the target
rather than from a feature list. 13-17 are the syntactic forms the slice uses and the corpus
did not, one rung per form and measured rather than guessed; 18 is the eight files; 19 is the
whole linked program.

13. **Constants and scoped names (13 rungs). 12/13 — every rung it targets**
    (`implementation-notes.md` clinks 27–32). 928 `const` reads, 155 `cpath`s and 54 `casgn`s
    in the slice; the corpus had `const` only as a class name in `C.new`. The prediction that a
    constant environment must be "threaded through `class'`/`module'` bodies rather than a
    whole-program table" was right about the *requirement* and wrong about the *mechanism*: it
    lives in `Ctx` (carried into method bodies for free) and grows at `JudgeSeq.cons`, and a
    class body's constants are typed at the class statement against a syntactic `constLitTy?`
    rather than being threaded at all. The class-body forms came with it — `attr_reader`
    (expanded into the `def`s it stands for), `alias` (resolved by `classMethods?`),
    `private_constant` (the one item here that is *precision*, not soundness — `NameError` is
    outside the type-stuck family), and `Object#class`/`Module#to_s`. Nested namespaces cost
    qualified `Cls.name`s and `JudgeNested`, and nothing else.
    `const-frozen-hash` **climbs and does not deliver**: it types at `.any`, which nothing
    consumes, which is the ladder's sharpest statement of §Frontier item A — `cvss.rb` reads
    every one of its six frozen tables with `fetch` and puts the result into Float arithmetic.
14. **Parameters and arguments (15 rungs).** **1/15**, and the 1 is the finding
    (`param-block`, §2026-09-01). §Frontier item 11 has recorded optional/rest/keyword
    parameters as owed since tier 6; the slice settles it, with **105 `kwargs` nodes** at call
    sites. Two things are new in kind. First, keyword arguments are matched **by name**, and a
    missing one raises ArgumentError, which is *in* the type-error family — so unlike a
    positional arity mismatch this is a soundness obligation (`param-missing-keyword-unsafe`
    is the control). Second, `arg-splat-call` and `arg-kwsplat-call` are blocked on facts
    `Ty` cannot state — an array's **length** and a hash's **keys** — which is
    `narrow-nilable-and-union`'s gap arriving from a third direction. `param-rest`'s finding
    is the opposite: a `def` is called by name, so the rest *parameter* needs no arity spine
    at all, and the `ty_language_gap` is only about a callable in a variable.
15. **Strings, symbols and regexps (19 rungs).** **3/19.** The slice's actual diet: 85
    interpolations, 58 regexp literals, 299 symbols. `regexp-match-captures` is the hard rung
    and the one to read — `String#match` answers `MatchData` **or nil** and `MatchData#[]`
    answers `String` **or nil**, so the program is safe only because the match succeeded, and
    its permanent-negative twin `regexp-no-match-unsafe` is the same call that fails. The two
    together force narrowing rather than a blanket answer either way. `regexp-interpolated`
    settles a design question cheaply: a pattern can be built at runtime (`semver.rb`
    interpolates four constants into `SEMVER_REGEX`), so a `Regexp` is **opaque** and nothing
    may be read off its source text. `regexp-gsub-block` is a higher-order row of tier 9c's
    kind, on the path of every purl the slice emits.
16. **Control flow beyond `if` (15 rungs). 10/15** (clinks 37–38). Both design predictions in
    the original note were right, and one of them was right about the *wrong construct*.
    `ctl-while`'s question was indeed the environment rather than the loop, and the cheap sound
    answer was indeed clink 11's rule applied to the loop — condition and body must both leave
    every type where they found it, which makes the fixed point trivial. `begin`/`rescue` has the
    same question in a harder form: a handler runs at an **arbitrary point inside the body**, so
    it cannot be typed in the body's incoming environment, its outgoing one, *or* the join of
    the two (`v = 1; v = "s"; v = 2` has the same types at both ends and a different one in the
    middle). The cheap sound answer there is `noLocalAsgn body` — tier 12's whitelist reused —
    and it costs `ctl-begin-rescue-else-ensure` and `ctl-rescue-in-block`, both of which assign
    in the body. `Vulnerability`'s raise/rescue-as-comparison-protocol is `ctl-raise-custom`,
    climbed, and it needed `excName?` to walk `Cls.super?` to `StandardError`. `raise` is
    `.never`, which is `primNever`'s reading of "does not return" arrived at from the other side.
    `next` gets **no rule of its own** and both obvious ones are unsound (clink 37), so it joins
    `.ret` as a statement kind whose rule lives in `JudgeSeq`. `ctl-rescue-wrong-class-unsafe` is
    the control against reading any `begin` as discharging the type-error family, and it is
    rejected because `Judge.begin'` never looks at the rescued classes when typing the body.
    Still owed: `else`/`ensure`, `ctl-break` (a `break` changes the *enclosing send's* result,
    not the block's) and `ctl-return-early` (the length-indexed array).
17. **Collections and Comparable (23 rungs). 9/23** (clink 39), and mostly *library* rather
    than language: the builtin call shapes the slice reaches for constantly and the corpus never.
    `homebrew/README.md` §2 measures the same gap over all of Homebrew (6.4% of 113,610 call
    sites resolve to nothing we have); these are its slice-sized head. Three findings from the
    rows that are climbed. The guard on a row moved for the first time from the **receiver** to
    the **element** (`include?` calls `==` on elements, `uniq` hashes them) — `NilQSafe` for the
    third time, asking its usual question one level down. Two result types are computed by
    tier 12's **refinement functions** (`compact` is `arrayOf (nonNilTy τ)`, `filter_map` is
    `arrayOf (truthyTy ρ)`), their first use outside `narrowEnvs`. And **`Array#<<` discharged
    tier 5's obligation** with a twist: the row is *invariant*, and that is what keeps clink 34's
    `arrayOf .never`-means-provably-empty reading honest — pushing onto one would need an
    argument of type `.never`, and nothing has one. The price is that `lib-array-push` does *not*
    climb, and it must not (`xs = []` starts at `arrayOf .never`, and a send does not retype its
    receiver's binding).
    The remaining 14 divide into the three `Ty` demands — a parameterised `Hash`
    (`lib-hash-fetch`, 62 sites), a pair type (`lib-array-zip`/`to-h`/`partition`/
    `lib-multiple-assign`), a length-indexed array (`lib-array-first-last`,
    `lib-array-sort-by-max-by`) — plus `Struct` and `lib-comparable`, the payoff of tier 10's
    mixin work, which three of the eight slice files depend on.
18. **The eight slice files (8 rungs).** **0/8.** One rung per file: the file, its
    require-closure, and a driver that exercises its own API. Ordered by dependency, which is
    also roughly by size — `semver.rb` (219 composed lines, 5 `def`s, no state) is the first
    plausible whole-file accept and needs only tiers 13, 15, 16 and 17; `version.rb` (1,033
    lines, nine classes, 63 `def`s, a 30-entry parser table) is the largest.
    `slice-vulnerability` is the decision core and the last rung before the whole thing.
19. **The whole linked slice (3 rungs).** **0/3**, and one of the three is a permanent
    negative. All eight files linked from three entry points (8 spliced, 0 thunked, 0 external
    requires, 0 cycles) under three drivers: the decision-core demonstration, a 16-input sweep
    that shows the verdict is genuinely a *function of its inputs*, and
    `slice-adversarial` — the same program under inputs a caller can supply, which reaches
    five type-family raises and therefore **must never validate**. `slice-whole` and
    `slice-adversarial` are the same code; the difference is a precondition on the inputs, and
    that pair is the ladder's sharpest statement of what a `validate` verdict claims.

Run `scripts/run_ratchet.sh` for current numbers:

```
corpus agreement (CRuby vs the Lean semantics): 254/254 agree, 0 disagree

tier 1: 8/8    tier 2: 18/20  tier 3: 6/6    tier 4: 8/9    tier 5: 8/8
tier 6: 6/10   tier 7: 16/16  tier 8: 10/10  tier 9: 20/27  tier 10: 6/6
tier 11: 8/10  tier 12: 9/12  tier 13: 12/13 tier 14: 9/15  tier 15: 13/19
tier 16: 10/15 tier 17: 11/23 tier 18: 0/8   tier 19: 0/3
flagged Ty language gaps: 2 (proc-arity-leniency, narrow-nilable-and-union)
hand-authored derivations on file: 177
rungs where validate differs from the recorded target: 35
```

All 177 are synthesized by `chk` itself, with nothing trusted anywhere. (This section used
to read "23 validating, of which 14 structural"; the other nine were rungs a certificate
claim answered for. See §Claim-free.) `scripts/run_check_rungs.sh` is the companion number
(also run inline by `run_ratchet.sh`): 177/177 of those cross-checked against the real
semantics **on the prelude-booted heap** (clink 18 fixed a bug where it was not), 144/144
negative controls rejected.

Three numbers, and they move for different reasons:

- **"differs from the recorded target" going down** is the climb, tier fraction by tier
  fraction. It counts *both* directions: a rung targeting `true` that answers `false` is
  work to do, and a rung targeting `false` that answers `true` is a soundness bug.
- **"flagged Ty language gaps"** should stay flat unless `Ty.lean`'s grammar itself grows
  (§Ty language gaps) — not something `chk` alone can move.
- **"254/254 agree" should never move.** A disagreement there is a bug in the model or the
  desugarer, not a climb. It is also why a program the *model* cannot run stays out of the
  corpus even when it is ordinary Ruby — see §Frontier item 13.

## Permanent negatives (23 rungs, and only these 23 by design)

**Clink 49 added two** (`nested-def-redefines-unsafe`, `shadowed-lambda-unsafe`), the
regressions for `found-issues.md` §F3 and §F2/§A5 — both programs `validate` certified and both
executors raise. Like clink 46's, they are controls for a *fix*, not new coverage: a `true` on
either is that soundness bug returning.

**Was 22 until 2026-09-01**, when `metaprog-method-missing-splat` was retargeted to `true` and
climbed — its `ty_language_gap` flag had been misfiled (§Ty language gaps, clink 40). That is the
first time a rung has left this list, and it is worth noting *how*: not by a new `Ty`
constructor, but by re-reading a reason that turned out to be about a signature this judgment
never writes.

Every other rung targets `true`. These don't, each for one of the two reasons
`Ratchet/Corpus.lean` names (`false_reason`). Tier 11 added three: `xc-block-retypes-capture`
and `xc-block-retypes-ivar` (both `unsafe_program`), plus the retargeted
`if-does-not-leak-reassignment` from clink 3. All three are the *same* rule from clink 11 —
a callee may not retype state its caller can still see — and they exist to stop that fix
being reverted. Tier 12 added two more (`narrow-backwards-unsafe`, `narrow-absent-unsafe`),
which exist to constrain a capability that does not exist yet: the first is certified by any
narrowing rule that refines the two branches the wrong way round, the second by any rule that
treats `nilable T` as `T` without a guard.

**Tiers 13-19 added seven**, one per new tier plus the whole-slice probe, and each is the
control for the *specific* wrong generalisation its tier invites:
`const-string-arith-unsafe` (a checker that gave every constant `.any` rather than its
initialiser's type — tempting, because the slice's constants are tables);
`param-arity-unsafe` and `param-missing-keyword-unsafe` (counting arguments instead of
matching them by name — ArgumentError is *in* the family, so this is soundness);
`regexp-no-match-unsafe` (`String#match` typed `MatchData` rather than nilable, whose safe
twin `regexp-match-captures` the checker must also accept);
`ctl-rescue-wrong-class-unsafe` (reading any `begin` as discharging the family);
`lib-array-first-nil-unsafe` (`Array#first` typed non-nilable, the named-accessor twin of
tier 12's `narrow-absent-unsafe`); and **`slice-adversarial`**, the whole linked slice
under adversarial inputs, which is the only one of the 19 that is a real program rather
than a written-to-fail one.

- **`unsafe_program`** (19 rungs) — the program genuinely raises `NoMethodError`/
  `ArgumentError`/`TypeError` when run:
  `bad-plus` (`1 + true`), `unknown-method` (`5.foo_bar_baz` — a made-up method, unlike
  the real `5.zero?` its sibling `unmodeled-builtin-zero-p` uses),
  `fun-wrong-arity`, `fun-body-mismatch`, `fun-unknown-call`, plus tier 9's
  `block-bad-arith` (`[1,2].each { |x| x + "a" }` — TypeError inside a block body,
  which the block wrapper must not launder) and `lambda-arity-mismatch`
  (`->(x){x}.call(1, 2)` — ArgumentError, because lambda arity is strict), and the seven
  above. A sound `chk` must never say `true` for any of these — they are the soundness
  regression tests.
- **`ty_language_gap`** (3 rungs) — `metaprog-method-missing-splat`, tier 9's
  `proc-arity-leniency`, and tier 12's `narrow-nilable-and-union` (retargeted at clink 24; it
  was recorded as a demand on narrowing and is really a demand on `arrayOf` carrying a
  **length**). See next section.

There used to be a third reason, `dishonest_cert`, holding exactly one rung; it went
away with certificates (§Claim-free).

## Ty language gaps

**Two of the four recorded here have since been re-read and are *not* `Ty` gaps** (clink 40,
2026-09-01). Both were phrased in terms of a **signature**, and this judgment never writes one:
`callDef`/`callMissing` type a body once per call-site argument shape (tier 6's finding), so
there is no arity to spine.

- **`metaprog-method-missing-splat` is climbed and retargeted to `true`.** `paramBind` binds
  `*args` to `arrayOf (elemTy <the remaining argument types>)`, which is the *second* of the two
  fixes the entry below itself proposed. It became climbable the moment tier 14b's rest-parameter
  rows landed, written for an unrelated rung.
- **`proc-arity-leniency` still targets `false`, but for a different reason than recorded.** What
  it needs is for **`Ty.clos` to record whether a callable is a proc or a lambda** — only a
  proc's arity is lenient — which is a field on an existing constructor, not a new one. Its
  strict sibling `lambda-arity-mismatch` is a permanent `unsafe_program` for the same call shape,
  and that contrast is exactly the distinction `Ty.clos` cannot currently draw.

So the count printed by `Main.lean` is **2**, and the one that is unambiguously a missing
constructor is the length-indexed array (the fourth entry below), which §Frontier item G shows
the slice asking for from four directions. `Ty`'s arrow spine (`arrow0`/`arrowCons`) is *still*
unused after tier 9 predicted it might never be needed, and the retargeting above is the second
piece of evidence for that prediction.

The original text of the first two entries is kept below, because the reasoning is the record of
what was believed and the correction is only legible against it.

---

**Four found so far. The first two are the same missing thing: `Ty`'s arrow spine
(`arrow0`/`arrowCons`) has no optional-or-rest arity constructor.**
`def method_missing(name, *args)` — the idiomatic shape — has a parameter list no `Ty`
value describes: not "no `chk` rule for it yet" but "no `Ty` states the truth without
lying about arity." Approximating it as `arrow_of([Sym], ...)` fits the zero-extra-args
call site in the corpus while being wrong the moment a caller passes any extra
arguments. `metaprog-method-missing-fixed-arity` sits right next to it in tier 10 with
the *same* dispatch shape and no splat, and validates fine (aspirationally) — proving
the gap is specifically the rest parameter, not `method_missing` dispatch generally.

Tier 9's **`proc-arity-leniency`** reaches the same gap from the other direction:
`proc { |x, y| x }.call(1)` is legal Ruby (a proc pads missing params with nil and
drops extras), but the only `Ty` for that block, `arrow_of([Int, Int], Int)`,
says the call site is wrong; weakening the second param to `nilable Int` still cannot
say "…and may be absent entirely", nor that a third argument would also be fine. Its
strict sibling `lambda-arity-mismatch` is a permanent `unsafe_program` for the *same*
call shape — which is the point: the arrow spine cannot distinguish the two arity
disciplines, so it either rejects the legal proc or accepts the illegal lambda.

Fixing both needs a `Ty` extension — an `arrowRest (rest ret : Ty)` spine terminator, or
modeling `*args` as `arrayOf Ty` — decided deliberately, not smuggled in as a special
case of something else. Until then, `Main.lean`'s runner always prints a "flagged: Ty
language gaps" section (independent of pass/fail) so this doesn't quietly disappear into
a wall of `false`s the way it would have under the old philosophy.
**A third gap, found at tier 5, that costs precision rather than a rung: no `hashOf`.**
`Ty` has `arrayOf` and nothing beside it, so a hash literal can only be the bare
`.cls "Hash"` and `PrimSig.hashIndex` can only answer `.any`. Both tier-5 hash rungs still
*validate* — `.any` is a sound answer, just an inert one — so neither carries a
`ty_language_gap` `false_reason`; the gap shows up instead as a program the checker cannot
type at all, `{"a"=>1}["a"] + 1`, which is safe Ruby recorded as a conservative negative
control in `CheckRungs.lean`. Recorded here anyway, because it names a specific missing
constructor (`hashOf (key val : Ty)`) and it is the first gap in this section that a rung
count does not surface.

**A fourth, found at tier 12 and the first to change a rung's *target*: `arrayOf` carries an
element type and no length.** `narrow-nilable-and-union`
(`arr = [1, "a"]; v = arr[0]; if v.is_a?(Integer) then v + 1 else v + "!" end`) was recorded as
a demand on narrowing, and the narrowing half works: `isATy` sees through the `nilable` and
excludes both `nil` and `String` in one step, so the then-branch types. The **else**-branch does
not, and should not — `nil.is_a?(Integer)` is false too, so `notATy` leaves
`nilable (cls String)` and `v + "!"` would be `nil + "!"`. The program is safe *only* because
this array has an element at index 0, and no `Ty` here can say that. Missing constructor: a
length-indexed array (or a tuple type) that would let `PrimSig.arrayIndex` answer `elem` rather
than `nilable elem` for an index known in range. Retargeted to `false` with
`false_reason = "ty_language_gap"` rather than left as a permanent mismatch, because a sound
checker **must** reject it.

**Watch for more of these as the ladder grows** — this section is the place to record
each one; a `ty_language_gap` `false_reason` should always come with an entry here
naming the specific missing `Ty` constructor, not just "not supported yet."

## Design notes (read before rebuilding `chk`)

The implementation cleared from `Ratchet/Validate.lean` (see `git show
5a9f1ad:sam-xif/ruby/ratchet/Ratchet/Validate.lean` from the repo root) covered:
literals; `var`/`vasgn`/`vcall` (flat environment, no `VarKind` distinction); `seq`;
`if'` (condition exactly `Bool`, branches joined via `joinTy`, no-`else` wrapped in
`nilable`); a hardcoded arithmetic/string/boolean/`to_s` `send` table; `array`
(homogeneous elements only); `hash` (typed as the bare `.cls "Hash"`, no key/value
parameterisation); top-level `def'` + calls dispatched by name, signature supplied by a
claim on the `def'` node, `Param.req` only. Two design principles the corpus now
assumes that version didn't have, plus everything tiers 7–10 need beyond it:

- **Where a structural rule is missing, there is nothing to fall back on** (§Claim-free).
  So the mismatched-branch rungs (`if-branch-mismatch`/`elsif-chain-mismatch`) and
  `array-heterogeneous` are demands on the *join*, not on an escape hatch: `joinTy` has
  to produce a `Ty.union` instead of answering `none`, and the array rule has to join its
  element types (falling back to `any`) rather than requiring them equal. Both stay
  inside the existing grammar — `union` and `any` are already there, currently inert.
- **"Type-safe" means "never `NoMethodError`/`ArgumentError`/`TypeError`", not
  "never raises" and not "the condition/branches are syntactically uniform".** Three
  rungs only make sense under this precise reading: `bare-undeclared-var` (raises
  `NameError`, outside the family, so `Ty.any` is an honest claim — nothing downstream
  depends on its value); `if-condition-not-bool`/`if-nil-condition` (Ruby's `if` never
  raises over its condition's type — a rebuilt `if'` rule should join
  `(thenTy, elseTy)` unconditionally, with no `Bool`-only restriction at all, which
  wasn't just incomplete before, it was actively wrong); `eq-different-type` (`==`
  never raises for unrelated types, so requiring both sides the same `Ty` was a
  conservative *choice* in the builtin table, not a necessity — the rule wanted is
  `Object#== : (any) → Bool`).
- **Ivar types come from `initialize`'s writes, per class** — and the read-with-no-write
  case answers `Nil`, not an error (`class-ivar-lazy-nil`). The old cert design keyed ivar
  types by name *globally*, across every class at once; that simplification went away with
  the claims that carried it, and should not come back.
- **A class with no `initialize`** (`class-no-initialize`, `metaprog-class-reopening`)
  needs `.new` dispatch to default to a zero-arg constructor returning the instance,
  not to fail for lack of an `initialize` claim — mirroring real Ruby's inherited
  `Object#initialize`.
- **`vcall` dispatch must consult the current `self` type**, not just a top-level
  function table: a bare call inside a method body (`class-method-calls-method`'s
  `area`, tier 8/9's bare singleton-method calls) is implicit-self, and resolving it
  needs to try "instance method of self's class" (self bound to `Ty.cls`) or
  "singleton method of self's class" (self bound to `Ty.clsOf`) before falling
  through to a free top-level function.
- **`include`/`extend`/`prepend` are ordinary `send`s** (`send none "include" [const
  M] none`, confirming the umbrella project's "everything is a message send" even for
  metaprogramming) — no new `Expr` head, but the ancestor walk needs to grow two more
  edges: modules a class `include`s are an *additional* instance-method source,
  modules it `extend`s an additional *singleton*-method source, and `prepend`ed
  modules go *ahead* of the class itself in MRO order (so `super`/`zsuper` inside a
  prepended module's method must resolve to the class's own method, not vice versa —
  `metaprog-prepend`'s whole point).
- **A `method_missing` fallback route**: dispatch should try every declared method
  first, then — only if none match — a class's own `method_missing` if it declares
  one (`metaprog-method-missing-fixed-arity`). See §Ty language gaps for why the
  idiomatic splat-arity version doesn't validate yet regardless.

## Frontier

**The order changed on 2026-09-01.** Items 0-16 below were written when the corpus was a
feature list; the corpus is now a *target* (§2026-09-01), and the target ranks the work
differently. The ranking that matters is **how many of tier 18's eight files a capability
unblocks**, and by that measure:

- ~~**A. A parameterised `Hash` type.**~~ — **done** (clink 41), and it was the right thing to
  rank first: four rungs climbed, four retyped, and `Hash#fetch`'s 62 call sites made typeable.
  What the entry did not say is *which* parameterisation: uniform, not keyed, because the target
  reads its tables with a **variable** key (`TABLE.fetch(metric)`), where a per-key map answers
  nothing. And the useful row turned out to be `fetch` rather than `[]`, for a reason about
  `KeyError` being outside the type-stuck family — with only `[]`, every hash read is a nilable
  nothing consumes.
- ~~**B. A constant environment (tier 13).**~~ — **done** (clinks 27–32). The prediction that
  the design question is "scope-threaded rather than a whole-program table" was right; what it
  under-weighted is that the *existing* rules had to change. Four of them grew a
  `constGet? κ n = none` premise, because a `casgn` can rebind a name a class declaration owns
  and both orders of that raise. What it also missed: a class body's constants cannot be
  threaded at all — `Ctx.afterStmt` sees a class statement's type, not its contents — so they
  are read syntactically (`constLitTy?`) and *discharged* by a premise at the definition site.
- ~~**C. Keyword parameters and arguments (tier 14).**~~ — **done** (clink 35). The prediction
  that this is the one place where getting it wrong is *unsound* was right, and there turned out
  to be **two** obligations rather than one: a missing required keyword *and* an unexpected one.
  What it under-weighted is that `Expr.kwargs` is not a value, so the *call shape* had to change
  (`Judge.callDefKw`) rather than a rule gaining a premise.
- ~~**D. `Regexp` as an opaque `.cls` plus the `String` rows (tier 15).**~~ — **done**
  (clink 36), and "cheap" was right: nine rows and one rule for ten rungs. `String#match`'s
  nilable result was *not* the hard part in the predicted sense — tier 12's narrowing cannot help,
  because separating `regexp-match-captures` from `regexp-no-match-unsafe` needs a regexp engine
  rather than a refinement. That rung is now a recorded non-climb.
- ~~**E. `begin`/`rescue` (tier 16).**~~ — **done for the no-`else`/`ensure` shape** (clink 38).
  The prediction about the target was exactly right. What it did not see is that the hard part is
  the *environment*: a handler runs at an arbitrary point inside the body, so the answer is
  `noLocalAsgn body` (tier 12's whitelist), and two of the tier's rungs are its price.
- **F. A pair/tuple type.** `zip`, `to_h`, `partition`, `rpartition` and every
  `a, b = ...` in the slice want one, and `arrayOf` cannot express it because the element
  types need not agree. This is a **fourth independent demand on the `Ty` grammar**, beside
  the three already flagged in §Ty language gaps, and it is the first one the ladder found
  by pointing at a target rather than by writing a rung.
- **G. The length-indexed array** (§Ty language gaps, already flagged). The slice asks for
  it three more ways: `arr.first`, `MatchData#[]` after a successful match, and
  `a, b = s.split("-")`.

`semver.rb` is the cheapest whole-file target, and **B, D and E are all done now** — so the next
pass should point `validate` at `slice-semver` and read what it still refuses, rather than
guessing. That is the first time on this ladder that a whole-file rung is worth *attempting*
rather than deferring, and the honest expectation is that it fails on something unlisted: the
file is 219 composed lines and the per-form tiers only measured the forms the census found.

The demands on `Ty` that remain are **G** (the length-indexed array — `arr.first`,
`MatchData#[]`, every `a, b = s.split("-")`) and **F** (a pair type — `zip`, `to_h`,
`partition`). Both are grammar changes, and both want the care `Ty.clos` and `Ty.hashOf` got: a
**spine** rather than a list payload, so that `Ty` keeps kernel-reducing. Clink 41 is the worked
example — one constructor, four rungs climbed, four retyped, and *no derivation term changed*,
because `JudgePairs` grew two indices without changing its constructors' arity.

The original list, kept because its per-item reasoning is still the record of why each tier
cost what it did:

The full climb, in roughly the order that costs least to unlock the most:

0. ~~**Tier 4, `if`**~~ — **done** (clink 3). Both predictions in this entry held: the
   join over `Env` was the real design question, and it unblocked `&&`/`||`. What the
   entry got wrong is that it filed environment-joining as *precision*; it is soundness,
   and `if-does-not-leak-reassignment`'s target was wrong, not merely imprecise.
1. ~~**Tier 5, arrays and hashes**~~ — **done** (clink 4). Every prediction in this entry
   held, including the `nilable` result for `Array#[]`.
2. ~~**Tier 6, top-level `def`**~~ — **done** (clink 5). The declaration table arrived
   (`DefTable`, threaded), the `bareName` obligation was discharged, and the "infer a
   signature" framing turned out to be avoidable: per-call-site body instantiation needs no
   signature at all. What this entry did *not* anticipate is that `prim`'s explicit-receiver
   restriction and the top-level-`self` assumption survived intact — a method body is judged
   with a locals-only environment and no `self`, so the moment a body needs `self` (tier 7's
   `@ivar`s, its very first rung) both come due at once.
3. ~~**Tier 7, classes**~~ — **13/16 done** (clink 6). Every prediction here held; what the
   entry under-weighted is that the ivar environment had to go in the *type* (`Ty.inst`), not
   just in the judgment, because two instances of one class need different types.
4. ~~**Tier 7's hierarchy**~~ — **done** (clink 7). The `super`-needs-the-definition-site
   prediction was right and was the real design question. The `subTy` prediction was wrong:
   dispatch by walk needs no subsumption, and `subTy` would only come due at a *parameter
   annotation*, which this checker has none of.
5. ~~**Tier 8, modules**~~ — **done** (clink 8). The guess in this entry was right down to
   the mechanism, including "a superclass-less class whose instance methods are unreachable".
   The trap it flagged turned out to be a different one: not `module_function` but `M.new`,
   which needed `Cls.isModule` to reject.
6. ~~**Tier 9b, `yield` / `&b` / lambda-local `return`**~~ — **done** (clink 10). The `yield`
   prediction was right (`Ctx.blockTy`); the lambda-`return` prediction was right that the
   obvious rule is unsound, but the fix turned out cheaper than "change `JudgeSeq`" —
   `bodyResult`, matching the body's whole shape.
7. **Narrowing** (tier 12, 12 rungs) — **the highest-priority item**, and the one that
   unblocks checking under an assumption about inputs: an input's type is almost always a
   `nilable` or a union, and today nothing consumes either, so an open-world checker would type
   nothing. Start with `narrow-nilable-truthy` (bare `var` condition — no aliasing, no new
   `PrimSig` row, a complete capability on its own), then the `nil?`/else form, then `is_a?` on
   a union. Leave `narrow-guard-clause` and `narrow-and-guard` for last. Two existing decisions
   come due with it: a wildcard-receiver row for `nil?` (clink 1 declined one for `!`), and
   `Judge.if'`'s ivar-spine *agreement* premise becoming a *join* (clink 6) so
   `narrow-union-in-ivar` can even produce its union. And `subTy` finally gets a job. See
   clink 12 for why narrowing cannot be a syntactic rewrite — the desugarer's temps mean it
   needs an aliasing story.
8. **Tier 11's cross-products** (9 rungs left) — the highest-value work, because these are
   programs a person actually wrote rather than tier headings. Two fixes cover most of them:
   **`callMethod`/`callSMethod` with a block** (thread it into `blockTy`/`paramEnvB` exactly as
   `callDefBlk` does — mechanically small, and `callMethod`'s docstring should stop implying
   blocks are out of scope), and **`selfTy` in `Ty.clos`** beside the captured locals, which is
   the documented fix for `closCall`'s `selfTy = none` premise and is soundness-relevant rather
   than cosmetic: without it a lambda created in one `self` and called in another has its body
   checked against the wrong one. `xc-module-applies-lambda` is the cleanest single demand for
   the second; `xc-ivar-array-map` needs tier 9c as well.
9. **Tier 9c, blocks passed to builtins** (9 rungs left) — all that remains of tier 9, and
   all one thing: **higher-order `PrimSig`**. `[1,2].map { |x| x.to_s }` needs a claim about
   what `Array#map` *does with* a block, not merely about its argument types, and the result
   depends on a different thing per method — the block's return type (`map`), the receiver
   (`each`), the element type (`select`/`sort_by`), or a seeded accumulator (`inject`). That
   is a new kind of row and probably a new relation beside `PrimSig`; the block's type is
   already a `Ty.clos`, so the machinery to *call* it exists. The two `blockpass` forms
   (`&:to_s`'s `Symbol#to_proc`, `&some_lambda`) need it first, and
   `block-doend-with-block-local` additionally needs `|x; y|` block-locals, which
   `lambdaLit`/`callDefBlk` refuse in their patterns today.
   The arrow spine (`arrow0`/`arrowCons`) is *still* unused, and tier 9's finding is that it
   may never be needed: `Ty.clos` does the job without parameter types.
11. **Optional/rest/keyword/block params** (`Param.opt`/`.rest`/`.key`/`.kwrest`/
   `.block`) — the cleared implementation rejected any `def'` using them, and tier 10's
   `metaprog-method-missing-splat` (with tier 9's `proc-arity-leniency`) needs this
   *and* the `Ty` extension in §Ty language gaps together before it can validate.
   `Param.block` is needed sooner than the rest: tier 9's `block-param-ampersand`
   (`def run(&b)`) is otherwise ordinary safe Ruby.
12. **Blocks and `yield`** (`Expr.block`, `Expr.yield'`) — the real payoff construct, and
   the first one that needs the interpreter (or at least a model of what `each`/`map`
   actually do) to say anything about a block's body. **Tier 9 is now the
   corpus demand for this**, 22 rungs of it, ordered so the first (`lambda { 1 }`,
   `arrow_of([], Int)`) is reachable long before the last.
13. **Modules**: a declaration table (something like the real project's
   `Types/Decls.lean`, deliberately not ported — see §What is deliberately not built)
   keyed by owner name, built from every `def'`/`defs` nested in every `class'`/`module'`
   node (accumulating across reopenings for free), each method's signature *inferred*
   from its body; `.const name` typed `Ty.clsOf name`; `.new` dispatch (default
   constructor or the class's `initialize`); instance/singleton `vcall`/`send` dispatch
   through `self`'s type (§Design notes); a parent-chain *and* mixin-aware ancestor walk
   for inheritance, `include`/`extend`/`prepend`, and `super'`/`zsuper`. Tiers 7, 8 and
   10 (32 rungs) are real Ruby waiting on exactly this — none of it needs a new `Ty`
   constructor except the one item below.
14. **Extend `Ty` with a rest/vararg arrow constructor** (§Ty language gaps) — the one
   `Ty`-grammar change this ladder has found a concrete need for.
15. **A demand on the *semantics*, not this checker: `super` with an explicit block.**
   `class Child < Base; def run; super { |x| x * 3 }; end; end` is ordinary Ruby that CRuby
   runs, but the difftest engine answers `sut_unsupported` — "zsuper with an explicit block" is
   outside `../lean/RubyCore`'s fragment. It is therefore *not* in the corpus: a rung for it
   would attach a type to a program the model cannot execute, which is what
   `scripts/run_agreement.sh` exists to prevent. The first time the semantics rather than the
   checker was the binding constraint on a rung (clink 11).
16. **Extend the semantic cross-check past rung 13.** Mostly done for the covered
   fragment (§Semantics status, `CheckRungs.lean`) and it grows a row at a time as `chk`
   does; the *corpus-wide* half is now covered from the other side by
   `scripts/run_agreement.sh` (CRuby vs the model on all 114, §Architecture). What is
   still open is (a) the real theorem — `validate p = true → ∀ r,
   Reachable p r → ¬ typeStuck r`, which needs the semantics *in the statement*, not just
   in a test harness, and would be the point at which `Judge`'s constructors stop being
   assertions and start being lemmas — and (b) whether a recorded `expect_stuck` field
   per rung earns its keep given `checkrungs` derives the same fact by running the program.
   The original framing of this item, kept because the plumbing note is still accurate:
   the semantics itself is no longer missing —
   `Semantics/Interp.lean` imports the real `stepFn` and exposes `run`/`typeStuck` over
   it (§Semantics status) — what's missing is the *plumbing*: an `expect_stuck` field
   per rung, `Main.lean` importing `Semantics/` and calling `run` on each rung's
   program, and deciding how a rung's `program` JSON gets decoded into `RubyCore.Expr`
   for that call (the real `RubyCore.Decode.program` is already available transitively
   — see the file's docstring — so this may be as simple as decoding the same JSON
   twice, once into `Ratchet.Expr` for `validate`, once into `RubyCore.Expr` for `run`).
   This gets back the other half of the old (pre-restart) corpus design: does a
   `validate`-certified program actually avoid `NoMethodError`/`ArgumentError`/
   `TypeError` when run? Worth doing once `chk` exists again (item 0) — until then
   `validate`'s claims have nothing checker-side worth cross-checking.

## What is deliberately not built here

**No `chk` outside the fragment §Checker status describes** — extending it is the active work;
everything below is about what its eventual design should and shouldn't include.

**No `Env` in `Judge`, and no subsumption rule** — both deliberate, both due at the rung
that forces them (tier 3 and a declared-parameter type respectively). See
`Ratchet/Judge.lean`'s module docstring.

**No semantic soundness theorem.** `../lean/RubyCore/Proof/Cert/Sound.lean`'s
`validate_sound` is the model for what would come next — `validate c p = true → ∀ r,
Reachable p r → ¬ typeStuck r`. `Ratchet/Proof/ChkSound.lean` proves only the *syntactic*
half (`chk ⇒ Judge`); the semantic half needs the semantics in the statement (§Frontier
item 6), and until then `checkrungs`'s per-rung execution is evidence, not proof.

**No `Types/Decls.lean`-style declaration table.** The real project's checker resolves
`send` against a genuine per-class method table built from the whole program (plus a
prelude). A hardcoded `send` table and "one claim per top-level `def'`" (§Design notes)
were deliberately tiny stand-ins. Growing either into a real declaration table, rather
than a longer hardcoded match, is a design decision to make deliberately when the corpus
actually needs it — not preemptively.

**No `Types/Infer.lean`/`Check.lean` reuse.** Whatever `chk` becomes, it should be
written from scratch against the ported `Expr`/`Ty`, not a copy or a wrapper of the real
project's own checker. The point of the restart is to have *our own* small checker whose
coverage is visible and growable one rung at a time.
