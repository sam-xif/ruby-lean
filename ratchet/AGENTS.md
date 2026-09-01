# AGENTS.md — `ratchet/`: a type-checking ladder, restarted small

This is a **restart** of the type-checking work, deliberately isolated from `../lean/`
(`RubyCore`) and from `../certify/`/the judgment layer (own `lakefile.toml`/
`lean-toolchain`, no import of `RubyCore`). Those are real, load-bearing, and not being
replaced — see `../type-safety-by-reachability.md` and
`../docs/semantics/certificate-language.md`/`judgment-layer.md` for that work. This
folder exists because that machinery grew by tackling ambitious whole-slice goals
(Homebrew's `version.rb`, Sorbet fragments, `define_method`) before the checker itself
had a graduated coverage ladder to climb. **The idea here: drive the checker from a corpus that ratchets up in complexity one
rung at a time, so "how far does `validate` reach today" is always a single number, not
a research question.** It started as a certificate-checking ladder and kept the
architecture minus the certificates (§Claim-free): a rung is now a program and a target,
and `validate` either synthesizes the type or does not.

## Checker status: **95 rungs, hand-authored judgment first, nothing trusted**

`Ratchet/Validate.lean`'s `validate` covers **all of tiers 1–8, plus tier 9's callable
values**: the eight literals,
`+`/`-`/`*`/`/` on `Integer`, `+` on `String`, the integer comparisons, the nullary total
queries (`to_s`/`zero?`/`length`), `!`, and `==` with an unconstrained argument (see
`EqSafe`), plus tier 3's locals (`var`/`vasgn`/`seq`, and a bare `vcall` gated on the
`BareNameError` table), tier 4's conditionals (`if'`/`ifNoElse`), tier 5's array and hash
literals with their `#[]`, tier 6's top-level `def` plus implicit-self calls, and tier 7's
`class`/`new`/`@ivar`/instance dispatch/`self`/inheritance/`super`/singleton methods, and
tier 8's modules, tier 9's `lambda`/`proc`/`#call`/`yield`/`&b`, and **tier 12's narrowing**
(the four direct-test rungs) — 95 rungs. **Every rung at or below tier 8 matches its recorded
target; tier 9 is at 10/22, tier 11 at 1/10 and tier 12 at 4/12.** What remains is tier 9's
nine blocks-passed-to-*builtins* rungs, tier 10 (metaprogramming), tier 11's cross-products,
and tier 12's remaining eight narrowing rungs.

**Tier 12 (clinks 13 and 14) is where `nilable` and `union` stop being write-only.** Narrowing
lives *inside* `Judge.if'` — each branch is typed in `narrowEnvs κ.classes c Γc`, a **total**
function that is the identity on every condition it does not recognize, which is why folding it
into the existing rule did not disturb a single one of the 91 derivations already on file. Three
recognized conditions so far (`if x`, `if x.nil?`, `if x.is_a?(C)`), four type-level refinements
(`truthyTy`/`falsyTy`/`isNilTy`/`nonNilTy`) resting on the single fact that Ruby's only falsy
values are `nil` and `false` — which is why `falsyTy .int = .never` is *precise*, not reckless —
plus `isATy`/`notATy`, which project a union member-by-member using complete ancestor lists
(`builtinAncestors` for builtins, `ancestors?` for declared classes). `nil?` needed a *guard*
(`NilQSafe`) rather than the wildcard receiver clink 1 declined for `!`; `is_a?` needed a
`Judge` rule of its own (`isAQuery`), because its guard consults the class table and `PrimSig`
cannot. Clink 14 also records that **`subTy` is still unused** after two clinks predicted
narrowing would bring it due: refinement needs class *membership*, not `Ty` subsumption.

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
§Architecture for exactly where the line is drawn. Own `lakefile.toml`, own
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
  `true` for every rung except the nine named in §Permanent negatives, each with a
  `false_reason` (`"unsafe_program"`/`"ty_language_gap"`) explaining why.
- **`Main.lean`** / **`scripts/run_ratchet.sh`** — the runner. `scripts/run_ratchet.sh`
  does two things in order: the **agreement** gate (next bullet), then the ladder.
  `Main.lean` is the ladder half — it loads every corpus entry, runs `validate`, and
  reports per-rung and per-tier results against the recorded `expect_validate` (one
  number per tier now, §Claim-free), a dedicated always-shown list of `ty_language_gap`
  rungs (§Ty language gaps), plus a count of rungs where today's answer differs from the
  target (still large, by design — see §Checker status). `Main.lean` imports
  `Ratchet.Rungs` but not `Semantics/`: the ratchet's headline number stays a pure
  statement about `validate`.
- **`scripts/run_agreement.sh`** — **every rung, under CRuby and under the Lean
  semantics, compared.** Delegates to the real difftest engine
  (`../difftest`, `replay --sut lean`), which runs each `.rb` both ways and compares the
  full observation: stdout, the `inspect` of the final value, and the escaping
  exception's (class, message). This is what makes a rung's *type* mean something — a
  program the model executes differently from Ruby is a program whose type is a
  statement about a fiction — so `run_ratchet.sh` runs it first and aborts on any
  disagreement. Currently **114/114 agree**. Needs `uv` and a CRuby; skip with
  `RATCHET_SKIP_AGREEMENT=1`. Note the division of labour with `checkrungs`: this compares
  *the model against Ruby* over the whole corpus, `checkrungs` compares *a hand-derived type
  against the model* over the 13 covered rungs.
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

## The ladder (12 tiers, 136 rungs, 95 climbed)

**Every rung's target is `expect_validate = true`, with exactly nine, named
exceptions** (§Permanent negatives below) — see the 2026-08-31 (later) note for why
this is stricter than the first cut of this corpus was, and `Ratchet/Corpus.lean`'s
module docstring for the two reasons a rung is allowed to target `false` at all.

**Every rung also agrees with CRuby**, checked by `scripts/run_agreement.sh` before the
ladder is reported: 114/114 (§Architecture).

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
9. **Blocks, procs and lambdas (22 rungs).** Ruby's callable literals, in one place
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
10. **Metaprogramming (6 rungs) — LAST on the ladder, as intended.** `method_missing`,
   class reopening, and `include`/`extend`/`prepend`. Five of six are ordinary safe
   Ruby needing only dispatch design (§Design notes has the subtleties: self-context
   `vcall` resolution, mixin ancestry, prepend-ordered MRO with `super`, a
   method_missing fallback route). The sixth (`metaprog-method-missing-splat`) is one of
   this ladder's two found **ty_language_gaps** — see §Ty language gaps.

11. **Cross-cutting (10 rungs).** No new feature — *combinations* of features that already
   have rules, added because a corpus-driven ladder is blind to its own cross-products.
   **1/10 climbed** (clink 11); see §Checker status.
12. **Narrowing (12 rungs).** No new feature either — the capability that makes `nilable` and
   `union` *usable*. **4/12** (clinks 12, 13, 14). The corpus came first, deliberately as
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

Run `scripts/run_ratchet.sh` for current numbers:

```
corpus agreement (CRuby vs the Lean semantics): 136/136 agree, 0 disagree

tier 1: 8/8    tier 2: 18/20  tier 3: 6/6    tier 4: 8/9    tier 5: 8/8
tier 6: 6/9    tier 7: 16/16  tier 8: 10/10  tier 9: 10/22  tier 10: 0/6
tier 11: 1/10  tier 12: 4/12
flagged Ty language gaps: 2 (proc-arity-leniency, metaprog-method-missing-splat)
rungs where validate differs from the recorded target: 27
```

All 95 are synthesized by `chk` itself, with nothing trusted anywhere. (This section used
to read "23 validating, of which 14 structural"; the other nine were rungs a certificate
claim answered for. See §Claim-free.) `scripts/run_check_rungs.sh` is the companion number
(also run inline by `run_ratchet.sh`): 95/95 of those cross-checked against the real
semantics, 53/53 negative controls rejected.

Three numbers, and they move for different reasons:

- **"differs from the recorded target" going down** is the climb, tier fraction by tier
  fraction. It counts *both* directions: a rung targeting `true` that answers `false` is
  work to do, and a rung targeting `false` that answers `true` is a soundness bug.
- **"flagged Ty language gaps"** should stay flat unless `Ty.lean`'s grammar itself grows
  (§Ty language gaps) — not something `chk` alone can move.
- **"124/124 agree" should never move.** A disagreement there is a bug in the model or the
  desugarer, not a climb. It is also why a program the *model* cannot run stays out of the
  corpus even when it is ordinary Ruby — see §Frontier item 13.

## Permanent negatives (14 rungs, and only these 14 by design)

Every other rung targets `true`. These don't, each for one of the two reasons
`Ratchet/Corpus.lean` names (`false_reason`). Tier 11 added three: `xc-block-retypes-capture`
and `xc-block-retypes-ivar` (both `unsafe_program`), plus the retargeted
`if-does-not-leak-reassignment` from clink 3. All three are the *same* rule from clink 11 —
a callee may not retype state its caller can still see — and they exist to stop that fix
being reverted. Tier 12 added two more (`narrow-backwards-unsafe`, `narrow-absent-unsafe`),
which exist to constrain a capability that does not exist yet: the first is certified by any
narrowing rule that refines the two branches the wrong way round, the second by any rule that
treats `nilable T` as `T` without a guard.

- **`unsafe_program`** — the program genuinely raises `NoMethodError`/
  `ArgumentError`/`TypeError` when run:
  `bad-plus` (`1 + true`), `unknown-method` (`5.foo_bar_baz` — a made-up method, unlike
  the real `5.zero?` its sibling `unmodeled-builtin-zero-p` uses),
  `fun-wrong-arity`, `fun-body-mismatch`, `fun-unknown-call`, plus tier 9's
  `block-bad-arith` (`[1,2].each { |x| x + "a" }` — TypeError inside a block body,
  which the block wrapper must not launder) and `lambda-arity-mismatch`
  (`->(x){x}.call(1, 2)` — ArgumentError, because lambda arity is strict). A sound `chk` must never
  say `true` for any of these — they are the soundness regression tests.
- **`ty_language_gap`** (2 rungs) — `metaprog-method-missing-splat` and tier 9's
  `proc-arity-leniency`, see next section.

There used to be a third reason, `dishonest_cert`, holding exactly one rung; it went
away with certificates (§Claim-free).

## Ty language gaps

**Three found so far. The first two are the same missing thing: `Ty`'s arrow spine
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

**No `chk` above rung 13** — see §Checker status. Extending it is the active work;
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
