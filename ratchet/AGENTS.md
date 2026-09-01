# AGENTS.md — `ratchet/`: a certificate-checking ladder, restarted small

This is a **restart** of the type-checking work, deliberately isolated from `../lean/`
(`RubyCore`) and from `../certify/`/the judgment layer (own `lakefile.toml`/
`lean-toolchain`, no import of `RubyCore`). Those are real, load-bearing, and not being
replaced — see `../type-safety-by-reachability.md` and
`../docs/semantics/certificate-language.md`/`judgment-layer.md` for that work. This
folder exists because that machinery grew by tackling ambitious whole-slice goals
(Homebrew's `version.rb`, Sorbet fragments, `define_method`) before the checker itself
had a graduated coverage ladder to climb. **The idea here: preserve the
certificate-checking architecture, but drive it from a corpus that ratchets up in
complexity one rung at a time, so "how far does `validate` reach today" is always a
single number, not a research question.**

## Checker status: **14 rungs, hand-authored judgment first**

`Ratchet/Validate.lean`'s `validate` is real again, but only over a deliberately tiny
fragment: **tier 1's eight literals plus `+`/`-`/`*`/`/` on `Integer` and `+` on
`String`** — the first 13 rungs of the ladder, which is exactly where the 2026-08-31
(evening) pass stopped on purpose (see the next section). `nested-arith` falls out for
free as a 14th, being nothing but those rules nested.

What is different from the pre-restart version this replaced: the checker is no longer
the specification. `Ratchet/Judge.lean` is — a hand-authored typing judgment with one
constructor per rule — and every rung in the covered fragment has a **derivation term**
on file in `Ratchet/Rungs13.lean` that Lean's kernel checks, plus
`Ratchet/Proof/ChkSound.lean`'s `chk_sound : chk c e = some τ → Judge c e τ` tying the
executable checker back to it. Two numbers now come out of `scripts/run_ratchet.sh`
rather than one — **structural** vs **claim-assisted** — because a rung that validates
only because a certificate claimed its type has not really been climbed by the checker
(see §The claim leaf).

## Semantics status: **imported, and wired up for the covered fragment**

`Semantics/Interp.lean` imports the real `stepFn` (and its whole dependency closure —
`Heap`/`Machine`/`Builtins`/`CRubyNames`/the booted prelude) from `../lean/RubyCore/`
via a local Lake `require`, and provides `Ratchet.Semantics.run`/`typeStuck`/
`resultClassName`/`outcomeLabel` over it — see §Architecture and the file's own docstring
for why this one piece is imported rather than copied, unlike `Expr`/`Ty`.

It is now **wired into the corpus for the 13 rungs the judgment covers**, by the separate
`check13` executable (`Check13.lean`, `scripts/run_check13.sh`) rather than by an
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
field is ever worth adding, given `check13` derives the same information by running the
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
all (`cert_language_gap`, §Cert language gaps) — the one case this reclassification
was designed to surface rather than paper over, per the instruction that prompted it:
if something can't be expressed in the cert, flag it, don't just mark it `false`.

Also added: tier 9, metaprogramming (`method_missing`, class reopening,
`include`/`extend`/`prepend`), deliberately last on the ladder, and the direct
motivation for finding the one language gap above.

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
  accept the illegal lambda. §Cert language gaps.
- **`->(x) { return x * 2 }.call(3)` cannot be written at top level** — the desugarer
  exits 3 on `top-level return`. Wrapped in a method, which is the more honest rung
  anyway: it is inside a method body that lambda-local `return` differs from the proc
  and bare-block reading.

Two rungs already pass claim-assisted (`block-pass-symbol-to-proc`,
`block-sort-by-length`) — both because their claim happens to land on the outermost
send, i.e. the checker is trusting the answer, not computing it. Structural is still
14, and 79 rungs are not yet climbed.

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
4. **`Ratchet/Rungs13.lean` + `Check13.lean` — the confidence.** Thirteen `Rung` records,
   each carrying a hand-written **derivation term** (a wrong `ty` does not compile), plus
   `chk_agrees_with_hand_derivations` — one `rfl` per rung, the `Judge ⇒ chk` direction
   that `chk_sound` does not give. `Check13.lean` then closes the two gaps no proof in
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
  `false` to a `FalseClass`; `Ty` does not distinguish them, so `Check13.lean`'s
  `expectedClasses` maps `.bool` to both. Recorded because it is the one place the
  cross-check has to be *loosened* to pass, and a loosened cross-check should be
  deliberate.

## The claim leaf

`Judge.claim` admits whatever a certificate asserts about a subterm. It is the
certificate architecture's trusted edge and it is **unsound in general** — a cert may
claim anything, including a type for the program's root node, at which point `validate`
answers `true` having checked nothing. That is the intended mechanism (it is exactly how
`unknown-method-with-claim`'s `5.zero?` is meant to certify, and that rung *is* its whole
program), so the fix is not to forbid it but to stop counting it as the same thing:

- `Main.lean` splits each tier into **structural** (re-running `validate` with the
  certificate emptied still succeeds — the checker did the work) and **claim-assisted**
  (it did not). Today: 14 structural, 9 claim-assisted, 23 validating in total.
- All 13 rungs in the hand-authored fragment have an **empty** `cert`, so their
  derivations cannot use the leaf at all. `Rungs13.lean`'s `empty_cert_lookup` states
  that as a theorem, and `Check13.lean` re-checks `cert_empty` against the corpus file,
  so the fragment's confidence does not quietly rest on the one rule with no argument
  behind it.

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
  package for program syntax — a certificate claim's `expr` field is decoded with the
  exact same `Decode.expr`, since it's literally a fragment of the same wire format.
- **`Ratchet/Ty.lean`** — the `Ty` inductive ported verbatim from `RubyCore/Types/Ty.lean`
  (`int`/`bool`/`nilT`/`sym`/`cls`/`any`/`clsOf`/`nilable`/`float`/`arrayOf`/`union`/
  `arrow0`/`arrowCons`), plus the pure helpers (`arrowOf`/`arrowParts?`/`subTy`/`subTys`/
  `joinTy`/`mkNilable`/`Env`/`envGet?`/`envSet`). **Not ported**: the metatheory around
  them (`subTy_trans`, `SubEnv`/`subEnvB` and their proofs, lambda-capture pinning,
  `FrameCtx`) — no soundness theorem needs them yet (see the file's own docstring for
  the rationale, and §What is deliberately not built here below).
- **`Ratchet/Cert.lean`** — `Claim := { expr : Expr, ty : Ty }`, `Cert := List Claim`,
  and `Cert.lookup : Cert → Expr → Option Ty` (find by `==`). See the 2026-08-31 note
  above for why this replaced a shadow-AST design.
- **`Ratchet/Judge.lean`** — `Judge : Cert → Expr → Ty → Prop` (mutual with `JudgeAll`
  over an argument list) and `PrimSig`, the primitive-signature table as a relation. The
  **specification**: what `validate` is deciding, one human-checkable constructor at a
  time. Covers rungs 1–13 and nothing else, on purpose — see §2026-08-31 (evening).
- **`Ratchet/Validate.lean`** — `primSig?`, `chk`/`chkAll`, and
  `validate : Cert → Expr → Bool` (`= (chk c p).isSome`). The decision procedure for
  `Judge`'s fragment, with `Cert.lookup` as a uniform fallback at every node kind. This
  is the `Cert -> Expr -> Bool` shape the restart asked for.
- **`Ratchet/Proof/ChkSound.lean`** — `primSig?_sound`, `chk_sound`/`chkAll_sound`,
  `validate_sound_syntactic`. Axiom-clean; the file ends with its own `#print axioms`.
- **`Ratchet/Rungs13.lean`** — the 13 rungs as `Rung` records carrying hand-written
  `Judge` derivation terms, plus `chk_agrees_with_hand_derivations` (one `rfl` per rung)
  and `empty_cert_lookup`.
- **`corpus/NNN-id.rb` + `corpus/NNN-id.json`** — each rung is real Ruby source (the
  `.rb`, for human reading) plus a generated `.json` (`{id, tier, description, program,
  cert, expect_validate, false_reason}`) where `program` is a **committed snapshot** of
  `export-json`'s actual output for that `.rb` file, not re-derived live at test time —
  deliberately, per the same norm `certify/`'s own LLM-arm cache follows ("a ratchet
  whose number depends on a live sample is not a ratchet"). Regenerate with
  `python3 scripts/generate_corpus.py`; **never hand-edit the `.json` files** — a claim's
  `expr` field is extracted programmatically from the real desugarer's output
  (`generate_corpus.py`'s `find_node`/`find_within`), never hand-transcribed, so it
  cannot silently drift from what the program actually contains. `expect_validate` is a
  **target**, not necessarily what `validate` answers today — `true` for every rung
  except the seven named in §Permanent negatives, each with a `false_reason`
  (`"unsafe_program"`/`"dishonest_cert"`/`"cert_language_gap"`) explaining why.
- **`Main.lean`** / **`scripts/run_ratchet.sh`** — the runner: loads every corpus entry,
  runs `validate`, and reports per-rung and per-tier results against the recorded
  `expect_validate` — each tier split **structural / claim-assisted** (§The claim leaf) —
  a dedicated always-shown list of `cert_language_gap` rungs (§Cert language gaps), plus
  a count of rungs where today's answer differs from the target (still large, by design —
  see §Checker status). `Main.lean` imports `Ratchet.Rungs13` but not `Semantics/`: the
  ratchet's headline number stays a pure statement about `validate`.
- **`Check13.lean`** / **`scripts/run_check13.sh`** (the `check13` exe) — the evidence
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

## The ladder (10 tiers, 114 rungs, 14 climbed structurally)

**Every rung's target is `expect_validate = true`, with exactly ten, named
exceptions** (§Permanent negatives below) — see the 2026-08-31 (later) note for why
this is stricter than the first cut of this corpus was, and `Ratchet/Corpus.lean`'s
module docstring for the three reasons a rung is allowed to target `false` at all.

1. Literals (8 rungs) — every one of these should be synthesizable with no claims at
   all once `chk` exists.
2. Arithmetic/string/bool `send`s (20 rungs) — wants a small hardcoded builtin dispatch
   table, plus the claims escape hatch demonstrated on unmodeled builtins (`5.zero?`,
   `"abc".length`) and on a builtin the hardcoded table is deliberately *not* widened
   for (`1 == "a"` — see §Design notes).
3. `var`/`vasgn`/`seq` (6 rungs) — real Ruby scoping (mutable locals, not the `let` of a
   from-scratch toy language), including the NameError-is-not-a-type-error subtlety
   (`bare-undeclared-var`, §Design notes).
4. Conditionals (9 rungs) — `if'`/`elsif` chains, including a no-`else` → `nilable`
   case, branch-mismatched `if`s certified via `Ty.union` claims, and a real,
   deliberately-recorded corner case (see §Design notes).
5. Arrays/hashes (8 rungs) — including that indexing (`#[]`) is just a `send`, same as
   everything else in Ruby; the real `Expr` has no dedicated index constructor.
6. Top-level functions (9 rungs) — wants a `def'`'s signature declared as a claim on the
   `def'` node itself (an arrow spine); no separate `FunCert` format needed. Includes a
   self-recursive function (`fact`).
7. **Classes (16 rungs).** Real, varied class-based Ruby (construction, ivars,
   inheritance, `super`, singleton "factory" methods, instances in arrays/hashes),
   each with real arrow-spine claims on every `def'`/`defs` node plus by-name ivar-read
   claims — see §Architecture's `Cert.lean` note and §Design notes for the dispatch
   machinery these claims assume exists.
8. **Modules (10 rungs).** Same claim shape, for `module'`/`defs self'`.
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
   (`def apply(f, v)`), and lambda-local `return`. Claims are the same arrow spine
   `def'` nodes get, so 19 of 22 target `true`; the three that don't are the tier's
   real findings — `block-bad-arith` and `lambda-arity-mismatch` (genuinely raising
   programs) and `proc-arity-leniency` (§Cert language gaps).
10. **Metaprogramming (6 rungs) — LAST on the ladder, as intended.** `method_missing`,
   class reopening, and `include`/`extend`/`prepend`. Five of six are ordinary safe
   Ruby with real claims (§Design notes has the dispatch subtleties: self-context
   `vcall` resolution, mixin ancestry, prepend-ordered MRO with `super`, a
   method_missing fallback route). The sixth
   (`metaprog-method-missing-splat`) is one of this ladder's two found
   **cert_language_gaps** — see §Cert language gaps.

Run `scripts/run_ratchet.sh` for current numbers:

```
tier 1: 8/8 (8 structural)     tier 2: 9/20 (6 structural, 3 claim-assisted)
tier 3: 1/6 (0, 1)             tier 4: 2/9 (0, 2)          tier 5: 3/8 (0, 3)
tier 6: 0/9    tier 7: 0/16    tier 8: 0/10
tier 9: 2/22 (0 structural, 2 claim-assisted)                tier 10: 0/6
flagged cert language gaps: 2 (proc-arity-leniency, metaprog-method-missing-splat)
rungs not yet climbed: 79
```

Read the **structural** column, not the total: a claim-assisted rung validated because a
certificate asserted a type, and a claim is trusted (§The claim leaf). Structural is 14 —
tier 1's eight, plus `add`/`sub`/`mul`/`div`/`str-concat` and `nested-arith`.
`scripts/run_check13.sh` is the companion number: 13/13 of those cross-checked against
the real semantics, 7/7 negative controls rejected.

The number to watch as `chk` grows is **"rungs not yet climbed" going down**, tier
fraction by tier fraction. The "flagged cert language gaps" count is a *different*
number: it should stay flat unless `Ty.lean`'s grammar itself grows (see §Cert language
gaps) — it is not something `chk` alone can move.

## Permanent negatives (10 rungs, and only these 10 by design)

Every other rung targets `true`. These ten don't, each for one of the three reasons
`Ratchet/Corpus.lean` names (`false_reason`):

- **`unsafe_program`** (7 rungs) — the program genuinely raises `NoMethodError`/
  `ArgumentError`/`TypeError` when run, no matter what any certificate claims:
  `bad-plus` (`1 + true`), `unknown-method-no-claim` (`5.foo_bar_baz` — a made-up
  method, unlike the real `5.zero?` its sibling `unknown-method-with-claim` uses),
  `fun-wrong-arity`, `fun-body-mismatch`, `fun-unknown-call`, plus tier 9's
  `block-bad-arith` (`[1,2].each { |x| x + "a" }` — TypeError inside a block body,
  which the block wrapper must not launder) and `lambda-arity-mismatch`
  (`->(x){x}.call(1, 2)` — ArgumentError, because lambda arity is strict). A sound `chk` must never
  say `true` for any of these — they are the soundness regression tests.
- **`dishonest_cert`** (1 rung) — `fun-dishonest-return-claim`: `get5`'s body really
  returns `Int` and running it is completely safe, but *this certificate* claims its
  return type is `an instance of String`, which contradicts its own body. Rejecting a
  self-inconsistent certificate is independent of the program's actual safety — the
  point is that a checker which let a cert's claims disagree with each other would be
  meaningless, not that this particular Ruby is unsafe.
- **`cert_language_gap`** (2 rungs) — `metaprog-method-missing-splat` and tier 9's
  `proc-arity-leniency`, see next section.

## Cert language gaps

**Two found so far, both the same missing thing: `Ty`'s arrow spine
(`arrow0`/`arrowCons`) has no optional-or-rest arity constructor.** `def method_missing(name, *args)` — the idiomatic shape — has a
parameter list no `Ty` value can honestly describe: not "no `chk` rule for it yet" but
"no claim, however clever, states the truth without lying about arity." A claim
approximating it as `arrow_of([Sym], ...)` would silently accept the zero-extra-args
call site in the corpus while being unsound the moment a caller passes any extra
arguments. `metaprog-method-missing-fixed-arity` sits right next to it in tier 10 with
the *same* dispatch shape and no splat, and validates fine (aspirationally) — proving
the gap is specifically the rest parameter, not `method_missing` dispatch generally.

Tier 9's **`proc-arity-leniency`** reaches the same gap from the other direction:
`proc { |x, y| x }.call(1)` is legal Ruby (a proc pads missing params with nil and
drops extras), but the only claimable type for that block, `arrow_of([Int, Int], Int)`,
says the call site is wrong; weakening the second param to `nilable Int` still cannot
say "…and may be absent entirely", nor that a third argument would also be fine. Its
strict sibling `lambda-arity-mismatch` is a permanent `unsafe_program` for the *same*
call shape — which is the point: the arrow spine cannot distinguish the two arity
disciplines, so it either rejects the legal proc or accepts the illegal lambda.

Fixing both needs a `Ty` extension — an `arrowRest (rest ret : Ty)` spine terminator, or
modeling `*args` as `arrayOf Ty` — decided deliberately, not smuggled in as a special
case of something else. Until then, `Main.lean`'s runner always prints a "flagged:
cert language gaps" section (independent of pass/fail) so this doesn't quietly
disappear into a wall of `false`s the way it would have under the old philosophy.
**Watch for more of these as the ladder grows** — this section is the place to record
each one; a "cert_language_gap" `false_reason` should always come with an entry here
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
assumes that version didn't have, plus everything tiers 7–9 need beyond it:

- **Every node kind should have a claim-fallback, not just `send`/`vcall`.** The
  cleared version only fell back to `Cert.lookup` for sends; `if'`/`array` had no
  escape hatch at all. `if-branch-mismatch`/`elsif-chain-mismatch`/
  `array-heterogeneous` all now target `true` *via a claim* on the mismatched node
  (a `Ty.union`, or `arrayOf(Ty.any)`) — meaning a rebuilt `chk` should try structural
  typing first at *every* node kind, and fall back to `Cert.lookup` uniformly on
  failure, not case by case.
- **"Type-safe" means "never `NoMethodError`/`ArgumentError`/`TypeError`", not
  "never raises" and not "the condition/branches are syntactically uniform".** Three
  rungs only make sense under this precise reading: `bare-undeclared-var` (raises
  `NameError`, outside the family, so `Ty.any` is an honest claim — nothing downstream
  depends on its value); `if-condition-not-bool`/`if-nil-condition` (Ruby's `if` never
  raises over its condition's type — a rebuilt `if'` rule should join
  `(thenTy, elseTy)` unconditionally, with no `Bool`-only restriction at all, which
  wasn't just incomplete before, it was actively wrong); `eq-different-type` (`==`
  never raises for unrelated types, so requiring both sides the same `Ty` was a
  conservative *choice* in the builtin table, not a necessity — the claims escape
  hatch is enough to certify it without loosening the hardcoded rule itself).
- **Ivar types are claimed by name, globally, not scoped per class** — a documented
  simplification, not a `Ty` gap: `.var .ivar "@x"` claims apply wherever `@x` is read
  in *any* class. Fine for this corpus (no two classes reuse an ivar name with
  different types), a real limitation to fix before this scales.
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
  one (`metaprog-method-missing-fixed-arity`). See §Cert language gaps for why the
  idiomatic splat-arity version doesn't validate yet regardless.

## Frontier

The full climb, in roughly the order that costs least to unlock the most:

0. **Continue the tier 2–6 climb from rung 14** (§Design notes) — the fragment through
   rung 13 is done, judgment-first (§2026-08-31 (evening)); next up in corpus order is
   comparison/boolean/`to_s` sends (`cmp-lt` … `nil-eq-nil`), then tier 3's `var`/`vasgn`/
   `seq` — which is where `Judge` grows its `Env` and every rule's shape changes, so it is
   the one step worth designing before writing. Keep the discipline that produced rungs
   1–13: a rule in `Judge.lean` before a case in `chk`, a derivation term per rung in
   `Rungs13.lean`'s successor, and a `check13` row cross-checking it against the real
   semantics — plus negative controls for every new `PrimSig` row, since confirming rungs
   pass never shows a signature is too generous.
1. **Environment merging across `if` branches** (`SubEnv`/a real join over `Env`, not
   just over `Ty`) — the one remaining simplification `if-does-not-leak-reassignment`
   still needs; the machinery (`SubEnv`/`subEnvB`) already exists, ported-but-not-yet,
   in the real `Types/Ty.lean`.
2. **Optional/rest/keyword/block params** (`Param.opt`/`.rest`/`.key`/`.kwrest`/
   `.block`) — the cleared implementation rejected any `def'` using them, and tier 10's
   `metaprog-method-missing-splat` (with tier 9's `proc-arity-leniency`) needs this
   *and* the `Ty` extension in §Cert language gaps together before it can validate.
   `Param.block` is needed sooner than the rest: tier 9's `block-param-ampersand`
   (`def run(&b)`) is otherwise ordinary safe Ruby.
3. **Blocks and `yield`** (`Expr.block`, `Expr.yield'`) — the real payoff construct, and
   the first one that needs the interpreter (or at least a model of what `each`/`map`
   actually do) to make good on a claim about a block's body. **Tier 9 is now the
   corpus demand for this**, 22 rungs of it, ordered so the first (`lambda { 1 }`,
   `arrow_of([], Int)`) is reachable long before the last.
4. **Classes and modules**: a declaration table (something like the real project's
   `Types/Decls.lean`, deliberately not ported — see §What is deliberately not built)
   keyed by owner name, built from every `def'`/`defs` claim nested in every
   `class'`/`module'` node (accumulating across reopenings for free); `.const name`
   typed `Ty.clsOf name`; `.new` dispatch (default constructor or the claimed
   `initialize`); instance/singleton `vcall`/`send` dispatch through `self`'s type
   (§Design notes); a parent-chain *and* mixin-aware ancestor walk for inheritance,
   `include`/`extend`/`prepend`, and `super'`/`zsuper`. Tiers 7–9 (32 rungs total) are
   real Ruby, claimed and waiting, ready to certify the moment this lands — none of it
   needs a new `Ty` constructor except the one item below.
5. **Extend `Ty` with a rest/vararg arrow constructor** (§Cert language gaps) — the one
   `Ty`-grammar change this ladder has found a concrete need for.
6. **Extend the semantic cross-check past rung 13.** Mostly done for the covered
   fragment (§Semantics status, `Check13.lean`) and it grows a row at a time as `chk`
   does; what is still open is (a) the real theorem — `validate c p = true → ∀ r,
   Reachable p r → ¬ typeStuck r`, which needs the semantics *in the statement*, not just
   in a test harness, and would be the point at which `Judge`'s constructors stop being
   assertions and start being lemmas — and (b) whether a recorded `expect_stuck` field
   per rung earns its keep given `check13` derives the same fact by running the program.
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
item 6), and until then `check13`'s per-rung execution is evidence, not proof.

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
