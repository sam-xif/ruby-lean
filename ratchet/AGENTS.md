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

## Checker status: **stub**

`Ratchet/Validate.lean`'s `validate` currently always returns `false`. Every checking
rule that used to live there (`chk`, the builtin `send` dispatch table, the top-level
function-signature collection, `defsOk`) was deliberately cleared out — see the git
history (`git log --follow -- Ratchet/Validate.lean`, commit `5a9f1ad` has the last
working version) for a reference if it's useful, but the point of clearing it is that
the corpus below is now the *target* to rebuild against, not a description of current
behavior. Running `scripts/run_ratchet.sh` today reports `0/N` "certified well-typed"
on every tier and a large "rungs not yet climbed" count — that is the honest, expected
state of a stub, not a bug. §Design notes below preserves what the cleared
implementation got right, as guidance for rebuilding it (possibly differently) rather
than as a spec to reproduce exactly.

## Semantics status: **imported, not yet wired up**

`Semantics/Interp.lean` imports the real `stepFn` (and its whole dependency closure —
`Heap`/`Machine`/`Builtins`/`CRubyNames`/the booted prelude) from `../lean/RubyCore/`
via a local Lake `require`, and provides `Ratchet.Semantics.run`/`typeStuck` over it —
see §Architecture and the file's own docstring for why this one piece is imported
rather than copied, unlike `Expr`/`Ty`. It is real and it works (smoke-tested: `1 +
"a"` really does raise a `TypeError`, `typeStuck = true`; `1/0` raises
`ZeroDivisionError`, `typeStuck = false`, matching the real project's own
`NoMethodError ∪ ArgumentError ∪ TypeError` family exactly). What it is **not** yet is
*wired into the corpus*: there is no `expect_stuck` field on a corpus rung, and
`Main.lean` never calls `Semantics.run`. That wiring — and deciding whether to decode a
rung's `program` a second time via the real `RubyCore.Decode.program` for this purpose,
or something else — is left for when `Ratchet/Validate.lean`'s `chk` exists again to
have something worth cross-checking against (see §Frontier).

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
- **`Ratchet/Validate.lean`** — `validate : Cert → Expr → Bool`. **Currently a stub**
  (`fun _ _ => false`) — see §Checker status. When rebuilt, this is where `chk`, a local
  type-checker over real `Expr` that falls back to `Cert.lookup` for anything it can't
  synthesize structurally, belongs. This is the `Cert -> Expr -> Bool` shape the restart
  asked for.
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
  `expect_validate`, a dedicated always-shown list of `cert_language_gap` rungs
  (§Cert language gaps), plus a count of rungs where today's answer differs from the
  target (currently large, by design — see §Checker status). There is no `expect_stuck`
  check yet — `Main.lean` does not import `Semantics/` (see next bullet).
- **`Semantics/Interp.lean`** — `Ratchet.Semantics.run`/`typeStuck`, over the real,
  **imported** (not copied) `RubyCore.Interp.stepFn` and its full dependency closure —
  see §Semantics status. The one place this package's `lakefile.toml` declares a
  `require` on `../lean`.

## The ladder (9 tiers, 92 rungs, all currently unclimbed)

**Every rung's target is `expect_validate = true`, with exactly seven, named
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
9. **Metaprogramming (6 rungs) — LAST on the ladder, as intended.** `method_missing`,
   class reopening, and `include`/`extend`/`prepend`. Five of six are ordinary safe
   Ruby with real claims (§Design notes has the dispatch subtleties: self-context
   `vcall` resolution, mixin ancestry, prepend-ordered MRO with `super`, a
   method_missing fallback route). The sixth
   (`metaprog-method-missing-splat`) is this ladder's one found
   **cert_language_gap** — see §Cert language gaps.

Run `scripts/run_ratchet.sh` for current numbers:

```
tier 1: 0/8    tier 2: 0/20   tier 3: 0/6   tier 4: 0/9
tier 5: 0/8    tier 6: 0/9    tier 7: 0/16  tier 8: 0/10  tier 9: 0/6
flagged cert language gaps: 1 (metaprog-method-missing-splat)
rungs not yet climbed: 85
```

(The 85, not 92: the 7 rungs whose `expect_validate` is permanently `false` — see
§Permanent negatives — trivially agree with a stub that always answers `false`.) The
number to watch as `chk` is rebuilt is **"rungs not yet climbed" going down**, tier
fraction by tier fraction, not a single jump back to `0`. The "flagged cert language
gaps" count is a *different* number: it should stay flat unless `Ty.lean`'s grammar
itself grows (see §Cert language gaps) — it is not something `chk` alone can move.

## Permanent negatives (7 rungs, and only these 7 by design)

Every other rung targets `true`. These seven don't, each for one of the three reasons
`Ratchet/Corpus.lean` names (`false_reason`):

- **`unsafe_program`** (5 rungs) — the program genuinely raises `NoMethodError`/
  `ArgumentError`/`TypeError` when run, no matter what any certificate claims:
  `bad-plus` (`1 + true`), `unknown-method-no-claim` (`5.foo_bar_baz` — a made-up
  method, unlike the real `5.zero?` its sibling `unknown-method-with-claim` uses),
  `fun-wrong-arity`, `fun-body-mismatch`, `fun-unknown-call`. A sound `chk` must never
  say `true` for any of these — they are the soundness regression tests.
- **`dishonest_cert`** (1 rung) — `fun-dishonest-return-claim`: `get5`'s body really
  returns `Int` and running it is completely safe, but *this certificate* claims its
  return type is `an instance of String`, which contradicts its own body. Rejecting a
  self-inconsistent certificate is independent of the program's actual safety — the
  point is that a checker which let a cert's claims disagree with each other would be
  meaningless, not that this particular Ruby is unsafe.
- **`cert_language_gap`** (1 rung) — `metaprog-method-missing-splat`, see next section.

## Cert language gaps

**One found so far: `Ty`'s arrow spine (`arrow0`/`arrowCons`) has no vararg/rest-arity
constructor.** `def method_missing(name, *args)` — the idiomatic shape — has a
parameter list no `Ty` value can honestly describe: not "no `chk` rule for it yet" but
"no claim, however clever, states the truth without lying about arity." A claim
approximating it as `arrow_of([Sym], ...)` would silently accept the zero-extra-args
call site in the corpus while being unsound the moment a caller passes any extra
arguments. `metaprog-method-missing-fixed-arity` sits right next to it in tier 9 with
the *same* dispatch shape and no splat, and validates fine (aspirationally) — proving
the gap is specifically the rest parameter, not `method_missing` dispatch generally.

Fixing it needs a `Ty` extension — an `arrowRest (rest ret : Ty)` spine terminator, or
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

0. **Rebuild the tier 1–6 fragment** (§Design notes) — literals through top-level
   functions, with the two design principles (uniform claim-fallback, the precise
   reading of "type-safe") applied from the start rather than retrofitted.
1. **Environment merging across `if` branches** (`SubEnv`/a real join over `Env`, not
   just over `Ty`) — the one remaining simplification `if-does-not-leak-reassignment`
   still needs; the machinery (`SubEnv`/`subEnvB`) already exists, ported-but-not-yet,
   in the real `Types/Ty.lean`.
2. **Optional/rest/keyword/block params** (`Param.opt`/`.rest`/`.key`/`.kwrest`/
   `.block`) — the cleared implementation rejected any `def'` using them, and tier 9's
   `metaprog-method-missing-splat` needs this *and* the `Ty` extension in §Cert
   language gaps together before it can validate.
3. **Blocks and `yield`** (`Expr.block`, `Expr.yield'`) — the real payoff construct, and
   the first one that needs the interpreter (or at least a model of what `each`/`map`
   actually do) to make good on a claim about a block's body.
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
6. **Wire the semantics into the corpus.** The semantics itself is no longer missing —
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

**No `chk` at all right now** — see §Checker status. This is the active thing to build;
everything below is about what its eventual design should and shouldn't include.

**No soundness theorem.** `../lean/RubyCore/Proof/Cert/Sound.lean`'s `validate_sound` is
the model for what would come next — `validate c p = true → ∀ r, Reachable p r → ¬
typeStuck r` — but that needs the semantics (§Frontier item 6) to even state, let alone
prove.

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
