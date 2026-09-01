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

## 2026-08-31 rebuild: real `Expr`/`Ty`, real desugared Ruby

The first version of this harness used a from-scratch, invented `Expr`/`Ty`/corpus —
useful for proving the certificate-checking mechanism out quickly, but disconnected from
real Ruby. This version **ports `Expr` and `Ty` verbatim from the real model**
(`../lean/RubyCore/Syntax.lean`, `../lean/RubyCore/Types/Ty.lean` — see the provenance
note at the top of `Ratchet/Expr.lean`/`Ratchet/Ty.lean` for exactly what was kept vs.
trimmed) and sources every corpus program from **real Ruby run through the real
desugarer** (`harness/desugar-dt/bin/export-json`), not hand-authored ASTs. **Not
ported**: the semantics (`stepFn`/the interpreter) — there is no `eval`/`typeStuck` in
this package yet, only the static checker. That is explicitly deferred, not forgotten;
see §Frontier.

Consequence for the certificate format: since `Expr` derives `BEq` (ported unchanged,
including its docstring's own reason — "added for the certificate language... keyed on
the subterm a claim is about"), the certificate is no longer a parallel type-annotated
shadow tree (what the first version built). It's a **flat list of claims**, each pairing
an actual `Expr` subterm with the `Ty` it's claimed to have, matched against the real
program by structural equality (`Ratchet/Cert.lean`). A claim is needed only where
`chk` cannot synthesize a subterm's type structurally.

## Isolation

Nothing here imports `../lean/RubyCore/`. Own `lakefile.toml`, own `lean-toolchain`
(pinned to the same `v4.32.2` as `../lean/` only because that's the toolchain already on
this machine — there is no dependency). `Expr`/`Ty` are copied text, not linked; if this
package's copy and the real model's ever diverge, that's a deliberate fork to notice and
resolve, not a build error to silently paper over.

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
- **`Ratchet/Validate.lean`** — `chk`, the local type-checker over real `Expr`, and
  `validate : Cert → Expr → Bool`. `chk` handles a small, explicit fragment structurally
  (see §Fragment below) and falls back to `Cert.lookup` for everything else — an
  explicit claim is required, or the program is rejected. This is the
  `Cert -> Expr -> Bool` shape the restart asked for.
- **`corpus/NNN-id.rb` + `corpus/NNN-id.json`** — each rung is real Ruby source (the
  `.rb`, for human reading) plus a generated `.json` (`{id, tier, description, program,
  cert, expect_validate}`) where `program` is a **committed snapshot** of
  `export-json`'s actual output for that `.rb` file, not re-derived live at test time —
  deliberately, per the same norm `certify/`'s own LLM-arm cache follows ("a ratchet
  whose number depends on a live sample is not a ratchet"). Regenerate with
  `python3 scripts/generate_corpus.py`; **never hand-edit the `.json` files** — a claim's
  `expr` field is extracted programmatically from the real desugarer's output
  (`generate_corpus.py`'s `find_node`), never hand-transcribed, so it cannot silently
  drift from what the program actually contains.
- **`Main.lean`** / **`scripts/run_ratchet.sh`** — the runner: loads every corpus entry,
  runs `validate`, and reports per-rung and per-tier results against the recorded
  `expect_validate`. There is no `expect_stuck` check (no interpreter yet).

## The ladder (8 tiers, 89 rungs today)

1. Literals (8 rungs) — `chk` synthesizes all of these directly; no claims needed.
2. Arithmetic/string/bool `send`s (21 rungs) — a small hardcoded builtin dispatch table
   (`builtinSendTy?`), plus the claims escape hatch demonstrated on unmodeled builtins
   (`5.zero?`, `"abc".length`).
3. `var`/`vasgn`/`seq` (6 rungs) — real Ruby scoping (mutable locals, not the `let` of a
   from-scratch toy language).
4. Conditionals (9 rungs) — `if'`/`elsif` chains, including the no-`else` → `nilable`
   case and a deliberately-kept known simplification (see below).
5. Arrays/hashes (10 rungs) — including that indexing (`#[]`) is just a `send`, same as
   everything else in Ruby; the real `Expr` has no dedicated index constructor.
6. Top-level functions (9 rungs) — a `def'`'s signature is a claim on the `def'` node
   itself (an arrow spine); there is no separate `FunCert` format. Includes a
   self-recursive function (`fact`).
7. **Classes (16 rungs) — FRONTIER.** Real, varied class-based Ruby (construction,
   ivars, inheritance, `super`, singleton "factory" methods, instances in
   arrays/hashes) that `chk` has no rule for at all yet: every rung is
   `expect_validate: false`, with empty claims (there is nothing a claim could do for a
   `class'`/`defs`/`super'` node today). See §Frontier.
8. **Modules (10 rungs) — FRONTIER.** Same treatment, for `module'`/`defs self'`.

Run `scripts/run_ratchet.sh` for current numbers:

```
tier 1: 8/8     tier 2: 17/21   tier 3: 5/6    tier 4: 5/9
tier 5: 7/10    tier 6: 5/9     tier 7: 0/16   tier 8: 0/10
expectation mismatches: 0
```

Tiers 1–6 mix well-typed positives with genuinely-ill-typed real Ruby negatives (not
dishonest certificates — with claims no longer annotating *every* node, most of this
fragment has nothing for a certificate to lie about; a bad rung is usually just bad
Ruby, e.g. `1 + true`). Tiers 7–8 are uniformly `0/N`, by design (§Frontier) — that `0`
moving is exactly the signal that classes/modules have been picked up. **"expectation
mismatches: 0" is the number that matters** — it means `validate`'s actual verdict
matches what the generator recorded for every rung. That's the CI gate, not the
per-tier fractions.

## Fragment `chk` currently covers

Literals; `var`/`vasgn`/`vcall` (flat environment, no `VarKind` distinction);
`seq`; `if'` (condition must be exactly `Bool`, branches joined via `joinTy`, no-`else`
wrapped in `nilable`); a hardcoded arithmetic/string/boolean/`to_s` `send` table;
`array` (homogeneous elements only); `hash` (typed as the bare `.cls "Hash"`, no
key/value parameterisation); top-level `def'` + calls dispatched by name, signature
supplied by a claim on the `def'` node, `Param.req` only.

## Known, deliberately-kept simplifications

Not bugs — see `Ratchet/Validate.lean`'s module docstring, restated here with the
corpus rungs that demonstrate each one:

- **`if` does not propagate a branch's reassignments** into the following code — the
  environment after an `if` is the environment from *before* it, not a merge of both
  branches. `041-if-does-not-leak-reassignment.json`: `x = 1; if true; x = "hello"; end;
  x + 1` validates as `Int`, because the checker never sees that the only branch this
  `if` has reassigns `x` to a String. Fixing this needs `SubEnv`-style environment
  merging — deliberately not ported from `Types/Ty.lean` (see §Isolation) until it's
  needed.
- **`if`'s condition must be exactly `Bool`**, not merely truthy — Ruby only treats
  `nil`/`false` as falsy, so `if 1 then ... end` (`044-if-nil-condition.json` is the
  `nil` variant) is real, safe Ruby this checker currently rejects.
- **`==`/`!=` require both sides the same `Ty`** — `021-eq-different-type.json`:
  `1 == "a"` never raises in real Ruby (it just answers `false`), but validate rejects
  it anyway, conservatively.
- **Arrays must be element-homogeneous**, **hashes have no parameterised type at all**
  (unlike the ported `Ty.arrayOf`, there is no `hashOf` — see `Ty.lean`'s module
  docstring for why that's an honest reflection of the real project's own type
  language, not a gap this port introduced) — `047-array-heterogeneous.json`,
  `049-hash-lit.json`.
- **Indexing (`#[]`) is not in the hardcoded builtin table** — real Ruby has no
  dedicated index syntax at the `Expr` level, it's just a `send` like any other method
  call, so `arr[0]`/`h["k"]` need an explicit claim same as any other unmodeled
  builtin (`051`–`054`, mirroring `str-length-with-claim`/`-no-claim`).
- **`send` carrying a block is always rejected**, regardless of claims — blocks are
  semantics-adjacent and explicitly deferred (§Frontier).
- **Classes and modules are not typed at all** — `chk` has no case for `class'`/
  `module'`/`defs`/`super'`/`sclass`, and `.const` is not yet typed as `Ty.clsOf` the
  way the real project's own `Ty` grammar intends. All 26 tier-7/8 rungs are rejected
  regardless of claims (there being nothing a claim could currently do for these
  constructs) — see §Frontier.

## Frontier

In roughly the order that costs least to unlock the most:

1. **Environment merging across `if` branches** (`SubEnv`/a real join over `Env`, not
   just over `Ty`) — closes the biggest of the known simplifications above, and the
   machinery (`SubEnv`/`subEnvB`) already exists, ported-but-not-yet, in the real
   `Types/Ty.lean`.
2. **Optional/rest/keyword/block params** (`Param.opt`/`.rest`/`.key`/`.kwrest`/
   `.block`) — `paramNames`/`buildFunSigs` currently reject any `def'` using them.
3. **Blocks and `yield`** (`Expr.block`, `Expr.yield'`) — the real payoff construct, and
   the first one that needs the interpreter (or at least a model of what `each`/`map`
   actually do) to make good on a claim about a block's body.
4. **Classes and modules** (`Expr.class'`/`Expr.module'`/`Expr.sclass`/`Expr.defs`/
   `Expr.super'`) — tier 7/8's 26 rungs are real class/module-shaped Ruby, ready and
   waiting; what's missing is (a) typing `.const name` as `Ty.clsOf name` rather than
   falling through to `Cert.lookup`, (b) a notion of a class's declared
   fields/methods as data (something like the real project's `Types/Decls.lean`,
   deliberately not ported — see §What is deliberately not built), and (c) dispatch
   rules for `.new`/instance methods/singleton (`self.`) methods keyed off that table,
   including a parent-chain walk for inheritance (`class-inheritance-field`/
   `-override`) and `super'` (`class-super-call`).
5. **The semantics** (`stepFn`, ported from `../lean/RubyCore/Interp/`) — once there is
   one, this package gets back the other half of the old corpus design: does a
   `validate`-certified program actually avoid `NoMethodError`/`ArgumentError`/
   `TypeError` when run? Until then, `validate` is a claim with nothing to check it
   against beyond its own internal consistency.

## What is deliberately not built here

**No soundness theorem.** `../lean/RubyCore/Proof/Cert/Sound.lean`'s `validate_sound` is
the model for what would come next — `validate c p = true → ∀ r, Reachable p r → ¬
typeStuck r` — but that needs the semantics (§Frontier item 5) to even state, let alone
prove.

**No `Types/Decls.lean`-style declaration table.** The real project's checker resolves
`send` against a genuine per-class method table built from the whole program (plus a
prelude). This package's `builtinSendTy?` is a deliberately tiny hardcoded stand-in, and
`buildFunSigs`'s "one claim per top-level `def'`" is the smallest possible analogue for
functions. Growing either into a real declaration table, rather than a longer hardcoded
match, is a design decision to make deliberately when the corpus actually needs it —
not preemptively.

**No `Types/Infer.lean`/`Check.lean` reuse.** This package's `chk` is written from
scratch against the ported `Expr`/`Ty`, not a copy or a wrapper of the real project's
own checker. The point of the restart is to have *our own* small checker whose coverage
is visible and growable one rung at a time.
