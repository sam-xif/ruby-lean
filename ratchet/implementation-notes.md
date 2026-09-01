# implementation-notes.md — non-trivial choices, one clink at a time

Running log of the design decisions behind each ratchet advance that were *not* forced.
`AGENTS.md` says what the package is; this file says why the parts that could have gone
another way went the way they did. Newest last.

---

## Clink 1 (2026-08-31) — tier 2's remaining `send` rungs: 14 → 24

Rungs added: `cmp-lt`, `cmp-le`, `cmp-ge`, `not-expr`, `to-s-call`,
`unmodeled-builtin-zero-p`, `str-length`, `eq-same-type`, `eq-different-type`,
`nil-eq-nil` — plus `nested-arith`, which `chk` already answered but which had no hand
derivation on file. Tier 2 goes 6/20 → 16/20.

**Why exactly these ten and not all of tier 2.** The tier's two remaining non-negative
rungs are `bool-and` (`true && false`) and `bool-or`. Ruby's `&&`/`||` are *not* sends:
the desugarer emits

```
seq (vasgn local __dt_t1 (true)) (if (var local __dt_t1) (false) (var local __dt_t1))
```

— a temporary local, a `seq` and an `if`. So `&&` is a tier-3 + tier-4 construct wearing
a tier-2 costume, and typing it needs `Env`, which every rule's shape changes for. Left
for the next clink deliberately rather than smuggling in half an environment.

**The four new rule shapes, and what each one claims.** The interesting content of this
clink is entirely in `PrimSig`'s new rows; each is a different *kind* of assertion about
the semantics, which is why they are documented one at a time in `Judge.lean` rather than
as a table:

1. **Comparisons** (`<`, `<=`, `>`, `>=` on `Integer`) — result `Bool`, argument still
   constrained to `.int`. The constraint is load-bearing in the same way `strAdd`'s is:
   `1 < "a"` raises `ArgumentError` ("comparison of Integer with String failed"), which
   is *inside* the NoMethodError/ArgumentError/TypeError family this ladder calls
   type-stuck. `>` is admitted with no rung asking for it, because the soundness
   argument for it is character-for-character `<`'s; that is the one place in this clink
   where a row is not rung-driven, and it is noted here so it is a choice rather than a
   drift.
2. **Nullary total queries** (`Integer#to_s`, `Integer#zero?`, `String#length`) —
   constrain the receiver, nothing else. `to_s` is *zero-arg only*: `5.to_s(2)` is legal
   Ruby with a different signature, and admitting `[.int]` there would have been a guess,
   so it is a negative control instead.
3. **`!`** — the point of the rung is syntactic, not semantic: `!true` desugars to
   `send (tru) "!" []`, an ordinary send with an empty argument list. So Ruby's unary
   operators need **no new `Expr` node and no new rule shape**, only a `PrimSig` row.
   Kept narrow to a `.bool` receiver even though `!` is total on *every* Ruby object,
   because the general rule needs `.any` on the receiver and no rung asks for it.
4. **`==`** — the first rule in this package that is **polymorphic in an argument type**.

**`EqSafe`: why `==` got a side condition instead of a wildcard.** `AGENTS.md` §Design
notes demands `Object#== : (any) → Bool`, because `1 == "a"` is safe Ruby returning
`false` and a rule requiring matching operand types would reject it for no semantic
reason. But writing `PrimSig σ "==" [τ] .bool` for *all* `σ` would be a rule no rung could
ever falsify: `σ` ranges over `Ty`, including `.any` (which also denotes a `BasicObject`)
and the arrow types. So the argument is unconstrained and the **receiver** carries a
six-constructor `EqSafe` side condition (`int`/`float`/`bool`/`nilT`/`sym`/`cls _`), each
naming a class that really does inherit or override a total `==`. `eqSafe?` is its
decidable twin, tied back by `eqSafe?_sound`.

This is the ladder's first *conditional* `PrimSig` row, and it changes `primSig?`'s shape:
the `==` arm is a guarded match (`if eqSafe? σ`) sitting **first** in the table, before the
receiver-keyed rows, since it is keyed on the method name and an arbitrary receiver.
`primSig?_sound` correspondingly grows a nested `split` for that arm; the remaining rows
are still discharged by one `injection`/`subst` and a `first | exact .row` list.

**Negative controls for the new rows.** Per the standing rule that confirming rungs pass
never shows a signature is too generous, six controls were added to `CheckRungs.lean`:
`1 < "a"`, `1.length`, `nil.zero?` (all three genuinely raise — sound rejections), and
`!nil`, `"a" < "b"`, `5.to_s(2)` (all three safe — conservative rejections, printed as
such). `1.zero?` was retired as a control because it is now a rung.

`PrimSig.objEq` deliberately has **no sound-rejection control**, and that is recorded in
`CheckRungs.lean` rather than papered over: `==` really is total on every receiver
`EqSafe` admits, so no neighbouring `==` program in this fragment raises. What constrains
the rule is `EqSafe`, and violating it requires a `Ty` (`.any`, an arrow) that no
expression in today's fragment synthesizes — so the control that would probe it cannot be
written yet. Worth revisiting at the rung that first synthesizes `.any`.

**Renames.** `Ratchet/Rungs13.lean` → `Ratchet/Rungs.lean`, `Check13.lean` →
`CheckRungs.lean`, the `check13` exe → `checkrungs`, `scripts/run_check13.sh` →
`scripts/run_check_rungs.sh`, `rungs13` → `rungs`, `validate_all_13` →
`validate_all_rungs`. The "13" was baked into five filenames and would have been wrong
after every clink. Done now, while the churn is small.

**`run_ratchet.sh` now runs `checkrungs` too**, between the agreement gate and the ladder,
so one command covers all three legs (agreement → evidence → ladder). The ladder's own
number stays a pure statement about `validate`; the evidence just prints above it.

State after this clink: **24 rungs climbed**, 24/24 cross-checked against the real
semantics, 12/12 negative controls rejected, 114/114 corpus agreement with CRuby,
`chk_sound`/`validate_sound_syntactic` axiom-clean (`propext`, `Quot.sound`).

---

## Clink 2 (2026-08-31) — tier 3: the environment, threaded — 24 → 30

Rungs added: all six of tier 3 (`simple-assign`, `reassign-same-type`,
`reassign-different-type`, `bare-undeclared-var`, `seq-multiple-stmts`,
`assignment-chain`). Tier 3 goes 0/6 → 6/6.

This is the shape change `AGENTS.md` §Frontier item 0 flagged as "worth designing before
writing", so the design is the whole content of the clink.

**`Judge Γ e τ Γ'` — input *and* output environment.** The obvious move is to add a
context parameter and stop: `Judge Γ e τ`. That does not work here, because an
assignment is an **expression**, not a declaration form: `x = 1` has a value (`1`) *and*
an effect on what the next expression sees. With only an input context, the `seq` rule
would have to special-case `vasgn` as a statement head, which is both a lie about the
grammar (`y = (x = 1) + 1` is legal) and a rule that would need rewriting the moment a
`vasgn` shows up anywhere else. So the judgment threads: `Judge Γ e τ Γ'` reads "in `Γ`,
`e` synthesizes `τ` and leaves `Γ'`".

The cost is that *every* rule grew two indices, including tier 1's literals (`Judge Γ
(.int n) .int Γ`). The benefit shows up in two places beyond `vasgn`:

- **`prim` threads `Γ → Γ₁ → Γ₂`** across receiver then arguments, rather than typing
  all three parts in the same `Γ`. That is not decoration: Ruby evaluates the receiver
  first, then arguments left to right, and any of them may assign. Getting this wrong
  would be invisible on today's corpus and wrong on `f(x = 1) + x`.
- **`JudgeSeq` is a separate inductive**, not a `List` fold, so "a sequence is non-empty
  and its type is the *last* statement's" is structural. Every earlier statement still
  has to type — a statement whose value nobody reads can still be type-stuck.

**`Rung` gained an `outEnv` field**, and the corpus derivations state it explicitly
(`[("x", .int), ("y", .int)]`). It could have been existentially quantified; making it
explicit means a derivation with a right result type but a wrong environment does not
compile. `chk_agrees_with_hand_derivations` compares the pair.

**Locals are not single-typed, and no rule pretends otherwise.** `reassign-different-type`
(`x = 1; x = true; x`) types at `Bool` because `envSet` overwrites. There is deliberately
no join, no union and no "must be compatible" side condition on `vasgn`: a checker that
rejected this rung, or that widened `x` to `Int | Bool`, would be describing a different
language. Recorded because it is the one place where the *absence* of a rule is the
design.

**`bare-undeclared-var`: the rung that nearly introduced an unsound rule.** `x` alone
desugars to `vcall "x"`, and the tempting rule is:

> a bare identifier has type `.any`, because if it is unbound it raises `NameError`, and
> `NameError` is outside the `NoMethodError`/`ArgumentError`/`TypeError` family.

Every clause of that is true and the rule is still **unsound**, because a bare identifier
need not be unbound. `proc` and `lambda` are private `Kernel` methods; evaluating either
with no block raises `ArgumentError` — verified directly against CRuby 4.x — which is
squarely inside the family. `puts`, `rand`, `raise`, `loop` are reachable the same way.

So the rule is gated on a table, `BareNameError : String → Prop`, with exactly one row
(`x`), in precise analogy to `PrimSig`: a name is admitted when someone has checked that
it resolves to nothing. Two further properties of the *current* judgment are what make
even that one row sound, and both are written into the rule's docstring as things to
revisit:

1. **No rule types a `def'`.** A program that defines `x` and then calls it bare cannot
   be judged at all, so `bareName` cannot launder a user-defined method with a
   type-stuck body. Tier 6 must therefore either delete this rule or gate it on the
   program's declaration table.
2. **Top-level `self`.** Inside a method or class body a bare name resolves against a
   different receiver, and the judgment has no `self`.

`.any` as the result type is safe for a separate reason worth stating: no `PrimSig` row
has `.any` as its receiver and `.any` is not `EqSafe`, so nothing downstream can consume
the value. The type is inert by construction, not by luck.

**Cross-checking a `.any` claim.** `CheckRungs.lean` compares a derived `Ty` to the class
the semantics produced; `.any` names no class. Rather than inventing an extensional
reading, `semOk` is simply `true` for `.any` and the row's content reduces to
`¬typeStuck` — documented in place, including the cost (a rung claiming `.any` for a
program that *does* return a value would pass vacuously). Today exactly one rung does
this, and it returns no value at all.

**Three new controls, and a third verdict.** `proc`, `lambda` (bare names that are *not*
unbound) and `y` (unbound but not a table row). Running the first two exposed a gap in
the control harness: `RubyCore` does not model block-less `proc`/`lambda` and answers
`unsupported`, which the harness was reporting as "conservative: safe, no rule yet" —
i.e. calling a program safe because the model declined to run it. Added a distinct
verdict for `unsupported`/`outOfFuel` so that can never happen silently. The controls
still do their job: CRuby is the ground truth that refutes the blanket rule, and the
model's silence is not evidence for it.

State after this clink: **30 rungs climbed** (tiers 1–3 complete except `bool-and`/
`bool-or`, which need tier 4's `if`), 30/30 cross-checked against the real semantics,
15/15 negative controls rejected, `chk_sound`/`chkAll_sound`/`chkSeq_sound`/
`validate_sound_syntactic` axiom-clean.

---

## Clink 3 (2026-09-01) — tier 4's `if`, and the two rungs it unblocks: 30 → 40

Rungs added: `if-true-branch`, `if-no-else`, `if-condition-not-bool`,
`if-branch-mismatch`, `elsif-chain-mismatch`, `if-nil-condition`, `nested-if`,
`elsif-chain` — the whole of tier 4 except `if-does-not-leak-reassignment`, which turns
out to be a rung whose *target* was wrong (below) — plus `bool-and`/`bool-or`, tier 2's
two stragglers, which fall out for free because `&&`/`||` desugar to `seq`+`if`.
Tiers 1–4 are now at target with no mismatches.

**Two rules, not one.** `Judge.if'` takes an `else`; `Judge.ifNoElse` does not. A single
rule over `Option Expr` would have to case-split inside the premise, which is exactly the
shape `JudgeSeq` was factored out to avoid in clink 2. `ifNoElse`'s content is that
Ruby's missing branch evaluates to `nil`: the else-type is fixed at `.nilT` and the
else-environment at `Γc` (the environment as of the end of the condition), so
`joinT τ .nilT = mkNilable τ` and nothing is bound that the condition did not bind.

**The condition's type is unconstrained, deliberately.** `σ` appears nowhere in `if'`'s
conclusion. Ruby's `if` accepts every value and never raises over its condition — only
`nil` and `false` are falsy — so a `Bool` premise would reject `if 5 … end` and
`if nil … end`, both perfectly safe, and both now rungs (`if-condition-not-bool`,
`if-nil-condition`) that exist to pin this. The condition is still *typed*, because
evaluating it can itself be type-stuck; what is discarded is only its result type.

**`joinT` is total, and that is why `Ty.union` finally does something.** The ported
`Ty.joinTy` answers `none` for two unrelated branch types. An `if` rule that failed there
could not type `if c then 1 else "a"` at all — a program with no type error in it — so
this package grows its own `joinT` (a documented fork of the ported file; see
`AGENTS.md` §Isolation): `joinTy`'s structural cases first, so the familiar shapes keep
their familiar answers, and otherwise a **union of both sides' members**.

*Why the union is normalized (flattened + deduped).* `elsif` is nested `if'`, so
`elsif-chain-mismatch`'s outer join sees `Int` against `union(Int, String)`. Without
flatten-and-dedup the answer is `union(Int, union(Int, String))` — the same *values*, a
different `Ty`, and `Ty` is compared by decidable equality everywhere in this package, so
the rung's hand-written type would not match the computed one. The rung exists to hold
that normalization in place.

*Why producing a union is always sound.* Tier 4 is where the type language changes
register: a `Ty` stops naming *the* class of a value and starts naming an upper bound on
the set it belongs to. That is safe here for a structural reason, not a proved one —
**nothing consumes a union.** No `PrimSig` row has a union receiver and a union is not
`EqSafe`, so any rule that wants to *use* such a value simply fails to apply. The join
buys precision on the way out and costs everything on the way in, which for now is the
right trade: a checker that rejects `(if c then 1 else "a") + 1` is being conservative,
not wrong.

**`joinEnv`, and the rung whose target was wrong.** The environments are joined too, and
unlike `joinT` this is a **soundness** requirement. `corpus/042-if-does-not-leak-`
`reassignment` is `x = 1; if true; x = "hello"; end; x + 1`. Its recorded target was
`true`, with a long description calling the "environment after an `if` is the environment
from before it" simplification harmless precision loss. It is not: the lone branch
rebinds `x` to a `String`, `x + 1` really raises `TypeError` (confirmed under CRuby and
under the model — that is why this corpus entry agrees), and a checker carrying the
pre-`if` environment forward would certify a program that raises. So the rung's target is
now `false` / `unsafe_program`, its description says what it actually pins, and the same
shape is added as a **negative control** in `CheckRungs.lean` so the rejection is
labelled *sound* by running the program rather than merely *conservative*.

The corrected rule joins pointwise over the union of both branches' names. A name bound
in only one branch joins against `.nilT`, which is again just Ruby: the parser declares a
local at the assignment's *syntactic* position, so `if false then y = 1 end; y` is `nil`
rather than a `NameError`. After the join `x : union(Int, String)`, which matches no
`PrimSig` row, so `x + 1` is soundly rejected — the union's inertness doing exactly the
job the paragraph above describes.

**`&&`/`||` for free.** `true && false` desugars to
`seq (vasgn __dt_t1 true) (if (var __dt_t1) false (var __dt_t1))`. No new rule; the
`outEnv` on these two rungs records the desugarer's temporary, and the checker has no
idea it is a temporary and does not need one. This is the clink-1 note's prediction
cashed out: `&&` was tier-3/4 work in a tier-2 costume.

**Widening `expectedClasses`.** `CheckRungs.lean` cross-checks a derived `Ty` against the
class the semantics produced. A `nilable`/`union` admits more than one class, so the
check becomes a set membership rather than an equality — a deliberately weaker row for
these rungs, noted in place. The rung still fails if the class produced is outside the
set.

State after this clink: **40 rungs climbed** (tiers 1–4 complete, and every rung at or
below tier 4 now matches its recorded target), 40/40 cross-checked against the real
semantics, 16/16 negative controls rejected, corpus agreement 0 disagreements,
`chk_sound`/`chkAll_sound`/`chkSeq_sound`/`validate_sound_syntactic` axiom-clean
(`propext`, `Quot.sound`).
