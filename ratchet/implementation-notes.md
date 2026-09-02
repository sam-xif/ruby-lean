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

---

## Clink 4 (2026-09-01) — tier 5: arrays, hashes, and `#[]`: 40 → 48

Rungs added: all eight of tier 5 (`array-int`, `array-empty`, `array-heterogeneous`,
`array-of-sends`, `hash-lit`, `nested-array`, `array-index`, `hash-index`). Two new
`Judge` rules, one new auxiliary relation, two new `PrimSig` rows. Tier 5 is 8/8.

**Ruby has no index syntax, and that is the whole reason this tier is cheap.** `a[0]` is
`send a "[]" [0]` — an ordinary method call — so indexing needs no `Expr` node and no new
rule *shape*, only two `PrimSig` rows. This is the same observation clink 1 made about
`!`, and it keeps paying: the constructs that look like syntax in most languages are
sends in this one, so they land in the table rather than in the judgment.

**`elemTy`: the element type is a `joinT`, and the empty case is not a join unit.**
`Ty.arrayOf` takes one element type; Ruby arrays are heterogeneous. Tier 4's join carries
straight over, so `[1, "a", true] : arrayOf (union Int (union String Bool))` — a real
upper bound on every element, which is exactly what `arrayOf τ` claims. The empty literal
is the interesting case: there is no bottom type in this `Ty`, so nothing to fold from.
`elemTy [] = .any`, and the justification is *vacuity*, not algebra — for an array with no
elements, "every element has type `.any`" is trivially true. It is deliberately **not**
the base case of the fold (the singleton case returns `τ` itself), so a non-empty literal
never gets silently widened to `.any` by passing through a unit. `array-empty` and
`array-int` together pin that.

This is also the first place `.any` is *synthesized* from a value-producing expression.
Until now `.any` came only from `bareName`, whose expression never returns. `arrayOf .any`
does return a value — but the `.any` is inside an `arrayOf`, and `arrayIndex` turns it
into `nilable .any`, which nothing consumes. The inertness argument is unchanged; it just
now has to be made about a type in a position rather than a whole result.

**`arrayLit` reuses `JudgeAll`.** The relation that types a send's argument list is
exactly the relation that types an array literal's elements — same left-to-right
environment threading, same "one derivation per element" requirement. So no new
inductive, and the requirement that every element type (a stuck element sinks the
literal: `[1, 1 + "a"]` has no derivation) comes for free from the relation's shape.
`array-of-sends` is the positive form of the same point.

**`arrayOf` invariance is an obligation deferred, not discharged.** `Ty.arrayOf` is
documented as invariant because covariance is unsound under mutation-through-aliasing.
Nothing here relies on that yet, because there is no rule for `Array#<<` or `Array#[]=` —
no way to write to an array at all. The tier that adds one inherits the obligation, and
the rule's docstring says so. `nested-array` is where the choice is visible as a feature:
`[[1,2],[3,4]]` joins two *equal* `arrayOf Int`s so no union appears, and had the inner
arrays differed the outer element type would be a union rather than a silently widened
`arrayOf (union …)`.

**`hashLit`: a rule whose premise carries no type.** `Ty` has no `hashOf` beside
`arrayOf`, so a hash literal can only be the bare `.cls "Hash"`. The keys and values
still have to *type* — evaluating one can be stuck all on its own, and `{"a" => 1 + "b"}`
must not validate — so `JudgePairs Γ pairs Γ'` exists purely to demand that, and threads
the environment in Ruby's order (key, then value, pair by pair). It is the first relation
in this package with no `Ty` in its conclusion, and the shape is worth noticing: *"these
subterms must be well-typed"* is a separate obligation from *"and here is the type"*, and
a type language with a gap in it is where they come apart.

**Two rows, two different honest imprecisions.**

- `arrayIndex : arrayOf τ #[] (Int) → nilable τ`. The `nilable` is not caution, it is
  correct: `[1,2,3][99]` is `nil`. Bounding the index would need arithmetic on it and a
  length this checker does not track. The cost is that `[1,2,3][0] + 1` — safe Ruby
  returning `2` — cannot be typed, since `nilable Int` matches no arithmetic row. Kept as
  a negative control so the number is recorded rather than rediscovered.
  The `[.int]` argument *is* load-bearing (`[1,2,3]["a"]` raises `TypeError`, inside the
  family) — also a control, and the only one of tier 5's new controls whose admission
  would be unsound rather than merely imprecise. And, like `intDiv`, the row claims
  "never type-stuck", not "never raises": `[1,2,3][2**70]` raises `RangeError`, which is
  outside the family this ladder defines type-safety over.
- `hashIndex : .cls "Hash" #[] (anything) → any`. The argument is unconstrained for
  `objEq`'s reason — lookup goes through `hash`/`eql?`, total on every class in this `Ty`,
  and a missing key answers `nil` (`{"a"=>1}[[1,2]]` is `nil`) — and the result is `.any`
  because there is genuinely nothing to read a value type off. This is the sharpest
  statement of the `Ty` gap the `hash-lit` rung records: the rung validates, but
  `{"a"=>1}["a"] + 1` cannot, and that too is a control.

**Four new controls, three of them "conservative".** Tier 5 is the first clink where most
new controls are *safe programs the checker declines* rather than unsafe ones it must
reject: the `nilable` price, the `.any` price, and the element-union price
(`[1,"a"][0] + 1`). They are in `CheckRungs.lean` because a cost that is not measured
drifts, and because the harness distinguishes "rejected (sound: really type-stuck)" from
"rejected (conservative: safe, no rule yet)" — so the ladder shows which kind each is.

**`expectedClasses (.arrayOf _) = ["Array"]`, and what that does not check.** The harness
compares the class of the whole result value, and nothing in it inspects an array's
contents, so the *element* type is not cross-checked against the semantics here. What
backs the element type instead is `arrayLit`'s premise: each element has its own
derivation, and each of those would be a harness row if it were a rung. Noted in place.

**`toRubyCore` needed a mutual companion.** The controls' `.hash` case could not be a
`mapM` with a lambda over the pair list — the lambda hides the structural decrease from
the termination checker. Spelled out as `toRubyCorePairs` in a `mutual` block. Purely
mechanical, recorded so the next person does not retry the lambda.

State after this clink: **48 rungs climbed** (tiers 1–5 complete, every rung at or below
tier 5 matching its recorded target), 48/48 cross-checked against the real semantics,
20/20 negative controls rejected, corpus agreement 0 disagreements, and
`chk_sound`/`chkAll_sound`/`chkPairs_sound`/`chkSeq_sound`/`validate_sound_syntactic`
axiom-clean (`propext`, `Quot.sound`).

---

## Clink 5 (2026-09-01) — tier 6: top-level methods, and a bottom type: 48 → 54

Rungs added: all six positive rungs of tier 6 (`simple-fun`, `fun-zero-arg`,
`fun-calling-another-fun`, `fun-three-params`, `fun-returning-array`,
`fun-recursive-factorial`); the three negative ones (`fun-wrong-arity`,
`fun-body-mismatch`, `fun-unknown-call`) are now rejected for the right reasons rather
than for want of a rule. Tier 6 is 9/9 at target.

The biggest clink so far. Four things changed shape, and they are separable, so they are
written up separately.

### 1. Two new tables, and only one of them is bookkeeping

A method has parameters and a body, not a type, so nothing in `Env` can hold one. Tier 6
adds `DefTable` (methods already defined) and `AsmTable` (instantiations currently
assumed) as indices of `Judge`, and they are opposites:

- **`D` is syntax the checker has read.** Untrusted because it is read off the program.
- **`Δ` is a claim the checker is in the middle of discharging.** Untrusted because the
  only rule that adds to it also proves it.

`D` is **threaded**, not collected up front, and that is a soundness requirement:
collecting every `def` in the program would certify `foo(); def foo; end`, which raises
`NoMethodError` — the headline member of the family this ladder calls type-stuck. So
`JudgeSeq.cons` continues with `extendDefs D e`, exactly as it already threads `Env`. Note
what that does *not* cost: forward reference inside a **body** still works, because a body
is judged against the `D` in force at its *call site*, which is after every top-level `def`
has run (`fun-calling-another-fun` — and it would work with the two `def`s in either
order).

The cost that remains: a `def` inside an `if` branch never reaches the table
(`extendDefs` looks only at a statement head), so calling such a method is not typed. No
rung asks for it.

### 2. No signatures at all — per-call-site instantiation

Ruby writes no parameter types anywhere, so `def add(x, y) = x + y` has *nothing* to check
a call against until someone calls it. Three designs were available: infer one signature
per method (needs a constraint solver and a notion of principal type this `Ty` cannot
support — no type variables), demand annotations (there are none in the corpus), or **type
the body once per call-site argument shape**. The third is what `Judge.callDef` does: the
body is judged in `paramEnv d.params argTys`, a fresh environment holding only the
parameters at the types this call site produced, and the call's type is whatever the body
synthesizes there.

This is closer to C++ template instantiation than to Hindley–Milner, and the trade is
explicit:

- **What it buys.** `fun-returning-array` types at `arrayOf Int` with no annotation
  anywhere — the return type comes wholly from the body, the parameters wholly from the
  call site. `fun-body-mismatch` is caught, and *only* this rule catches it: the call site
  looks fine and the `TypeError` is inside a body that only dispatch reaches. And a method
  used at two shapes is checked at both rather than at their join.
- **What it costs.** Work is duplicated per call site (and, because of the two-pass check
  below, doubled again), and there is no such thing as "the type of `add`" to report. Also
  no polymorphism: a method whose body is only typeable for *some* argument types is
  rejected at exactly the call sites where it should be, which is right, but the checker
  can never say so once and for all.

Also fixed by construction: the body is judged in a fresh environment and the call's
*outgoing* environment is the caller's, after the arguments — never the body's. A Ruby
method body neither sees nor writes the caller's locals.

### 3. `Ty.never`, and the two strictness rules that make it usable

`fun-recursive-factorial` forced a bottom type. `Ty.never` = "this expression does not
produce a value", and it does three jobs that are the same job seen three ways:

1. **The unit of `joinT`.** `joinT τ .never = τ`: if one `if` branch cannot return, the
   `if`'s value comes only from the other. This also let `elemTy` become an honest fold
   (`elemTy [] = .never`), retiring tier 5's hand-written singleton base case — see the
   churn note below.
2. **The type of a strict operand that never returns.** `Judge.primNever`/`callNever`: if
   a send's receiver or an argument does not return, dispatch never happens, so no claim
   about the result can be falsified. Note these rules do not mention the method name or
   consult `PrimSig` — they hold for methods this checker knows nothing about.
3. **The candidate a recursive call gets while its own signature is being found** (below).

Only the two *send* shapes got a strictness rule. An `if` with a `.never` condition, an
array literal with a `.never` element and so on are equally justified and equally absent;
each would be a rule of its own and none has a rung. Recorded here so their absence is a
choice.

`.never` is inert like `.any` — no `PrimSig` row takes it as a receiver, it is not
`EqSafe` — but inert *from below*: `.any` is "some value, type unpinned", `.never` is "no
value". They are not interchangeable, which is why `arrayOf .never` is the precise type of
`[]` and `arrayOf .any` would not be.

### 4. Recursion: assume-then-verify, with an explicitly untrusted first pass

`fact`'s body cannot be judged before its return type is known, and its return type comes
from its body. `Judge.callDef` breaks the cycle by having `ρ` appear twice: as an
assumption (`⟨m, argTys, ρ⟩ :: Δ`, which `callAsm` picks up at the recursive occurrence)
**and** as the type the body must synthesize under that assumption. Nothing in the rule
says where `ρ` came from.

`chk` finds it in two passes:

- **Pass A — the hint.** Type the body with this instantiation assumed to *not return*
  (`ρ = .never`). For `fact` this is what makes the base case visible before the recursive
  case has a type: `n * fact(n-1)` becomes `.never` by `primNever`, and
  `joinT Int never = Int`. For a non-recursive method it is simply the body's type,
  computed once for nothing.
- **Pass B — the check.** Put the candidate in `Δ` and re-type the body; it counts only if
  it reproduces itself.

**Pass B is load-bearing, and there is a control that proves it.**
`def f(x) = if x <= 0 then 1 else f(x-1) + true; f(1)` really raises `TypeError` — the
recursion bottoms out, returns `1`, and `1 + true` runs. Pass A *accepts* it: the recursive
call at `.never` makes the whole `else` branch `.never`, which the join discards, leaving
`Int`. Only re-running with `Int` assumed exposes `Int + true`. This control is in
`CheckRungs.lean` and its rejection is labelled *sound* by running the program.

The nicest property of the split is that it shows up in the *proof*: `chk_sound`'s
`callDef` case binds pass A's result and never uses its derivation. The hint is untrusted
by construction, not by assertion.

**Why the discharge is legitimate at all** is an induction on the *execution*, not on the
derivation: each `callAsm` inside a body corresponds to an actual recursive call one level
deeper at run time, so "if the call returns, it returns a `ρ`" follows by induction on the
number of calls that completed. Non-termination makes the claim vacuous — the same reading
`PrimSig.intDiv` established for `ZeroDivisionError`. Since this package has no semantic
soundness theorem yet, that argument lives in `Judge.callDef`'s docstring alongside the
`PrimSig` rows' justifications, which is where the ladder's other semantic claims live too.

Consequence for reading a `Judge`: **`Judge D Δ Γ e τ Γ'` with a non-empty `Δ` is a
conditional claim.** Only `Δ = []` is absolute, and `validate` starts there — which is now
stated in `validate_sound_syntactic`'s conclusion (`Judge [] [] [] p τ Γ'`).

### 5. `bareName` grew a premise, exactly as clink 2 predicted

Clink 2 wrote: "the rung that adds `def'` (tier 6) must therefore either delete this rule
or gate it on the program's declaration table." Gated. Until now no rule typed a `def'`, so
`def x; …; end; x` could not be judged at all, and *that accident* was what made the one
`BareNameError` row sound. With `defStmt` in place, `def x; 1 + true; end; x` would take
the `bareName` route to `.any` and validate a program that raises `TypeError`. The new
premise `defGet? D m = none` restores the property by checking it instead of relying on it,
and the control is in `CheckRungs.lean`.

Remaining conservatism, recorded: there is no rule for a `vcall` that *does* name a defined
method (`def get5; 5; end; get5`, no parentheses — the desugarer emits a `vcall`, not an
argument-less `send`). Such a program is simply not typed. No rung asks for it.

### 6. Fuel

`chk` recurses into a body, and a body is not a subterm of the call, so tier 6 is where
`chk` stops being structurally recursive. Rather than invent a measure over `D` and `Δ`,
`chk` matches on a fuel budget and every recursive call spends one unit.

This has no soundness consequence and it is worth being exact about why: fuel can only turn
a `some` into a `none`, and `chk_sound` quantifies over every fuel value. It is purely a
*completeness* knob, which is why it is a named constant (`fuelDefault = 64`) rather than a
magic number at the call site. The alternative — a real termination measure — would have to
bound the number of distinct instantiations `(f, argTys)`, and argument types can grow
through joins, so there is no obvious bound to prove. Fuel is the honest answer, and it
matches how the semantics side of this project already works.

### Churn this clink caused elsewhere, deliberately

- **`elemTy [] = .never`, not `.any`** — so `array-empty`'s type changed from
  `arrayOf any` to `arrayOf never` and `elemTy` lost its singleton base case. Leaving
  `.any` there once a bottom type existed would have been exactly the kind of drift these
  notes exist to prevent: `.any` was tier 5's workaround for the absence of `.never`, and
  tier 5's own note says so.
- **`subTy .never _ = true`** added for consistency. `subTy` is still unused by `Judge`
  (there is no subsumption rule); the case is there so the function does not quietly lie.
- **`CheckRungs.toRubyCore` gained `def'`/`send none`** plus a `toRubyCoreParam`, for the
  new controls.

State after this clink: **54 rungs climbed** (tiers 1–6 complete, every rung at or below
tier 6 matching its recorded target), 54/54 cross-checked against the real semantics,
24/24 negative controls rejected — three of the four new ones *sound* rejections, one per
premise added this clink — corpus agreement 0 disagreements, and all six soundness
theorems axiom-clean (`propext`, `Quot.sound`).

---

## Clink 6 (2026-09-01) — tier 7's object model: 54 → 67

Rungs added: thirteen of tier 7's sixteen — `class-basic`, `class-method-with-param`,
`class-two-getters`, `class-method-calls-method`, `class-inheritance-override`,
`class-multiple-instances`, `class-no-initialize`, `class-ivar-lazy-nil`,
`class-array-of-instances`, `class-instance-in-hash`, `class-setter-method`,
`class-instance-as-fun-arg`, `class-self-returning-method`. The three left
(`class-inheritance-field`, `class-super-call`, `class-factory-method`) are the *hierarchy* —
method lookup up the superclass chain, `super`, and singleton methods — and are deliberately
a separate clink; this one is the object model.

### 1. `Ty.inst`: an object's type carries its instance variables

The forcing observation: **an object's observable type is not its class name.**
`Point.new(1, 2)` and `Point.new("a", "b")` are both `Point`s, and `getX` returns an
`Integer` from one and a `String` from the other. Nothing in the class *declaration* decides
that, because Ruby writes no ivar types, so the only moment the information exists is the
instantiation — and the only place to keep it is the type of the object.

Hence `Ty.inst (name) (ivars)`, where `ivars` is an **ivar spine**
(`ivar0`/`ivarCons name ty rest`). The spine rather than a `List (String × Ty)` payload for
exactly the reason `arrowOf` is a spine: a list payload makes `Ty` a nested inductive and
nested-derived `DecidableEq` does not kernel-reduce, which `Rungs.lean`'s per-rung `rfl`
checks depend on. `.cls name` stays, for the builtin classes whose instances have no ivars
this checker models (`String`, `Hash`).

`class-basic` is the payoff and worth reading as one: the `Int` in its type travels from the
literal `1`, through `initialize`'s parameter, into the spine inside `Ty.inst "Point" …`, out
through `getX`'s `@x` — with **no annotation anywhere in the program** — and the derivation
term is the record of that trip.

### 2. `Ctx`: five indices bundled into one

`Judge` needed a class table on top of tier 6's two, plus a `self` type, plus a *second*
threaded state (the ivar spine). That is eight or nine indices, which is unreadable, so the
four **input-only** components — `classes`, `defs`, `asms`, `selfTy` — are bundled as `Ctx`
and the judgment is `Judge κ Γ I e τ Γ' I'`. Nothing about the bundling is semantic; the
split is exactly *input-only vs. threaded*, and it is chosen so that reading a rule tells you
how state flows.

Cost, paid once: every rule, every `chk` arm and every proof case was rewritten. `Rung.deriv`
became `Judge ctx0 [] .ivar0 program ty outEnv .ivar0`, and all 54 earlier rungs re-derive
unchanged except for the two rules that grew premises.

### 3. Method dispatch: the receiver's *type* is the dispatch table

`callMethod` reads both halves of what dispatch needs off `.inst n Iself` — which class to
look the method up in, and what the object's ivars are — and then does tier 6's trick again:
the body is judged in `paramEnv`'s fresh locals, with `Iself` as its ivar state and
`some (.inst n Iself)` as the type of `self`.

`newInst` is where a spine is *manufactured*: `initialize`'s body is judged with the call's
argument types as its parameters and `.ivar0` as its state, and the spine that comes out
becomes the object's type. `newInstNoInit` is a separate rule rather than a defaulting clause,
because the arity condition differs and it matters: `Object#new` inherited unchanged takes
**zero** arguments and raises `ArgumentError` on any (control on file).

`selfCall` handles a bare name inside a body that names one of `self`'s own methods —
`class Rect; def describe; "area=" + area.to_s; end` — which is a `vcall`, not a local read
and not a top-level function call.

### 4. The one genuinely load-bearing invariant: **a method may not retype an ivar**

`callMethod`'s last premise ends `… Γb' Iself` — the body's *outgoing* spine must be the one
it started with. This is the soundness argument for the entire ivar mechanism, and the
control that shows it is the most important in `CheckRungs.lean`:

```ruby
class C
  def initialize(x); @x = x; end
  def set; @x = "s"; end
  def get; @x; end
end
c = C.new(1); c.set; c.get + 1        # TypeError
```

Without the premise the caller keeps its stale `.inst C {@x: Int}` after `c.set`, `c.get`
answers `Int`, and this validates. With it, `set` has no derivation.

The premise also buys the invariant that `ivarRead`'s defaulting depends on: **a spine is
complete** — it records every ivar the object will ever have — because a method that added
one would lengthen the spine and be rejected. That is what makes
`(ivarGet? I x).getD .nilT` sound rather than a guess, and `class-ivar-lazy-nil`
(`Box.new.reveal` is `nil`, checked by execution) the rung that states it.

`class-setter-method` is the boundary case: `@size = @size + 1` really does mutate, and is
admissible only because `Integer + Integer` is an `Integer` — the ivar's *type* is unchanged
even though its value is not. The conservative cost is measured by a second control: a method
that lazily creates an ivar is safe Ruby and is rejected.

### 5. `self` is not typed inside `initialize`, and that is a soundness requirement

`newInst` judges `initialize`'s body with `κ` **unchanged**, so `κ.selfTy` stays whatever the
caller's was (`none` in every rung). This looks like an omission and is not: `initialize`'s
job is to *change* the spine, so there is no single spine that describes `self` throughout it
and therefore no honest `.inst n _` to offer. A method called on `self` from inside
`initialize` would read a half-built spine and claim `nil` for an ivar about to be an
`Integer` — unsound. A rule that wants it needs a fixpoint over the spine; no rung asks.

### 6. `bareName` grew its second premise, for the same reason it grew its first

Tier 6 added `defGet? κ.defs m = none`. Tier 7 adds `κ.selfTy = none`, and it is the identical
failure one level down: inside a method body a bare name resolves against *that object*, so
`class C; def x; 1 + true; end; def go; x; end; end; C.new.go` would launder a stuck body
through the one `BareNameError` row. Control on file. The rule is now explicitly a top-level
rule, which every earlier version of its docstring already claimed it was.

### 7. `if`'s spine is not joined — the branches must agree

`Judge.if'` gained `I₁ = I₂` as a premise rather than a `joinEnv`-style widening, and the
asymmetry with locals is deliberate: a spine is not merely state, it is part of the *type* of
`self`, and there is no pointwise widening of it that keeps that type honest. A branch that
assigns an ivar at a new type is rejected rather than widened. No rung needs the precision.

### 8. What was left out, on purpose

- **Inheritance.** `extendClasses` *records* `Cls.super?` and nothing reads it; lookup is
  `defGet? c.methods`, one class deep. `class-inheritance-override` still climbs, and the
  note in its docstring says why that is not luck: `Dog` overrides `speak` and declares no
  `initialize`. `class-inheritance-field`, whose `Dog` inherits both, is the rung that needs
  the walk and is the one still unclimbed.
- **No assumption table for methods.** Unlike `callDef`, `callMethod` has no
  assume-then-verify machinery, so a recursive method exhausts fuel and is rejected. The fix,
  if wanted, is to key `AsmTable` by receiver type as well as name.
- **Class bodies are restricted to `def`s and `nil`** (`classMethods?`). That single premise
  does double duty: it is what makes the body safe to *evaluate* unchecked (a `def` statement
  never runs its body) and what makes the class readable into `CTable`. A body with anything
  else is not typed. `class' `'s type is `.any` because a class body's value is its last
  statement's (`class Foo; def hi; end; end` really is `:hi`) and nothing reads it.

### 9. An elaboration note worth keeping: `ivarSet` is not invertible by unification

`class-setter-method`'s derivation needed two explicit annotations (`Iself := boxSpine`,
`I' := boxSpine`). The body's outgoing spine is `ivarSet ?I' "@size" ?τ`, `callMethod`
requires it to equal `Iself` — itself an unreduced `ivarSet …` from `newInst` — and Lean
matches the two applications *structurally*, solving `?I' := .ivar0`, which is the wrong
environment. Pinning both to a named literal spine turns the check into a reduction
(`ivarSet boxSpine "@size" .int` really is `boxSpine`) instead of a match. Recorded because
it is not a workaround: it is the same fact the rung is about, showing up in the elaborator.

State after this clink: **67 rungs climbed** (tiers 1–6 complete, tier 7 at 13/16), 67/67
cross-checked against the real semantics, 29/29 negative controls rejected — three of the
five new ones *sound* rejections, one per premise added this clink — corpus agreement 0
disagreements, and all six soundness theorems axiom-clean (`propext`, `Quot.sound`).

---

## Clink 7 (2026-09-01) — tier 7's hierarchy: 67 → 70, and tiers 1–7 complete

Rungs added: the last three of tier 7 — `class-inheritance-field`, `class-super-call`,
`class-factory-method`. Three new rules, one new `Ctx` field, one new `Cls` field.

Each of the three is about a place where **"which class?" has a different answer from the
obvious one**, and that is the whole theme of the clink:

### 1. `mroGet?` — dispatch walks up, and reports where it landed

`defGet?` finds a method declared *on* a class; `mroGet?` finds the one dispatch would run,
walking `Cls.super?`. It replaced the `clsGet? … → defGet? c.methods …` pair in every
dispatch rule, which is why all thirteen earlier tier-7 rungs lost an `rfl`.

Two decisions:

- **It returns the class it found the method in**, not just the `Defn`. Nothing needed that
  until `super`, and then it is indispensable — see below.
- **The walk is bounded by the table's length**, because `CTable` is *data*: nothing stops it
  describing a cycle (`class A < B` and `class B < A` cannot both be declared in Ruby, but
  the table does not know that). Exhausting the budget answers `none`, which, like `chk`'s
  fuel, can only cost completeness. A chain longer than the table must have revisited a
  class, so the bound is not even conservative in practice.

`class-inheritance-field` is then two walks: `Dog` declares literally nothing (its body is
`nil`), so `mroGet? "Dog" "initialize"` finds `Animal`'s constructor and
`mroGet? "Dog" "speak"` finds `Animal`'s reader. The instance's type is still
`.inst "Dog" {@name: String}` — the class is the receiver's, the method is the ancestor's,
and keeping those separate is exactly what returning the definition site is for.

### 2. `Ctx.frame` — `super` needs the definition site, not the receiver

`class Triangle < Shape; def initialize; super(3); end`. The class `super` walks up from is
**`Triangle`**, the class the running method was *declared* in. `κ.selfTy` names the
*receiver's* class, which for a deeper hierarchy is a different and wrong answer — and inside
a constructor it is not even set (clink 6's deliberate `none`). So `Ctx` gained
`frame : Option Frame` = the defining class plus the method's own name (`super` calls the same
name), and `newInst` now enters `initialize` through `Ctx.inCtor`, which records the
definition site and nothing else.

`superCall` rebuilds the frame for the parent body from `mroGet?`'s answer, so a `super`
inside the parent walks from the right place again.

**The second half of the rule is that the ivar spine threads *through* the super call.** The
parent's body is judged with the spine as of the end of `super`'s arguments, and its outgoing
spine becomes the super call's — which becomes `Triangle#initialize`'s, which is the one
`newInst` puts in the type. So `@sides` is set by the *parent*, in the *child's* object, and
`class-super-call`'s derivation is that sentence. Getting this wrong in the other obvious way
(judging the parent at `.ivar0` and discarding its spine) would type
`Triangle.new.sides` as `Nil` — not unsound, but wrong, and the rung would fail on the
semantic cross-check rather than in the kernel.

`zsuper` (bare `super`, which forwards the current arguments implicitly) is a different `Expr`
head and has no rule.

### 3. Singleton methods are a separate namespace, and `self` there is a class object

`Cls` gained `smethods`, filled by `clsMember?`'s `defs .self'` case — `classMethods?` now
returns a pair, and its single `none` still does the same double duty it did in clink 6
(making the body safe to evaluate unchecked *and* readable into `CTable`).

`callSMethod` looks up `smroGet?` (the same walk over the other table — Ruby inherits class
methods) and judges the body with `self` typed **`.clsOf n`**. That last part is the point: it
is what makes the bare `new(0, 0)` inside `def self.origin` mean "allocate one of me". That
`send none "new" …` is `selfNew`, an implicit-self call resolved against a `self` that is a
class object rather than an instance — otherwise the same rule as `newInst`.

Two orderings, both deliberate and both recorded in place:

- On a `.clsOf` receiver, **a declared singleton method is tried before the allocator**, so a
  class defining `self.new` gets its own. That is what Ruby does.
- `selfNew` is tried **after** the top-level def table, so a top-level method actually named
  `new` would win. Nothing needs the other order, and no rung has such a program.

A singleton method's ivar state is `.ivar0` in and out: a class object can hold instance
variables of its own (`@count` at class level) and this judgment does not model them, so a
singleton method that assigns one is not typed.

### 4. Four new controls, all four *sound* rejections

Tier 7's hierarchy is unusually well served by controls, because every premise added has a
program that raises without it:

- `class A; end; class B < A; end; B.new.nope` — `mroGet?` terminating in `none` rather than
  falling back on anything. `NoMethodError`.
- `class P; def go; 1 + true; end; end; class C < P; def go; super; end; end; C.new.go` — the
  parent's body is checked *at the definition site*. The tier-7 twin of `fun-body-mismatch`:
  nothing at the call site looks wrong.
- `class A; def go; super; end; end; A.new.go` — `superCall`'s `c.super? = some sn` premise.
  Ruby raises `NoMethodError` ("super: no superclass method").
- `class P; def self.origin; 1; end; end; P.new.origin` — the two method tables really are
  separate.

### What is still not modelled, recorded so it is a choice

`zsuper`; `def obj.m` for an object other than `self`; class-level instance variables;
modules and `include`/`extend` (tier 8); an implicit-self call *with arguments* to another
instance or singleton method (only the zero-argument `vcall` form and the specific `new` form
have rules); and method-level recursion, which still exhausts fuel because `AsmTable` is keyed
by name and argument types but not by receiver.

**`subTy` is still unused.** It was expected to come due at inheritance, and it did not:
`mroGet?` makes a `Dog` usable wherever its own methods are called without any subtyping
relation, because dispatch is by walk rather than by subsumption. The place it would actually
be needed is a *parameter* annotation (`def f(a : Animal)`), and this checker has no
annotations. Worth stating, because the tier-7 frontier entry predicted otherwise.

State after this clink: **70 rungs climbed, and tiers 1–7 are complete** — every rung at or
below tier 7 matches its recorded target. 70/70 cross-checked against the real semantics,
33/33 negative controls rejected (all four new ones *sound*), corpus agreement 0
disagreements, and all six soundness theorems axiom-clean (`propext`, `Quot.sound`).

---

## Clink 8 (2026-09-01) — tier 8: modules: 70 → 80, tiers 1–8 complete

Rungs added: all ten of tier 8. Two new rules, one new `Cls` field.

**The cheapest tier on the ladder, and the cheapness is the finding rather than luck.** Every
one of the ten rungs is `module M; def self.foo; …; end; M.foo(args)`, and `M.foo` is
`callSMethod` — tier 7's singleton-method rule — with *nothing added*. A module already was,
in this judgment, exactly what tier 7 made a class object be: a thing with a singleton method
table, reachable through `Ty.clsOf`. Worth recording because the corpus's own tier ordering
implies modules are a step up from classes, and in this design they are a step *sideways*.

The two rules that were genuinely missing:

- **`moduleStmt`.** `Expr.module'` is a different head from `class'` with no superclass slot,
  so it needs its own statement rule. Same `.any` type for the same reason (a module body's
  value is its last statement's, and nothing reads it) and the same `classMethods?` premise
  doing the same double duty (safe to evaluate unchecked, and readable into `CTable`).
- **`selfSCall`.** `module M; def self.describe; value * 2; end; def self.value; 21; end` —
  the `value` inside `describe` is a `vcall`, and `self` there is a `.clsOf`, not an
  `.inst`, so `selfCall` does not apply. The twin, differing only in which table the lookup
  goes to. That difference is not a detail: an instance method and a singleton method of the
  same name are different methods, and `M.value` resolving to a plain `def value` would be
  wrong — control on file.

### The guard that tier 8 actually needed: `Cls.isModule`

**A module cannot be allocated.** `M.new` raises `NoMethodError`. Without a flag, `M.new`
would find no `initialize`, fall through to `newInstNoInit`'s zero-argument allocator, and
certify a program that raises.

So `Cls` gained `isModule`, and the three allocator rules go through two new module-aware
lookups rather than testing the flag themselves:

- `instClsGet?` — the table entry, unless it is a module.
- `ctorGet?` — `initialize` by the ordinary walk, but only for something allocatable.

Bundling it that way was deliberate: routing `newInst` through `ctorGet?` instead of
`mroGet? … "initialize"` kept its **premise count unchanged**, so none of tier 7's thirteen
existing derivations had to be touched. (Clink 7's `mroGet?` merge cost exactly that churn, so
the shape of the fix was chosen with it in mind.)

`newInstNoInit`'s two lookups are not redundant, and the docstring now says so:
`instClsGet?` says the receiver is allocatable at all, `ctorGet? = none` says it has no
constructor up its chain.

**No rung writes `new` on a module**, so the flag is invisible in all ten derivations and
visible only in `CheckRungs.lean`'s control. That is precisely the shape of guard that rots
undetected without one, which is why it went in with the tier rather than after it.

### One thing that is correct by accident, said out loud

A module's *instance* methods (a plain `def` in its body) are recorded in `Cls.methods` and
are unreachable: there is no `new` to get an instance, and `include`/`extend`/
`module_function` have no rule, so no program that reaches them types at all. `M.foo` for an
instance-method `foo` looks in `smethods`, misses, and is rejected — which is also what Ruby
does. Recorded in `Cls.isModule`'s docstring because "unreachable because three other
features are unimplemented" is a fact that stops being true the moment one of them lands.

### A row that finally has a rung

`PrimSig.intGt` was admitted in clink 1 with no rung asking for it — the one place a
signature was not rung-driven, and noted then as a choice rather than a drift.
`module-boolean-method` (`def self.positive?(n); n > 0; end`) is the rung that asks. Also
worth noting from that rung: a method name ending in `?` is an ordinary name, and nothing in
the judgment or the lookups treats it specially.

State after this clink: **80 rungs climbed, and tiers 1–8 are complete.** 80/80 cross-checked
against the real semantics, 36/36 negative controls rejected (all three new ones *sound*),
corpus agreement 0 disagreements, all six soundness theorems axiom-clean (`propext`,
`Quot.sound`). What remains is tier 9 (blocks and procs — 22 rungs, the largest single demand
left, and the first that needs `Ty`'s arrow spine) and tier 10 (metaprogramming).

---

## Clink 9 (2026-09-01) — tier 9a: callable values: 80 → 87

Rungs added: seven of tier 9's twenty-two — `lambda-zero-arity`, `lambda-stabby-one-param`,
`proc-basic`, `proc-bracket-call`, `lambda-closure-capture`, `lambda-returns-lambda`,
`lambda-as-argument`. The ones whose callable is created with `lambda`/`proc` and invoked
with `#call`/`#[]`, with no block ever *passed to* a method. Two new rules and one new `Ty`
constructor; **no new threaded state**, which was the design goal.

### 1. Why `arrowOf` could not be used, after sitting in `Ty` unused since the port

An arrow needs its parameter types, and **Ruby writes none.** `f = lambda { |x| x + 1 }`
says nothing about `x`; only `f.call(2)` does, and that is a different expression, possibly a
different statement, possibly inside a different method. There is no principal type to infer
without type variables, and this `Ty` has none. Every alternative considered failed on the
same point:

- Parameters at `.any` — then `x + 1` has no `PrimSig` row and the lambda is untypeable.
- An untrusted first pass à la clink 5 — but a hint has to come from *somewhere*, and the
  only source is a call site the checker has not reached yet.
- Bidirectional checking — nothing in `f = lambda { … }` supplies an expected type.

### 2. `Ty.clos idx captured` — a type that is a reference to code

So a callable's type says *which block* and *what it closed over*, and a call instantiates
the body at the call site's argument types: `Judge.callDef`'s move, lifted from a named
method to a value.

**`idx` indexes `Ctx.closures`, the table of every block literal in the program, collected
once by `collectBlocks` before checking starts.** That "before" is the whole reason there is
no fourth piece of threaded state. The obvious alternative — allocate an index when a lambda
expression is reached — makes the table grow mid-expression, and then a `Ty.clos k` is only
meaningful relative to a table that is still changing. A whole-program pre-pass makes the
index mean the same thing everywhere, and `Ctx` stays input-only.

**`captured` is a binding spine, and it is in the *type*, not in the table.** Two
syntactically identical blocks share a table entry — harmless, since an entry is only
`(params, body)` — but they need not have closed over the same environment. Reusing the ivar
spine constructors (`ivar0`/`ivarCons`) for this cost nothing and is why `Ty` gained one
constructor rather than three.

`closCall` judges the body in `paramEnv c.params argTys ++ spineToEnv cap` — this call's
argument types for the parameters, then the captured locals, parameters first so they shadow.
That single environment is the whole of tier 9a:

- `lambda-closure-capture` works because `spineToEnv cap` still holds `n`.
- `lambda-returns-lambda` — currying, with no arrow type anywhere — works because the inner
  literal's captured `x` is the *outer's parameter*, which was in `Γ` when the literal was
  reached. Its type is `.clos 1 {x: Int}`, index 1 because `collectBlocks` descends into a
  block's body.
- `lambda-as-argument` works because a `.clos` travels through `paramEnv` like an `Int`.

### 3. `lambda` and `proc` share one rule, and the imprecision is the recorded one

A lambda checks arity strictly; a proc pads missing parameters with `nil` and drops extras.
`Ty` cannot express the second discipline — that is exactly the gap §Ty language gaps already
records from `proc-arity-leniency` — so the rule imposes the **strict** reading on both.
Direction matters: strict-for-a-lambda is exact, strict-for-a-proc rejects legal calls, so
both errors are conservative. Lenient-for-both would accept `lambda-arity-mismatch`, which
raises. In the derivations the entire difference between `proc-basic` and a lambda is
`.inr rfl` instead of `.inl rfl`.

### 4. `κ.selfTy = none` on both rules — a hole closed by restriction

A closure's body sees the `self` of wherever it was *created*, and `Ty.clos` records the
captured locals but **not** the captured `self`. Restricting creation and invocation to
top-level `self` makes the omission harmless instead of unsound: a lambda made inside a
`Point` method and called inside a `Box` method would otherwise have its body checked against
the wrong `self`. All seven rungs are top-level or inside top-level `def`s (where `callDef`
leaves `selfTy` alone), so nothing is lost. Lifting it means putting `selfTy` in `Ty.clos`
beside the captured locals.

### 5. The thing that actually cost the time: `Expr`'s derived `BEq` does not reduce

`closIdx?` matches a block against the table **by syntax**, and every
`closIdx? … = some idx` premise plus `Rungs.lean`'s per-rung `rfl` needs that to happen *in
the kernel*. `Expr` is a **nested** inductive (`List Expr`, `List (Expr × Expr)`), so its
derived `BEq` is compiled by well-founded recursion and `exprEq (.int 1) (.int 1) = true` is
not provable by `rfl`. This is the same fact that made `Ty`'s arrow and ivar spines *spines*
rather than list payloads — noted in `Ty.lean` since the port — reappearing on the other side
of the boundary, on syntax this package does not own.

The fix is a hand-written structural comparator, and two details of it were not obvious:

- **`Option Expr` fields must be matched inline, not through an
  `exprEqOpt : Option Expr → Option Expr → Bool` companion.** `Option Expr` is not part of
  the nested-inductive bundle Lean builds structural recursion from, so adding that companion
  pushes the whole mutual group onto well-founded recursion — at which point it stops
  reducing and every dependent `rfl` fails. The first attempt had exactly that helper and
  failed even on `exprEq (.int 1) (.int 1)`; `collectBlocks`, written earlier with inline
  `match recv with …`, reduced fine, which is what pointed at the cause.
- **`paramEq` lives outside the group.** `Param.opt` carries a default `Expr`, so a recursive
  `paramEq` would pull `Expr` back in. An optional parameter therefore compares `false` —
  conservatively, since a block with one gets no index and is not typed, and no rung has one.

The catch-all is `false`, which is safe in both directions: uncovered syntax makes two
identical blocks compare unequal (no index, no rule, conservative rejection), and a spurious
`true` is impossible because every covered case compares every field.

### 6. A control that had to be *removed* from the controls list

`lambda { |x| x + true }` with no call **validates, and should**: it merely evaluates to a
Proc. A body is an obligation of its *call sites*, so a lambda nobody invokes cannot make a
program type-stuck — the same fact `Judge.defStmt` established in clink 5. It was briefly
added as a negative control, correctly failed as "CERTIFIED — table is too generous", and is
now a comment on the control next to it rather than a control. Worth recording because the
harness caught a mistake in the *test*, which is the harness working.

### What is left of tier 9 (12 rungs), and what each needs

- **A block passed to a builtin** (`block-each-int`, `block-map-to-s`, `block-nested-map`,
  `block-two-params-inject`, `block-select-with-if`, `block-sort-by-length`, and the negative
  `block-bad-arith`): needs `PrimSig` to grow *higher-order* rows — a claim about what
  `Array#map` does with a block, not just about its argument types. That is a genuinely new
  kind of row and probably a separate relation.
- **`blockpass`** (`block-pass-symbol-to-proc`, `block-pass-lambda-variable`): `&:to_s` and
  `&double`, i.e. a callable *reaching* a builtin, which needs the above first.
- **`yield`** (`yield-arith`): the block has to be available inside the method body it was
  passed to — a new component of `Ctx`.
- **`Param.block`** (`block-param-ampersand`): `def run(&b)`, which `paramEnv` currently
  refuses.
- **`return` inside a lambda** (`lambda-explicit-return`): needs care, and the obvious rule is
  unsound. Typing `.ret e` as `e`'s type makes `def f; return "a"; 2; end` validate at `Int`;
  typing it `.never` does not help, because `JudgeSeq` still takes the *last* statement's
  type. The honest fix is probably `JudgeSeq` refusing to continue past a non-returning
  statement, plus a rule that reads a trailing `return` as the body's result.

State after this clink: **87 rungs climbed** (tiers 1–8 complete, tier 9 at 7/22), 87/87
cross-checked against the real semantics, 39/39 negative controls rejected, corpus agreement 0
disagreements, all six soundness theorems axiom-clean (`propext`, `Quot.sound`).

---

## Clink 10 (2026-09-01) — tier 9b: a block reaching a method: 87 → 90

Rungs added: `yield-arith`, `block-param-ampersand`, `lambda-explicit-return`. Four new
rules, one new `Ctx` field, one new function on syntax. Tier 9 goes 7/22 → 10/22.

The shift from tier 9a is **where the block goes**: there a block literal *was* the value;
here it is passed to a method. A block literal and a lambda literal are the same node
(`Expr.block`), so `callDefBlk` builds the block's type exactly as `lambdaLit` does — same
index into the same whole-program table, same captured environment. The only difference is
where the node sits, which is why tier 9b needed no new `Ty`.

### 1. `Ctx.blockTy`, and why a block goes to two places at once

Ruby passes a block **out of band** from the argument list, so it cannot ride in `argTys`.
`callDefBlk` therefore does two things with it, and Ruby does both:

- puts it in `Ctx.blockTy`, which is the only thing `yield` can read (`yield-arith`);
- offers it to `paramEnvB`, so a `&b` parameter can *name* it (`block-param-ampersand`).

A method may use either or both. `blockTy` is set on entry to the body and by nothing else —
in particular it is **not** inherited into a nested `callDef`, because a block does not
propagate to methods the body calls.

`paramEnvB` binds `&b` to `.nilT` when no block is passed, which is exactly Ruby
(`def run(&b); b; end; run` is `nil`) and is not a formality: `b` is in scope either way, and
a control checks that `run` with no block is rejected for the *right* reason (`nil.call`
raises `NoMethodError`) rather than because `b` was unbound.

Each `yield` is checked independently, at its own argument types — the same per-call-site
instantiation as everywhere else in this judgment. A control exercises that from the failing
side: `def t; yield("a"); end; t { |x| x + 1 }` raises `TypeError`, and nothing at the call
site or in the method body looks wrong.

**No assumption table on `callDefBlk`**, unlike `callDef`: a method that recurses while
passing a block exhausts `chk`'s fuel and is rejected. The two-pass machinery would have to
be keyed by the block type as well as the argument types, and no rung asks.

### 2. `return` inside a lambda: a function on the body's shape, not a rule for `.ret`

`lambda-explicit-return`'s lambda body is exactly `return x * 2`. The obvious rule — `.ret e`
synthesizes `e`'s type — is **unsound**, and clink 9's closing note predicted this:
`def f; return "a"; 2; end` would validate at `Int`, because `JudgeSeq` takes the *last*
statement's type and the `return` never lets the last statement run. Typing `.ret e` as
`.never` does not help for the same reason.

The fix is `bodyResult : Expr → Expr`, which matches the body's **whole shape**: a body that
is exactly `.ret (some e)` has result `e`, anything else is itself. A `return` anywhere other
than as the entire body still has no rule, so `seq [return "a", 2]` remains underivable — and
there is a control for precisely that program (`lambda { |x| return "a"; 2 }.call(1) + 1`,
which really raises `TypeError`), so the restriction is held in place by execution rather
than by argument.

Applied at `closCall`/`yieldExpr` only, because only a lambda rung asks. A *method* whose
body is exactly `return e` is still not typed. The general fix — a judgment that accumulates
return types across a body — is a real design and nothing needs it yet.

### 3. A gap closed that had been recorded since tier 6

`bareName`'s docstring has said since clink 5: *"there is no rule for a top-level `vcall`
that does name a defined method (`def get5; 5; end; get5`, no parentheses), because the
desugarer emits a `vcall` rather than an argument-less `send`."*
`lambda-explicit-return` is the first rung to trip over it — its `apply_twice` is called
without parentheses.

`vcallDef` closes it, and it is `callDef` at zero arguments, assume-then-verify included,
which is why `vcallAsm` came with it. It does not overlap `bareName` (which requires
`defGet?` to *miss*) nor `selfCall`/`selfSCall` (which require a `self`). The docstring now
records the closure instead of the gap.

### 4. One elaboration note

`chk`'s block-carrying arm matches `.send none m args (some (.block ps [] body))` for both
routes, with the lambda route guarded by `(m = "lambda" || m = "proc") && args.isEmpty`.
`Judge.lambdaLit`'s conclusion, however, has `[]` in the argument position, so the proof has
to turn `args.isEmpty = true` into `args = []` and `subst` it before the constructor applies.
`simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, List.isEmpty_iff]` does it.
Recorded because the alternative — splitting the arm in two so `args = []` is syntactic —
would duplicate the whole `callDefBlk` branch.

### What is left of tier 9 (9 rungs), all one thing

Every remaining rung is a block **passed to a builtin**: `block-each-int`,
`block-map-to-s`, `block-nested-map`, `block-two-params-inject`, `block-select-with-if`,
`block-sort-by-length`, `block-doend-with-block-local`, and the two `blockpass` forms
(`&:to_s`, `&double`). They need `PrimSig` to grow **higher-order** rows — a claim about what
`Array#map` *does with* a block, not merely about its argument types — which is a new kind of
row and probably a new relation, since the result depends on the block's return type
(`map`), the receiver (`each`), or the element type (`select`). `block-doend-with-block-local`
additionally needs `|x; y|` block-locals, which `lambdaLit`/`callDefBlk` currently refuse in
the pattern.

State after this clink: **90 rungs climbed** (tiers 1–8 complete, tier 9 at 10/22), 90/90
cross-checked against the real semantics, 43/43 negative controls rejected — three of the four
new ones *sound*, one per premise added — corpus agreement 0 disagreements, all six soundness
theorems axiom-clean (`propext`, `Quot.sound`).

---

## Clink 11 (2026-09-01) — a soundness fix, and tier 11: features in concert: 90 → 91

Two things, and the second found the first.

### 1. The bug: a block may not retype a captured local

`Ty.clos` captures locals **by value**, into a spine, and `closCall`/`yieldExpr` discarded the
body's outgoing environment. But a Ruby block captures **by reference**, so:

```ruby
def t; yield(1); end
a = 1
t { |x| a = "s" }
a + 1                  # TypeError: no implicit conversion of Integer into String
```

`validate` answered **`true`** on this. The caller still believed `a : Int` after the block
ran. Genuinely unsound, in code committed two clinks earlier.

The fix is `capIntact`, a premise on `closCall` and `yieldExpr`: every name in the captured
spine must have, in the body's *outgoing* environment, the type it had on entry. It is the
exact analogue of `callMethod`'s no-retyping premise for instance variables (clink 6), and the
general rule is worth naming because it has now been rediscovered three times:

> **A callee may not retype state its caller can still see.**

Ivars for methods (clink 6), captured locals for blocks (here), and — the same fact one level
up — branch environments at an `if` (clink 3, `corpus/042`). I had written the ivar version
myself and still did not apply it to closures. Recording the general form so the next
state-carrying construct inherits it rather than rediscovering it.

What it costs: a block that accumulates into an outer local at a *different* type is rejected.
At the *same* type it is fine — the value changes, the type does not — which is the common
case, and `xc-block-accumulates-capture` is the rung that pins it. Two known conservatisms,
both recorded in `capIntact`'s docstring: a captured name **shadowed by a block parameter** is
compared at the parameter's slot, so `a = 1; lambda { |a| a = 2 }.call(3)` is rejected
(harmless, no rung shadows); and the precise alternative — thread the body's outgoing
environment back out and *join* it with the caller's, since a block may run zero times, with a
fixpoint for `each` — is not built.

Cost to existing work: every `closCall`/`yieldExpr` derivation grew one `rfl`. Nothing else
changed, and all 90 previous rungs re-derive.

### 2. Tier 11: the tier that adds no feature

Ten new rungs, from a program a human reported: `class A; def a(&blk); blk.call(3); end; end;
A.new.a { |v| v }` did not validate. It is not an unmodeled tier — it is a **cross-product**
of tier 7 and tier 9b, with two independent blockers, both restrictions I had introduced:

1. **No rule covers an explicit-receiver send that carries a block.** `callMethod` requires
   `blk = none`; `callDefBlk` requires an implicit receiver. Isolated by removing the block
   (validates) and by moving the `def` to top level (validates) — each half works alone.
2. **Behind it, `closCall` requires `κ.selfTy = none`**, so `blk.call` *inside* an instance
   method body would be rejected even with (1) fixed. Isolated by passing the lambda as an
   ordinary argument, no block anywhere: the instance-method version fails, the top-level
   version validates. This one *was* documented (clink 9) along with its fix — put `selfTy`
   into `Ty.clos` beside the captured locals.

Blocker 1 I had not documented at all: `callMethod`'s docstring never mentions that it
excludes blocks. That is the miss.

**Why the ladder was blind to it.** No corpus rung combines a class with a block — tier 9's
`block-param-ampersand` is the *top-level* `def run(&b)`, and tier 7's sixteen rungs never
pass one. A corpus-driven ladder measures what the corpus asks for, so an uncovered
cross-product is precisely the shape of thing that goes unnoticed. Hence a tier whose entire
content is combinations: no new feature, deliberately.

The ten, and what each demands:

| rung | in concert | target |
|---|---|---|
| `xc-class-block-param` | t7 dispatch × t9b block | `true` |
| `xc-class-yield-ivar` | ivar spine × `blockTy`, from the `yield` side | `true` |
| `xc-lambda-in-ivar` | `Ty.inst` spine *holding* a `Ty.clos` | `true` |
| `xc-module-yield` | t8 `callSMethod` × block | `true` |
| `xc-inherit-implicit-block` | `mroGet?` walk × `blockTy` × `selfCall` | `true` |
| `xc-block-retypes-capture` | **the bug above** | `false`, unsafe |
| `xc-block-accumulates-capture` | `capIntact`'s boundary — **climbed** | `true` |
| `xc-ivar-array-map` | t5 array × t7 ivar × t9c `map` × the t7×t9 gap | `true` |
| `xc-module-applies-lambda` | cleanest single demand for `selfTy` in `Ty.clos` | `true` |
| `xc-block-retypes-ivar` | the ivar twin of the bug | `false`, unsafe |

One rung earned its keep before it existed: sketching `xc-block-retypes-capture` is what found
§1. That is the argument for this tier in one sentence.

**One program deliberately left out.** `super { |x| x * 3 }` is ordinary Ruby that CRuby runs
fine, but the difftest engine reports `sut_unsupported` — "zsuper with an explicit block" is
outside the **Lean semantics** fragment. A rung for it would attach a type to a program the
model cannot execute, which is the one thing `scripts/run_agreement.sh` exists to prevent. It
is a demand on `../lean/`, not on this checker, and is recorded in `AGENTS.md` §Frontier
instead. Worth noting that this is the first time the *semantics* rather than the checker was
the binding constraint on a rung.

**A near-miss in the generator, worth recording.** `xc-module-applies-lambda` was first written
as `expect_validate=False, false_reason="unsafe_program"` — but the program returns `7`; it is
safe, and its honest target is `true`. `R()`'s assertion cannot catch that (it only checks that
`expect_validate=False` comes *with* a reason, not that the reason is true), so the target was
wrong for a few minutes with nothing complaining. The agreement gate would not have caught it
either: the program agrees with CRuby whatever the target says. The only defence is reading
each `false_reason` against the program, which is now noted at `R()`'s docstring's demand that
every `unsafe_program` really raise.

State after this clink: **91 rungs climbed** (tiers 1–8 complete, tier 9 at 10/22, tier 11 at
1/10), 91/91 cross-checked against the real semantics, 43/43 negative controls rejected,
**corpus agreement 124/124 with 0 disagreements**, all six soundness theorems axiom-clean
(`propext`, `Quot.sound`).

---

## Clink 12 (2026-09-01) — tier 12: narrowing pressure (corpus only): 136 rungs

No checker change. Twelve new corpus rungs, all of which need a capability the checker does
not have, added deliberately to create ratchet pressure for it. Tier 12 is 0/12; both
negatives are correctly rejected; nothing regressed (91/91 derivations, 43/43 controls,
136/136 agreement).

### Why this tier exists

`Ty.nilable` and `Ty.union` are the two types this checker can **produce** but has no way to
**consume**. No `PrimSig` row takes either as a receiver and neither is `EqSafe` — which is
exactly *why* producing one is trivially sound (`Judge.if'`'s docstring makes that argument),
and also why almost every interesting program that produces one becomes untypeable. Tiers 4
and 5 recorded that as a cost, in three negative controls that measure it. This tier converts
the cost into a demand.

The framing that made it urgent: any check worth running quantifies over inputs — `argv`, a
file's contents — and an input's type is almost always `nilable` or a union. Without narrowing,
an open-world checker would type nothing. So narrowing is not a precision nicety; it is a
prerequisite for the capability the project actually wants.

### The finding: narrowing cannot be a syntactic rewrite

This is the part worth keeping, and it came out of reading the *desugared* forms rather than
the Ruby. Three of the twelve rungs exist specifically because surface syntax and desugared
syntax disagree about what is being tested:

**`case v when Integer`** becomes

```
seq (vasgn local __dt_t1 (var local v))
    (if (send (const Integer) "===" [var local __dt_t1])
        (send (var local v) "*" [int 2])      -- NB: v, not __dt_t1
        …)
```

The scrutinee is copied to a temp, the condition tests **the temp**, and the branch bodies use
**`v`**. So a rule that refines "the variable named in the condition" refines the wrong one and
leaves `v` a union. Narrowing needs to know the temp and `v` hold the same value — an
**aliasing** story, not a rewrite.

**`if x && x > 1`** puts an entire `seq` (temp assignment plus a nested `if`) in the *condition*
position of the outer `if`, and the then-branch again uses `x` rather than the temp. Two
consequences: the tested variable cannot be read off the condition's syntax, and a refinement
established *inside* a condition has to survive being carried out of it. Note also that
`x > 1` within the condition already needs `x` narrowed — the refinement is consumed in the
same expression that establishes it.

**`return 0 if x.nil?`** is a `.ret` inside an `if` inside a `seq`, and the refinement it
licenses applies to *everything after* the guard. That is narrowing by **elimination of a
branch that leaves**, not by being inside a branch — and it needs `JudgeSeq` to stop taking
the last statement's type unconditionally, which `bodyResult`'s docstring already explains the
naive `.ret` rule cannot fix soundly.

### Two demands entailed by narrowing but not themselves narrowing

- **Builtin class constants.** `Integer`/`String` in `is_a?`/`===` are `Expr.const`, and
  `Judge.constCls` only types constants for classes the *program declared*. Five rungs need
  `.clsOf` for a builtin.
- **A `nil?` row.** `nil?` is total on every object, so its honest `PrimSig` row wants `.any`
  on the receiver — precisely the wildcard receiver clink 1 declined to admit for `!` ("the
  general rule needs `.any` on the receiver and no rung asks for it"). Now a rung asks.

### One rung is a demand on an existing rule, not a new one

`narrow-union-in-ivar` cannot even *produce* its union today: `Judge.if'` requires the two
branches to **agree** on the ivar spine (`I₁ = I₂`, added in clink 6 for a good reason). A
class whose `initialize` assigns `@v` at `Int` on one path and `String` on the other is
therefore not typeable at all. That premise has to become a *join* once there is something
that can consume a union — which is the shape of the whole tier: narrowing is what makes
several deliberately-conservative earlier choices affordable.

### `subTy` finally has a job

`narrow-union-subclass` narrows `union(inst Dog, inst Animal)` by `is_a?`. The asymmetry is
the content: `is_a?(Dog)` must narrow an `Animal` away, while `is_a?(Animal)` must **not**
narrow a `Dog` away. That is subtyping, and `subTy` has sat in `Ty.lean` unused since the port
— clink 7 noted that inheritance did *not* bring it due (dispatch is by `mroGet?` walk, not
subsumption) and predicted a parameter annotation would. It turns out to be narrowing instead.

### The two negatives, and what each would catch

- `narrow-backwards-unsafe` — the branches use the *wrong* refinement. `pick(false)` returns
  `"s"`, the else branch runs, `"s" + 1` raises `TypeError`. **Any implementation that refines
  the two branches the wrong way round certifies this**, which is the single most likely bug in
  a narrowing rule.
- `narrow-absent-unsafe` — `a = []; x = a[0]; x + 1` raises `NoMethodError`. This is
  `narrow-nilable-truthy` with the guard *deleted*, which is the point: the guard is what makes
  that rung safe, not the indexing. Catches any implementation that treats `nilable T` as `T`
  where convenient.

### A note on ordering

The twelve are deliberately graded. `narrow-nilable-truthy` is the one to do first — its
desugared condition is a bare `var local x`, so it needs no aliasing and no new `PrimSig` row,
and it is a complete capability on its own. `narrow-guard-clause` and `narrow-and-guard` should
be last; they need machinery (`.ret` in statement position, refinement out of a compound
condition) that the simpler rungs do not.

Also recorded: every one of the twelve **agrees with CRuby under the Lean semantics**, which
was not a foregone conclusion — `case/when`, `is_a?`, `nil?`, `&&` and `return … if` are all
modelled. Unlike clink 11's `super { … }`, the semantics is not the constraint here; the
checker is.

State after this clink: **91 rungs climbed** of 136 (tiers 1–8 complete, tier 9 at 10/22,
tier 11 at 1/10, tier 12 at 0/12), 91/91 cross-checked against the real semantics, 43/43
negative controls rejected, corpus agreement **136/136 with 0 disagreements**, all six
soundness theorems axiom-clean (`propext`, `Quot.sound`).

## Clink 13 (2026-09-01) — tier 12a: narrowing, the two direct tests: 91 → 93

The first two rungs of tier 12, and the first time this checker can **consume** a `nilable`.
`narrow-nilable-truthy` (`if x` on a `nilable Int`) and `narrow-nilable-nil-check`
(`if x.nil?`) — deliberately the two whose desugared conditions name the local directly, so
neither needs aliasing, `subTy`, or a builtin class constant. 93 derivations, 48/48 controls,
136/136 agreement, six theorems axiom-clean.

### Narrowing lives inside `Judge.if'`, not in a second rule

The obvious design is a new constructor, `ifNarrow`, sitting beside `if'` and applying only
when the condition has a recognized shape. It was rejected for a reason that is about the
judgment being a *specification*: two rules for one syntactic form means the honest answer to
"what does this checker believe about `if`" requires reading both rules **and** knowing which
one `chk` reaches, and the second half of that is not in `Judge.lean` at all.

So `if'` itself types each branch in a narrowed environment:

```
Judge κ Γ I c σ Γc Ic →
Judge κ (narrowEnvs c Γc).1 Ic t τ₁ Γ₁ I₁ →
Judge κ (narrowEnvs c Γc).2 Ic e τ₂ Γ₂ I₂ → …
```

What makes this affordable is that **`narrowEnvs` is total and is the identity on every
condition it does not recognize**. Which turned out to be every condition in tiers 1–11: the
corpus's `if`s test literals (`if true`, `if nil`, `if 5`) or comparisons (`n <= 1`, `x > 2`),
and none is a bare local read or a `nil?` send. Concretely, all **91** previously committed
derivation terms in `Rungs.lean` compiled **unchanged** — `narrowEnvs .tru Γc` reduces to
`(Γc, Γc)` in the kernel, so the premise is definitionally the old one. That was the empirical
bet this design rested on, and it paid; had a single earlier rung had a bare-var condition, the
separate-rule design would have been the right call after all.

`ifNoElse` got the same treatment, and its *else* half is the part worth a second look: the
absent branch still contributes to what the code after the `if` sees, so the outgoing
environment is `joinEnv Γ₁ (narrowEnvs c Γc).2` — using `Γc` would be sound but less precise,
and using `.1` would be a bug.

### Three pieces, kept apart on purpose

- **`NarrowKind`** (`truthy` | `isNil`) — *which runtime test* the condition performs. One
  constructor per test rather than per syntax, because several forms perform the same test
  (`if x`, `unless !x`, `if x != nil`, …), and later rungs will add forms without adding kinds.
- **`NarrowCond c x k`** — the recognizer, as a *relation* in `Judge.lean`, with
  `narrowCond?` as its executable twin. Two constructors: `bareVar` and `nilQuery`.
- **`narrowEnvs c Γ : Env × Env`** — the total function above.

The restrictiveness of `NarrowCond` is itself content. A refinement is a claim about the value
of `x` **at the point the branch begins**, so the condition must be an expression whose
evaluation cannot rebind `x` in between. Both admitted forms are (a local read; a total
zero-argument builtin send to a local). The general side condition — "the condition assigns to
no local the refinement mentions" — is a premise this ladder has not had to *state* only
because no recognized form can assign at all. Whichever rung admits a compound condition
(`narrow-and-guard`) inherits the obligation to state it.

### The four refinements, and the one claim they all rest on

`truthyTy`/`falsyTy`/`isNilTy`/`nonNilTy`, in `Ty.lean`. Each is a projection *out of* a type
the grammar already had — narrowing never manufactures a new type — and all four rest on one
fact about Ruby: **the only falsy values are `nil` and `false`.** Not `0`, not `""`, not `[]`.

That is why `falsyTy` answers `.never` on `.int`, `.cls _`, `.arrayOf _`, `.inst …` and the
rest: if `x : Int`, the else-branch of `if x` **cannot run**, so typing it with `x : never` is
not reckless, it is the precise answer, and `Ty.never`'s existing role as the join's unit makes
the dead branch contribute nothing to the result type. Three deliberate imprecisions:

- `.bool` refines to `.bool` in **both** directions, because `Ty` has no singleton `true`/
  `false`. Harmless — `.bool`'s only `PrimSig` row is `!`.
- `.any` refines to `.any` throughout: the checker knows nothing about the value, so it learns
  nothing from the test.
- `isNilTy` is *not* `falsyTy`. `false.nil?` is `false`, so `nil?` does not see `false` as nil,
  and keeping the two functions separate is cheaper than arguing about where they coincide.

### `nil?` needed a guard, not a wildcard

`nil?` is total on every object in the standard library, so the honest `PrimSig` row is a
wildcard receiver — which is exactly what clink 1 declined to admit for `!` and clink 12
predicted would come due. It came due, and a wildcard is still wrong, for a reason specific to
this type language: a wildcard receiver also covers `.inst n ivars`, an instance of a class the
**program** declared, and a program may write `def nil?; 1 + "a"; end`.

So the row is `PrimSig.nilQuery : NilQSafe σ → PrimSig σ "nil?" [] .bool`, with `NilQSafe` a
new relation in exactly `EqSafe`'s shape. The guard reads "no user code can be reached through
this type": the builtin scalars, `.cls n`, `.arrayOf _`, and — the one recursive row —
`.nilable τ` **only when `τ` is safe**. That last row is what keeps `nilable (inst Dog)` out,
and `nilable (inst Dog)` is a type this checker really produces (index an `arrayOf (inst Dog)`).

Two controls pin it, and they are a pair: a `Dog` that overrides `nil?` with `1 + "a"`, reached
through `[Dog.new][0]`, which really raises `TypeError` and which a wildcard row would certify;
and the same program with an ordinary `Dog`, which is safe Ruby this judgment declines. The
precise version of the guard consults `κ.classes` for an actual override; no rung needs it.

### The five controls, three of which are polarity swaps

Narrowing is the first capability on this ladder whose **most likely bug is a swap**, so three
of the five new controls are the same program with one refinement reversed, each certified by an
implementation that gets that refinement backwards, and each genuinely raising:
`a = []; x = a[0]; if x then 0 else x + 1 end` (truthy/falsy swapped),
`… if x.nil? then x + 1 else 0 end` (isNil/nonNil swapped — the more tempting one, since "the
guard is true, so we are in the good case" is what `if x` trains), and `… x + 1` with no guard
at all. `a = []` throughout, so the `nil` branch is the one that actually runs and the semantics
labels the rejection *sound* rather than merely conservative. All three report
"sound: really type-stuck".

### What tier 12's remaining ten still want

Unchanged from clink 12's list, minus nothing: aliasing (`case v when Integer` tests a
desugarer temporary while the branch bodies use `v`), `is_a?`/`===` with `subTy` and `.clsOf`
for a class the program did not declare, narrowing an **ivar** rather than a local (which also
needs `if'`'s `I₁ = I₂` premise to become a join), a refinement established *inside* a compound
condition, and narrowing by a branch that `return`s. None of the ten is unblocked by this
clink; what is unblocked is the *shape* — the refinement site now exists, and later rungs add
`NarrowCond` constructors and refinement functions rather than restructuring `if'`.

State after this clink: **93 rungs climbed** of 136 (tiers 1–8 complete, tier 9 at 10/22,
tier 11 at 1/10, tier 12 at 2/12), 93/93 cross-checked against the real semantics, 48/48
negative controls rejected, corpus agreement **136/136 with 0 disagreements**, all seven
soundness theorems axiom-clean (`propext`, `Quot.sound`).

## Clink 14 (2026-09-01) — tier 12b: `is_a?`, and class membership: 93 → 95

`narrow-union-is-a` and `narrow-union-subclass`. The first is the rung that makes `Ty.union`
*usable*: before this clink nothing in this package could consume one. The second is the one
whose refinement is asymmetric, which is where the interesting soundness argument is. 95
derivations, 53/53 controls, 136/136 agreement, eight theorems axiom-clean.

### `is_a?` is a `Judge` rule, not a `PrimSig` row

`nil?` fit in `PrimSig` because its guard (`NilQSafe`) could be structural: refuse `.inst`
receivers outright and no user-written `nil?` is reachable. `is_a?` cannot afford that — the
whole point of `narrow-union-subclass` is narrowing a union of *program-declared* classes — so
its guard has to be the precise one: **for every `.inst n` component of the receiver type,
`n`'s MRO must not define `is_a?`** (`isADispatchOk`). That is a class-table lookup, and
`PrimSig` is a relation on `(receiver, name, argTys, result)` with no table in it. So `is_a?`
became `Judge.isAQuery`.

Worth stating the division that fell out, because it is the reusable part: **`isAQuery` types
the send at `.bool` and computes nothing about the answer.** Whether the receiver *is* a `C` is
`isAAnswer`'s job, and `isAAnswer` is consulted only by `narrowEnvs`, in the branch entitled to
learn from it. That is what keeps `x.is_a?(C)` an ordinary expression — storable in a local,
passable as an argument — while only an `if` draws a conclusion.

The argument is required to have type `.clsOf cn`, not to *be* a constant. `1.is_a?(5)` raises
`TypeError` ("class or module required"), inside the family, so that index is a soundness
requirement; it is a recorded control. Reading the class *name* for narrowing is separate and
does come off the syntax (`NarrowCond.isAQuery` matches `[.const cn]`) — consistent because the
only two rules that type a `.const n` both answer `.clsOf n` for the same `n`, and this
judgment has no rule for constant assignment.

### Builtin class constants, and why they are not `CTable` rows

`Integer`/`String` in `is_a?` are `Expr.const`, and `Judge.constCls` only types constants for
classes the program *declared*. The obvious fix — seed `CTable` with rows for the builtins — is
wrong, and sharply so: a `CTable` row carries method tables, and `ctorGet?`/`instClsGet?` would
then find the zero-argument allocator, so **`Integer.new` would validate**, and it raises
`NoMethodError`. Hence a separate rule, `Judge.constBuiltin`, licensing the class object's
*identity* and nothing else, with `clsGet? κ.classes n = none` as a premise so the two `const`
rules stay disjoint (a program that reopens `class Integer` goes through `constCls`).
`Integer.new` is a control.

### Answering `is_a?` **negatively** needs an argument, and here it is

`isATy`/`notATy` project a union member-by-member using `isAAnswer`, which returns
`some true`/`some false`/`none` (undecidable → the member is kept in *both* branches, the
conservative direction). The `some false` answers are the load-bearing ones —
`narrow-union-subclass` works only because an `Animal` is decisively *not* a `Dog` — and each
comes from a **complete** ancestor list:

- **For a builtin receiver:** `builtinAncestors`, a hand-written table of full `.ancestors`
  lists (`Integer, Numeric, Comparable, Object, Kernel, BasicObject`, …), checked against
  CRuby. Complete is the operative word: a missing entry is an unsoundness, not an
  imprecision. `.bool` is deliberately absent — `true` and `false` are instances of *two*
  classes, so `is_a?(TrueClass)` has no single answer for `Ty.bool`.
- **For a declared class:** `ancestors?`, walking `Cls.super?`, and answering `none` if the
  walk leaves the table (`class Dog < StandardError` really *is* a `StandardError`; a truncated
  chain must not license a negative answer).

The completeness of a declared chain rests on a fact about earlier tiers that had nothing to do
with `is_a?`: a class enters `CTable` only through `extendClasses` → `classMethods?` →
`mapM clsMember?`, and `clsMember?` reads only `def` and `def self.`. So a class body containing
`include M` makes `classMethods?` answer `none`, the class never enters the table, and the whole
program is untypeable. **Every class in this table therefore has no mixins**, and its real
ancestors are its declared chain plus `Object`/`Kernel`/`BasicObject`. This is recorded in
`ancestorsUp`'s docstring as an explicit obligation on whichever tier gives `include` a rule
(tier 10): at that moment a table class can have an ancestor the chain does not name, and
`isAAnswer`'s negative direction breaks.

### `subTy` still has no job

Clink 7 predicted a parameter annotation would bring `subTy` due; clink 12 predicted
`narrow-union-subclass` would. **Neither did.** Narrowing needs *class membership*, which is
the ancestor walk `mroGet?` was already built on, not `Ty`-level subsumption — the refinement
keeps or drops whole union members, and never has to ask whether one `Ty` is below another.
`subTy` has now been unused across nine tiers, which is starting to look like a finding about
this design rather than a gap in it.

### A `Rungs.lean` cost worth recording: `if'`'s conclusion is not injective

`narrow-union-subclass`'s derivation term has four written-out implicits (`Γc`, `Γ₁`, `Γ₂`,
`τ₁`, `τ₂`), where every earlier `if'` derivation on the ladder needed none. Two compounding
reasons, both structural rather than accidental:

1. **`narrowEnvs κ.classes c Γc` is in `if'`'s conclusion**, so it reduces only when both `κ`
   and `Γc` are known — and `Γc` comes from a *premise*. Every tier-4..11 rung got away with
   this because its condition visibly leaves the environment alone (a literal, or a `prim`
   whose `JudgeAll` is `.nil`), so `Γc` unified with `Γ`. `narrow-nilable-truthy` and
   `narrow-nilable-nil-check` are still in that class; `is_a?` (three constructors deep) is not.
2. **`joinT` and `joinEnv` are not injective**, so Lean cannot recover the branch types or
   branch environments from the *result* — and in this rung the premises cannot supply them
   either, because each branch's `.callMethod` reads its receiver's type *out of* the branch
   environment.

Writing them out turned out to be the right outcome rather than a wart: the four annotations
*are* a statement of what narrowing did (`Γ₁` has `v : Dog`, `Γ₂` has `v : Animal`, and the
join puts the union back), which is precisely what a reader of that rung wants to see.

### Five new controls

The `is_a?` polarity swap (`corpus/135` run as a control, so its rejection is labelled by
execution — `"s" + 1`, TypeError); a class that overrides `is_a?` with `1 + "a"`, which is what
makes `isADispatchOk` load-bearing; `1.is_a?(5)`; `Integer.new`; and one honest-cost control,
`1.is_a?(Numeric)` — safe Ruby declined because `Numeric` is not a `BuiltinCls` row.

### One rung's recorded target now looks wrong

`narrow-nilable-and-union` (`arr = [1, "a"]; v = arr[0]; if v.is_a?(Integer) then v + 1 else
v + "!" end`) targets `true`, and with this clink's rules it is **provably not certifiable, and
should not be**: `arr[0]` is `nilable (union Int String)`, so the else-branch's type is
`nilable (cls String)` and `v + "!"` would be `nil + "!"` if the array were empty —
`NoMethodError`. The program is safe only because *this* array has an element at index 0, which
needs index-and-length reasoning `Array#[]` deliberately does not do (`PrimSig.arrayIndex`).
Flagged rather than retargeted: the honest fix is either a second guard in the rung's Ruby or a
`false_reason`, and that is a corpus decision, not a checker one.

### What tier 12's remaining eight want

`case/when` (aliasing — the condition tests a desugarer temporary while the branch bodies use
the original name), narrowing an **ivar** (which also needs `if'`'s `I₁ = I₂` premise to become
a join), a refinement established inside a compound condition (`if x && x > 1`), narrowing by a
branch that `return`s, narrowing inside a block body, and the `nilable`+union rung above.

State after this clink: **95 rungs climbed** of 136 (tiers 1–8 complete, tier 9 at 10/22,
tier 11 at 1/10, tier 12 at 4/12), 95/95 cross-checked against the real semantics, 53/53
negative controls rejected, corpus agreement **136/136 with 0 disagreements**, all eight
soundness theorems axiom-clean (`propext`, `Quot.sound`).

## Clink 15 (2026-09-01) — tier 12c: the guard clause: 95 → 96

`narrow-guard-clause` — `return 0 if x.nil?` — the one narrowing idiom where **nothing
syntactically encloses the narrowed code**. 96 derivations, 56/56 controls, 136/136 agreement,
eight theorems axiom-clean.

### Why it is a `JudgeSeq` rule

```ruby
def first_or_zero(a)
  x = a[0]
  return 0 if x.nil?
  x + 1              # x : Integer here, and no `if` is around this line
end
```

Every other refinement on this ladder is applied by `Judge.if'` to a *branch*. This one is
applied to **the rest of the sequence**, because the fact being used — "the previous statement
did not fall through" — is a fact about statement order, and `JudgeSeq` is the only relation
that knows about order. So the rule is `JudgeSeq.guard`, matching the statement shape
`.if' c (.ret (some e)) none` in **non-final** position, and it swallows both the guard and
everything after it:

```
Judge κ Γ I c σ Γc Ic →                                    -- the condition
Judge κ (narrowEnvs κ.classes c Γc).1 Ic e ρ Γr Ir → Ir = Ic →   -- what the guard returns
JudgeSeq κ (narrowEnvs κ.classes c Γc).2 Ic rest τ Γ' I' →       -- the rest, narrowed
JudgeSeq κ Γ I (.if' c (.ret (some e)) none :: rest) (joinT ρ τ) Γ' I'
```

Three things in there are decisions:

- **`.1` for the returned expression, `.2` for the rest.** The guard's body runs where the
  guard *fired*; the rest runs on the path it let through. Swapping them is the obvious bug and
  is a recorded control (`return 0 if x.is_a?(Integer); x + 1` with `a = []`, NoMethodError).
- **`joinT ρ τ`.** This is the only place in the judgment where a value leaves a sequence from
  somewhere other than its last statement, and the type has to cover both exits.
- **`Ir = Ic`.** The returning path may not touch the ivar spine, because the spine this rule
  reports is the *rest*'s — an ivar written on the way out would be invisible to the caller's
  `Iout = Iself` check. No rung feels it; a guard returns a constant or a local.

`κ` rather than `κ.afterStmt` for the rest, because `extendClasses`/`extendDefs` are visibly
the identity on an `.if'`.

### What was *not* done, and why that is the point

**`.ret` still has no rule.** The temptation is to give `.ret e` the type of `e` and be done;
that makes `def f; return "a"; 2; end` validate at `Int` (`bodyResult`'s docstring has had this
warning on file since clink 10), and typing it `.never` fails identically, because `JudgeSeq`
takes the last statement's type either way. The general fix is a return-type accumulator
threaded through the whole judgment — a fifth piece of state, and a real design. Restricting
the rule to *one syntactic shape in non-final position* gets the rung with no new state at all,
and leaves `seq [ret "a", 2]` underivable. That is control (ee): the same program, rejected,
and the semantics confirms it really returns a String.

`bodyResult` (a `.ret` as a lambda's *entire* body) and `JudgeSeq.guard` (a guarded `.ret` in
statement position) are now the two places `.ret` is readable, and they do not overlap. A method
whose body is exactly `return e` is still not typed — nobody has asked.

### One cost, recorded: a heartbeat bump in `ChkSound.lean`

`chkSeq`'s guard pattern (`.if' c (.ret (some r)) none :: _ :: _`) **overlaps** the generic
`e :: e' :: es` arm, so Lean's match compiler builds a splitter that case-analyses `Expr`
several levels deep and `split at h` has to push the hypothesis through it. `chk_sound`'s mutual
block needed `maxHeartbeats 1000000` (from the default 200000); the file still checks in a few
seconds. Not a soundness knob — a heartbeat limit can only turn a proof into an error.

### Three new controls

The polarity swap above; the `.ret`-has-no-rule control; and a `guard` twin of
`fun-body-mismatch` — `return x + 1 if x.nil?`, where the *returned expression* is type-stuck on
exactly the path the guard selects, and nothing at the call site or after the guard looks wrong.

State after this clink: **96 rungs climbed** of 136 (tiers 1–8 complete, tier 9 at 10/22,
tier 11 at 1/10, tier 12 at 5/12), 96/96 cross-checked against the real semantics, 56/56
negative controls rejected, corpus agreement **136/136 with 0 disagreements**, all eight
soundness theorems axiom-clean (`propext`, `Quot.sound`).

## Clink 16 (2026-09-01) — tier 12d: narrowing an ivar, and joining the spine: 96 → 97

`narrow-union-in-ivar`. 97 derivations, 58/58 controls, 136/136 agreement, eight theorems
axiom-clean.

### This clink reverses clink 6's most deliberate restriction

`Judge.if'` has required the two branches to **agree** on the ivar spine (`I₁ = I₂`) since
tier 7. Clink 6's argument for that was explicit and good: a spine is not merely state, it is
part of the *type* of `self` (`Ty.inst`), and there is no pointwise widening of it that keeps
that type honest. The consequence was that

```ruby
class Holder
  def initialize(flag)
    if flag then @v = 1 else @v = "s" end
  end
  ...
end
```

was not typeable **at all** — not imprecisely typed, untypeable, because no spine described the
result. Clink 12 flagged this as the one tier-12 rung that is a demand on an *existing* rule.

The premise is now `joinSpine I₁ I₂ = I₃`, with `I₃` the outgoing spine. Clink 6's argument was
not wrong, it was *early*: widening `@v` to `union Int String` is honest exactly when a union is
something code can consume, and tiers 12a–12c are what made that true. The rung is the matched
pair — the widening in `initialize`, the narrowing in `describe` — and neither half is any use
alone.

**`joinSpine I I = I` definitionally**, which is why generalizing the premise cost **zero edits
to the 96 derivation terms already on file**: each of them discharges the new premise with the
same `rfl` it used for the old one. That property (`joinT τ τ` reduces to `τ`, key order taken
from the left spine) is worth keeping in mind if `joinSpine` is ever changed.

### The refinement had to learn which state it lands in

`narrowCond?` now returns the **`VarKind`** along with the name, and there are two consumers:
`narrowEnvs` (acts only on `.lvar`) and `narrowSpine` (acts only on `.ivar`). `.cvar`/`.gvar`
fall through both, which is the right answer rather than an omission — no rule in this judgment
types either.

`narrowSpine` differs from `narrowEnvs` in two ways, both forced by what a spine is:

- **There is no "not found" case.** An instance variable that was never assigned reads `nil`
  (`ivarGet?`'s `.getD .nilT`, `class-ivar-lazy-nil`), so a miss refines `.nilT` — and that is
  *informative*, not a shrug: `if @v.is_a?(Integer)` on a never-assigned `@v` types the
  then-branch with `@v : never`, i.e. as unreachable, which is exactly right. (Consequence
  worth knowing: `class H; def d; if @v.is_a?(Integer) then @v + 1 else 0 end; end; end` now
  *validates*, at `Int`, with the then-branch vacuous.)
- **`ivarSet` appends**, so refining a name the spine does not carry lengthens it. Harmless —
  the added binding is what `ivarRead` would have defaulted to, and the outgoing spine is
  `joinSpine I₁ I₂`, which puts it back.

`JudgeSeq.guard` got the same treatment for symmetry (a guard may test an ivar); its `Ir = Ic`
premise became `Ir = (narrowSpine …).1`, which `narrow-guard-clause`'s existing `rfl` still
discharges because its condition tests a local.

### The two controls, and the question the join raises

Widening a disagreeing spine instead of rejecting it invites one obvious worry: can a *method*
now retype an instance variable out from under its caller? No — `callMethod`'s premise is still
that the body's outgoing spine equals its incoming one, and `joinSpine` of two branches that
both say `@x : String` is `@x : String`, not `@x : Int`. Control (hh) is that program, and it
really raises `TypeError`. Control (gg) is the ivar polarity swap, which is a *separate* code
path from the local one and so needs its own control.

### A third `Rungs.lean` elaboration cost, and the pattern in all three

`narrow-union-in-ivar`'s derivation needs tactic mode plus nine written-out indices. The
reasons compound, and they are worth naming as one pattern, because they will recur at every
later rung that narrows inside a method body:

1. `joinT`/`joinEnv`/`joinSpine` are **not injective**, so the branch types, environments and
   spines cannot be recovered from `if'`'s conclusion (first seen at `narrow-union-subclass`).
2. `narrowEnvs`/`narrowSpine` need the condition's **syntax**, which only the conclusion
   supplies — so they cannot reduce while the premises are being elaborated.
3. `callMethod`'s body premise reads the method's syntax out of a `Defn` that a *later*
   premise's `rfl` produces (`mroGet? … = some (dc, d)`, then `d.body`), so the body's `Expr`
   is a metavariable when (2) needs it.

The fix is mechanical once seen: `refine` the conclusion (which solves the syntax), state the
non-recoverable indices, and leave each premise a hole. And the annotations read as a statement
of what the rung does — `@v` enters as a union, the branches see `Int` and `String`, and
`joinSpine` returns it to the union — so this is a legibility cost, not a soundness one.

State after this clink: **97 rungs climbed** of 136 (tiers 1–8 complete, tier 9 at 10/22,
tier 11 at 1/10, tier 12 at 6/12), 97/97 cross-checked against the real semantics, 58/58
negative controls rejected, corpus agreement **136/136 with 0 disagreements**, all eight
soundness theorems axiom-clean (`propext`, `Quot.sound`).

## Clink 17 (2026-09-01) — why tier 12's last four are not next (no code change)

Tier 12 stands at 6/12. This note records what the remaining six are blocked on, because two of
them are blocked on a **design** rather than on effort, and the cheap ways out are unsound in
ways worth writing down before someone tries them.

### Two are not narrowing work at all

- **`narrow-in-block`** needs `Array#each` **with a block**, which is tier 9's remaining demand
  (the receiver-directed iterator rules). Its narrowing (`if y` on a `nilable Int`) has worked
  since clink 13. Nothing about tier 12 blocks it.
- **`narrow-nilable-and-union`** is provably not certifiable and should not be — see clink 14's
  last section. `arr[0]`'s `nilable` survives into the else-branch, and the program is safe only
  because *this* array has an element at index 0. Its recorded target is wrong, not the checker.

### Two need aliasing, and here is why the cheap versions are unsound

`narrow-union-case-when` and `narrow-and-guard` both desugar to a **temporary assigned from the
tested local**, with the branch bodies using the original:

```
seq (vasgn local __dt_t1 (var local v))
    (if (send (const Integer) "===" [var local __dt_t1])
        (send (var local v) "*" [int 2])            -- v, not __dt_t1
        (if (send (const String) "===" [var local __dt_t1]) … ))
```

So refinement has to reach a name the condition does not mention. Four designs were considered
and three rejected:

1. **A `JudgeSeq` rule over the pair `(alias assignment, if)`.** Local, no new state, and it
   fails on exactly these rungs: `case` with two `when`s nests, and the *inner* `if` — which
   also tests the temp while its body uses `v` — sits inside the outer `if`'s else branch, where
   only `Judge.if'` is looking, and `Judge.if'` cannot see the enclosing sequence.
2. **Aliases in `Ctx`**, grown at statement boundaries the way `defs`/`classes` are. Attractive
   because the desugarer's alias assignment always *is* its own statement. Unsound in two ways
   that cannot be patched at that granularity: a stale alias survives into a method body (where
   a same-named local is a different variable), and an assignment nested inside an expression
   (`y = (v = 1) + 1`) is not a statement, so the alias is never invalidated.
3. **A `Ty.sameAs (name) (τ)` binding carried in `Env`**, with `Judge.var` stripping it. This
   one nearly works — `joinEnv` handles it correctly (two branches that disagree join to a
   `union`, which is not a `sameAs`, so the alias simply disappears), and reassignment of either
   name invalidates it. It breaks on **block capture**: `t = v; blk { v = "s" }; if
   t.is_a?(Integer) then v + 1 …` keeps the alias alive across a call that changed `v`'s
   *value*, and `capIntact` only requires the *type* to be intact. Fixing that means the three
   block-call rules must invalidate aliases for every captured name — three more soundness
   obligations in rules that already carry the subtlest ones on the ladder (clink 11).
4. **A fourth threaded state**, `Alias : List (String × String)`, indexed on `Judge` alongside
   `Γ` and `I`. This is the honest design: aliasing is *state*, it is created and destroyed by
   execution, and threading it is what makes invalidation structural rather than a list of
   places to remember. It is also a tier-7-scale change — roughly forty rules gain an index —
   and each rule needs a decision about whether the alias survives it.

**Deferred, deliberately, to (4).** The general lesson is the one this ladder keeps
rediscovering in new clothes: *state that a rule needs must thread, or the rule's soundness
becomes a list of places somebody has to remember.* Clink 6 learned it for ivars, clink 3 for
branch environments, clink 11 for captured locals; option (2) and option (3) are that same
mistake proposed for aliases.

### What is next instead

**Tier 9's iterator rules.** They are worth more per unit of effort than aliasing: nine tier-9
rungs (`each`/`map`/`select`/`inject`/`sort_by` and the two `blockpass` forms) plus tier 12's
`narrow-in-block`, and they need a genuinely new *kind* of rule — a builtin whose signature
mentions a block — rather than a new piece of state.

## Clink 18 (2026-09-01) — tier 9c: the builtin iterators: 97 → 108

The biggest single clink on the ladder: **eleven rungs**, and the first one where a rule for
one tier climbed rungs in three (tier 9's nine iterator rungs, tier 11's `xc-ivar-array-map`,
tier 12's `narrow-in-block`). 108 derivations, 67/67 controls, 136/136 agreement, ten theorems
axiom-clean. Mismatches 25 → **14**, and tier 9 is now at 19/22 — every rung it targets.

### `PrimSig` cannot state an iterator's signature, so the signature is split in two

An iterator's result depends on what its **block** returns, and that is not known until the
block's body has been typed. `PrimSig` relates a receiver type, a name and a list of *argument*
types to a result; there is nowhere in it for a block to go. So:

- **`iterParams?`** — given the receiver's element type and the call's arguments, at what types
  does the block's parameter list get bound? Needed *before* typing the body.
- **`iterResult?`** — given that the body came back at `ρ`, what does the call return? After.
- **`IterSig`** is the relation that joins them, one constructor per iterator, and
  `iterSig?_sound` is the lemma that the two functions never drift apart from it.

That split is the reusable idea: a *bidirectional* table, where half the row is read before the
subterm and half after. Anything higher-order added later (`Hash#each_pair`, `Enumerable#group_by`)
takes the same shape.

### The five iterators differ in exactly the way that matters

| method | block params | result |
|---|---|---|
| `each` | `[elem]` | the **receiver** |
| `map` | `[elem]` | `arrayOf` (block's return) |
| `select` | `[elem]` | `arrayOf elem` |
| `sort_by` | `[elem]` | `arrayOf elem`, **if** the block's return is `Comparable` |
| `inject(init)` | `[α, elem]` | `α`, **if** the block returns `α` |

Clink 12's prediction ("a single block rule would get three of five wrong") was right, and each
difference now has a control that fails without it: `[1,2].each { |x| x.to_s } + "!"` raises
`TypeError` because `each` answers the *array*, not the strings.

**`sort_by`'s side condition, and why the obvious justification for it is false.** The first
draft of this clink justified `Comparable ρ` with "`["a"].sort_by { |s| nil }` raises
ArgumentError". It does not — `nil <=> nil` is `0`, and that program sorts fine. The real
failure mode is a key type whose `<=>` is not total **across its own values**: a union
(`[1, "a"].sort_by { |x| x }` → `ArgumentError: comparison of Integer with String failed`,
*inside* the family) or a user class inheriting `Object#<=>`, which answers `0` for identical
objects and `nil` otherwise. Both verified against CRuby 4.0.5 before the docstring was
rewritten. `Comparable`'s three rows (`int`, `float`, `.cls "String"`) are exactly the types
this `Ty` can produce a genuinely ordered array of; a union is excluded *because* it is not one
constructor.

**`inject`'s accumulator is a fixed point**, and it needs two controls, one from each side.
From the inside: a block returning `Int` on one path and `String` on the other really does
change the accumulator's type between iterations, and no single `Ty` describes it. From the
outside: `inject`'s result is the initial value's type *only because* the block is required to
reproduce it — `[1,2].inject(0) { |acc,x| x.to_s } + 1` raises `TypeError`, and an
implementation that reported `init`'s type without checking the block would certify it. Same
assume-then-verify shape as `Judge.callDef`'s recursion, with the initial value as the candidate.

### `iterBlock` is cheaper than `closCall`, and the reason is worth keeping

The block is **syntactically present at the call site**, so its body is typed *right there*, at
`iterParams?`'s types. No whole-program block table, no `Ty.clos` index, no captured-environment
spine. Nesting therefore costs nothing (`block-nested-map`: the rule applies to itself), and the
`|x; y|` block-locals `Judge.lambdaLit` has always refused come free — `blockLocals` binds each
at `.nilT`, which is what Ruby does.

**No `κ.selfTy = none` premise**, unlike `closCall`/`callDefBlk`, and that omission is what
climbed tier 11's `xc-ivar-array-map`. Those two rules need the restriction because they build a
`Ty.clos` whose captured environment is only meaningful at a creation site this judgment can
describe. Here nothing is captured into a type and `κ` passes through unchanged, so `self`
inside the body *is* `self` outside it — exactly Ruby. An iterator may therefore appear inside a
method body, over an ivar receiver.

**`capIntact` over the enclosing environment**, and the argument for carrying `Γ₂` out unchanged
is a two-sided one worth spelling out, because either half alone would be wrong: a block may run
**zero** times (an empty receiver), so the outgoing environment cannot be the body's; and
`capIntact` says the body changed no outer name's *type*, so it cannot be wrong to use the
incoming one. `narrow-in-block`'s `s = s + y` sits exactly on that boundary — the value changes,
the type does not — and `a = 1; [1,2].each { |x| a = "s" }; a + 1` is the control on the other
side of it.

### The two `&` forms, and one pleasing result

`map(&:to_s)` needed **no new claim about types at all**. `Symbol#to_proc` builds a
one-parameter callable that sends that name to its argument, so the block's return type is the
result of a send — and this judgment already has a table of those. `iterSymPass`'s premise is
`PrimSig β s [] ρ`: the *same* row `map { |x| x.to_s }` uses, reached from the other syntax. The
control that this reads a table rather than assuming totality is `[1,2].map(&:foo_bar)`, which
really raises `NoMethodError`.

`map(&some_lambda)` is `closCall` with the argument types supplied by `IterSig` instead of by a
call site; the `&` expression is typed after the receiver and the arguments (Ruby's order), and
what `capIntact` protects there is the `cap` *spine*, because a value-level callable really did
capture into one.

### **A cross-check bug this clink found: the two legs were running different models**

The most important thing in this clink is not a rule. `Semantics/Interp.lean`'s `run` was
`Interp.run fuel (Machine.init p)`, and its docstring claimed this was "the same `Machine.init`
the real `rubycore` executable and the difftest engine use". **It was not.** The difftest SUT
boots the prelude (`Prelude.initWithPrelude`) — RubyCore's core library written *in RubyCore*,
which is where `Enumerable#select` and `Enumerable#sort_by` live — and `Machine.init` does not.

So for eleven clinks, `checkrungs` was validating hand-derived types against a **strictly
smaller model** than `run_agreement.sh` was comparing to CRuby. It went unnoticed because
nothing below tier 9c reached a prelude-defined method. `block-select-with-if` and
`block-sort-by-length` are the first, and they came back
`unsupported(unmodeled method Array#select)` from `checkrungs` while the agreement gate reported
136/136 agree — two numbers disagreeing about the same model, which is precisely what the
two-legged design exists to surface.

Fixed: `run` now boots the prelude, with `Prelude.boot` hoisted into a nullary `def` so the
~200k-step boot is paid once per process rather than per rung (the whole run still takes ~2s). A
boot failure is reported as `unsupported` rather than falling back to the unbooted heap — a
cross-check against the wrong heap is worse than no cross-check, which is the lesson this bug
teaches. Both rungs now confirm, and no other rung's verdict changed.

The generalisable point: **a cross-check is only as good as its agreement with the thing it
claims to be checking**, and "the same X the real engine uses" is a claim that should be
mechanically true (a shared function) rather than asserted in a docstring. `run` calling
`Prelude.initWithPrelude`'s own body inline is a step toward that; sharing the function outright
would be better and is not free, because `initWithPrelude` re-boots per call.

### Two `Ty` gaps re-confirmed, neither new

`{"a" => 1}.map { |p| p }` is safe Ruby that no iterator rule types, because `iterBlock`
requires an `arrayOf elem` receiver and `Ty` has no `hashOf` to read an element type out of.
That is the third recorded gap (clink 4), now with a second symptom. And `proc-arity-leniency`
remains the arity gap; tier 9's 19/22 is *every* rung it targets, the other three being two
`unsafe_program`s and that gap.

State after this clink: **108 rungs climbed** of 136 (tiers 1–8 complete, tier 9 at 19/22 —
every targeted rung, tier 11 at 2/10, tier 12 at 7/12), 108/108 cross-checked against the real
semantics **on the prelude-booted heap**, 67/67 negative controls rejected, corpus agreement
**136/136 with 0 disagreements**, all ten soundness theorems axiom-clean (`propext`,
`Quot.sound`).

## Clink 19 (2026-09-01) — tier 11: a closure remembers its `self`: 108 → 110

`xc-lambda-in-ivar` and `xc-module-applies-lambda`. 110 derivations, 69/69 controls, 136/136
agreement, ten theorems axiom-clean. Mismatches 14 → 12, tier 11 at 4/10.

### The premise that was constraining the wrong thing

`Judge.closCall` carried `κ.selfTy = none`, and `lambdaLit`/`callDefBlk`/`yieldExpr` carried it
too. `lambdaLit`'s docstring said honestly what it was for and named the fix:

> A closure's body sees the `self` of wherever it was *created*, and this rule records the
> captured *locals* but not the captured `self`. … Lifting this means putting `selfTy` in
> `Ty.clos` beside the captured locals.

The trouble is that `closCall`'s copy of the premise constrains the **call** site, which is not
a property of the closure at all. `@f.call(v)` inside `Box#apply` is a call from a place where
`self` is a `Box`, and the lambda in `@f` was made at top level — perfectly fine, and
underivable. Two of tier 11's rungs are exactly that.

So `Ty.clos` gained a third field: the creation site's `self`, encoded as a `Ty` (a `Ty` field
must be one) with **`.never` meaning "created where `self` was not typed"**. `closSelf?` and
`closSpine` decode it, and `Ctx.inClosure` builds the context a body is judged in.

### Both halves of the fix are needed, and the second is the easy one to miss

`closCall` now judges the body in `κ.inClosure σ` **at `closSpine σ`** — the creation object's
instance variables, not the caller's. Getting only the `self` right and leaving the spine as the
caller's would be unsound, and the control says so concretely: a lambda created in an `A` whose
`@v` is a String, invoked in a `B` whose `@v` is an `Integer`, with body `@v + 1`. It computes
`"s" + 1` and raises `TypeError`; a rule reading the caller's spine sees `@v : Integer` and
certifies it.

The invariant that makes one field enough: **where `κ.selfTy = some (.inst n I)`, the threaded
spine *is* `I`** — every body-entering rule (`callMethod`, `selfCall`, `callSMethod`) maintains
it. So `closSpine` can recover the spine from the `self` type.

### What crosses the boundary and what does not

Stated once, because it is the rule of thumb for anything closure-shaped: **a closure body's
`self` and instance variables come from where the closure was *made*; its class and method
tables come from where it is *called*.** The second half is not laziness — Ruby resolves a
method call inside a block at call time, so a body that calls a method defined after the block
literal but before the invocation works, and carrying the call site's tables models that.

Two things are cleared rather than carried, both conservatively, and both recorded as controls
rather than argued away: `frame` (so a `super` inside a closure body has no rule) and `blockTy`
(so a `yield` inside a closure body has no rule, even though Ruby resolves it to the enclosing
method's block). Control (rr) is that program — safe Ruby returning `3`, declined. Making
either precise means recording it in `Ty.clos` too, exactly as `selfTy` now is.

### `callDefBlk` keeps its premise, doing a different job

`κ.selfTy = none` stays on `callDefBlk`, and after this clink it means something else: not
protecting the block (the block's creation `self` is now in its type) but keeping the rule
**disjoint from implicit-self dispatch**. Inside a method body a bare `foo { … }` resolves
against the object, not the top-level `defs` table — which is what tier 11's remaining four
rungs need, and is the next clink.

### Cost: an arity change across the package, and why it was cheap anyway

`Ty.clos` going from two fields to three touched `Ty.lean`, five `Judge` rules, four `chk`
arms, three `chk_sound` arms, `Main.lean`'s renderer, `CheckRungs.lean`'s `expectedClasses`,
and eleven `Rungs.lean` derivations — but every one of those edits was mechanical (`.clos i c`
→ `.clos i c .never`, and dropping one `rfl` from three rules' premise lists), and the type
checker found all of them. Worth contrasting with clink 17's rejected designs: the reason *that*
change was refused and this one was not is that this one puts the fact **in the data** where the
kernel can see every use site, rather than in a list of places somebody has to remember.

State after this clink: **110 rungs climbed** of 136 (tiers 1–8 complete, tier 9 at 19/22,
tier 11 at 4/10, tier 12 at 7/12), 110/110 cross-checked against the real semantics, 69/69
negative controls rejected, corpus agreement **136/136 with 0 disagreements**, all ten
soundness theorems axiom-clean (`propext`, `Quot.sound`).

## Clink 20 (2026-09-01) — tier 11: a block reaching a method of an object: 110 → 114

`xc-class-block-param`, `xc-class-yield-ivar`, `xc-module-yield`,
`xc-inherit-implicit-block`. **Tier 11 is now at 8/10 — every rung it targets.** 114
derivations, 73/73 controls, 136/136 agreement, ten theorems axiom-clean. Mismatches 12 → **8**.

### Three rules, no new idea in any of them

Each is its block-less twin plus `callDefBlk`'s two moves — build the block's `Ty.clos`, and
put it in **both** `blockTy` (so `yield` can reach it) and `paramEnvB` (so a `&b` parameter can
name it):

| new rule | twin | receiver |
|---|---|---|
| `callMethodBlk` | `callMethod` | `.inst n Iself` |
| `callSMethodBlk` | `callSMethod` | `.clsOf n` |
| `selfCallBlk` | `selfCall` | implicit, inside a method body |

The reason they were missing is the reason tier 11 exists: tier 9 wrote the block-carrying call
rule for the **top-level `defs` table only**, so `A.new.a { … }` — a class and a block, both of
which had rules for years — was underivable, and a corpus-driven ladder could not see it
because nothing in the corpus combined them. Clink 11 found this by hand; this clink closes it.

`selfCallBlk` also gains something `selfCall` does not have: **arguments**. `selfCall` has none
because a *bare* name is the zero-argument form and a `vcall` node has nowhere to put a block —
so the moment a block is involved the node is a `send none m args (some block)`, and there is no
reason to restrict `args`.

### `xc-inherit-implicit-block` is the densest rung in the corpus, and needed nothing new

`wrap { 7 }` inside `Child#show`: an implicit-receiver send, carrying a block, inside a method,
dispatching to an **inherited** method. `selfCallBlk` finds `Base#wrap` by tier 7's ordinary
`mroGet?` walk; the block — written inside `Child#show`, so with creation `self`
`.inst "Child" ivar0` — travels down to a `yield` in the parent's body, where clink 19's
creation-`self` field is what judges its body correctly. Three tiers' mechanisms meeting with
nothing added to any of them, which is the outcome a cross-product tier is *supposed* to have.

Worth tracing `xc-class-yield-ivar` for the same reason: `@n` is read from the **object's**
spine inside `bump`, passed as an argument to a block whose body is judged against the
**block's** creation `self`. Two different `self`s in one derivation, each used where it
belongs — which is only expressible at all because of clink 19.

### A latent soundness bug, fixed in passing

`callDefBlk` captured `envToSpine Γ` — the environment *before* the arguments — into the
block's `Ty.clos`. A block captures locals by reference and the arguments are evaluated before
the block ever runs, so an argument with an effect must be visible inside the block:

```ruby
x = 1
t(x = "s") { x + 1 }      # the block sees x : String
```

would capture `x : Int` and certify a program that raises. Fixed to `Γ'` (post-arguments), and
the three new rules copy the corrected version. No rung has an argument with an effect, so this
was a latent bug rather than a wrong number — recorded because it is the third time on this
ladder that "which environment does this rule mean" has been the whole question (clink 3's
branch join, clink 11's `capIntact`, this).

### One conservatism, deliberate and asymmetric

The method routes refuse a block with `|x; y|` **block-locals** (`locs = []` in the
conclusion), because the block becomes a `Ty.clos` and `Clos` records only `(params, body)`.
The *iterator* route (clink 18) admits them, because it types the block where it stands and
never builds a `Ty.clos` at all. That asymmetry is real and is recorded as control (vv) — safe
Ruby, declined; lifting it means recording the locals in `Clos`.

A small `chk` note that mattered for the proof: the guard is written `match locs with | [] =>`
rather than `if locs.isEmpty then`, because the match **substitutes** `locs := []` and so makes
the rules' `.block ps [] body` conclusion available to `split at h` without a separate
`isEmpty`-to-equation step.

### What is left, and it is now a short list

Eight mismatches: **tier 10's five metaprogramming rungs** (`include`/`extend`/`prepend`, class
reopening, `method_missing`) and **tier 12's three** — two needing the aliasing design clink 17
deferred, and `narrow-nilable-and-union`, whose recorded target is wrong (clink 14).

State after this clink: **114 rungs climbed** of 136 (tiers 1–8 complete, tier 9 at 19/22 and
tier 11 at 8/10 — every targeted rung in both, tier 12 at 7/12), 114/114 cross-checked against
the real semantics, 73/73 negative controls rejected, corpus agreement **136/136 with 0
disagreements**, all ten soundness theorems axiom-clean (`propext`, `Quot.sound`).

## Clink 21 (2026-09-01) — tier 10a: class reopening was a bug, not a feature: 114 → 115

`metaprog-class-reopening`. 115 derivations, 75/75 controls, 136/136 agreement, ten theorems
axiom-clean. Mismatches 8 → 7.

The finding is the whole clink: **this rung was filed under metaprogramming and is not
metaprogramming at all.** A reopened class is the same thing a class always was; the table was
simply wrong about it.

`extendClasses` prepended a fresh `Cls` for every `class` statement, and `clsGet?` is a
`find?`. So

```ruby
class Foo; def a; 1; end; end
class Foo; def b; 2; end; end
Foo.new.a + Foo.new.b
```

gave `Foo` the methods `[b]` and not `[a, b]` — the second statement *shadowed* the first — and
the program was untypeable. Not conservative: wrong. `mergeCls` accumulates instead.

Three decisions in `mergeCls`, each with a control or a note:

- **The later body's methods go first**, because `defGet?` is a `find?` and a redefinition must
  win over what it replaces. Reversed, `class Foo; def a; 1; end; end; class Foo; def a; "s";
  end; end; Foo.new.a + 1` would validate; it raises `TypeError`. Control (ww).
- **A missing `< Bar` does not erase an inherited superclass** (`c.super?.orElse old.super?`).
  Ruby actively *rejects* a reopening that names a different superclass; this function would
  silently take the later one, which no rung exercises and which is recorded in the docstring
  rather than guarded.
- **The merged entry is prepended rather than replacing in place.** The stale entry is
  unreachable (`clsGet?` finds the new one first), which keeps the function a one-liner, and it
  only makes `mroGet?`/`ancestors?`'s `C.length` budget more generous.

The reason accumulation is safe to model this way at all is a property tier 6 built for a
different purpose: the table grows in **`JudgeSeq.cons`**, statement by statement, so a call
placed *between* the two `class` statements still sees only the first body. Control (xx) is that
program, and it really raises `NoMethodError`. A whole-program scan would have needed an
argument; statement threading needs none.

State after this clink: **115 rungs climbed** of 136, 115/115 cross-checked, 75/75 negative
controls rejected, corpus agreement **136/136**, all ten soundness theorems axiom-clean.

## Clink 22 (2026-09-01) — tier 10b: `include` and `extend`: 115 → 117

`metaprog-include`, `metaprog-extend`. 117 derivations, 80/80 controls, 136/136 agreement,
ten theorems axiom-clean. Mismatches 7 → 5, tier 10 at 3/6.

### The dispatch change is small; the soundness obligations are the work

Both derivations are their tier-7/tier-8 twins **unchanged** (`callMethod`, `callSMethod`). All
the reach is in the lookup: `Cls` gained two fields, `lookupUp` gained one step, and
`clsMember?` two rows. What the clink actually cost was three separate soundness arguments.

**1. `Cls.includes` vs `Cls.extended` — one asymmetry, and it *is* `extend`.** `include` puts a
module's **instance** methods into instance dispatch; `extend` puts the *same* instance methods
into **singleton** dispatch. So `mixinGet?` serves both directions — both read `.methods` — and
only the table consulted at the call site differs (`mroGet?` reads `includes`, `smroGet?` reads
`extended`). The two controls are the two mistakes: an instance must not get an extended method
(`P.new.shout`), and the class object must not get an included one (`P.greet`). Both really
raise `NoMethodError`. Order: the list is searched **reversed**, because a later `include` wins
in Ruby.

**2. `include` on a non-Module raises `TypeError`**, which is *inside* the family. So
`Judge.classStmt`/`moduleStmt` gained an `allModules κ.classes (incs ++ exts) = true` premise.
Without it, `class P; include SomeClass; end; P.new.a_method_of_SomeClass` dispatches happily
and certifies a program that raises before it ever gets there — control (yy). The premise also
refuses a name the table does not know, which is stricter than Ruby (a module from another
file); this judgment has no notion of another file, and a name it cannot resolve is a name whose
`isModule` it cannot check.

**3. The obligation clink 14 wrote down came due, and it was real.** `isAAnswer` answers
`is_a?` **negatively** off `ancestorsUp`'s chain, and clink 14's argument for that being sound
was: *a class enters `CTable` only if `classMethods?` could read its whole body, and
`classMethods?` reads only `def`s — so no class in the table has mixins.* This clink makes
`classMethods?` accept `include`, so that argument evaporates.

Control (bbb) is what it looks like when it does:

```ruby
module M; end
class P; include M; end
x = P.new
if x.is_a?(M) then x.nope else 0 end
```

`x` really *is* an `M`, so the then-branch runs and `x.nope` raises `NoMethodError`. Under a
module-blind chain, `isAAnswer` answers `some false`, `isATy` refines `x` to `.never`, the whole
then-branch goes vacuous (`joinT never Int = Int`), and the program **validates**. Fixed by
`ancestorsUp` naming `c.includes`.

And the fix needed its own guard, one level down: a module that *itself* includes another module
has an ancestor a one-level walk would omit. `mixinAncestors?` **refuses** such a module —
answering `none`, i.e. "chain unknown" — rather than under-reporting it. Control (ccc) is that
program, rejected. Making the walk properly recursive is a fuelled traversal nobody has needed.

The pattern here is worth naming, because it is the second time on this ladder: **a soundness
argument that rests on another rule's restriction has to be re-checked when that restriction is
lifted.** Clink 14 wrote the obligation down in `ancestorsUp`'s docstring; that is the only
reason it was not missed. `mixinAncestors?`'s docstring now carries the next one.

### One thing that did *not* need changing

`isADispatchOk` — the guard that `is_a?` reaches `Object#is_a?` rather than a user override — is
unchanged, and correctly so: it asks `mroGet?`, which now searches mixins, so a **module** that
defines `is_a?` is caught by the same lookup that finds any other method. A guard written in
terms of the dispatch mechanism rather than in terms of a syntactic restriction survives the
mechanism getting stronger.

State after this clink: **117 rungs climbed** of 136, 117/117 cross-checked, 80/80 negative
controls rejected, corpus agreement **136/136**, all ten soundness theorems axiom-clean.

## Clink 23 (2026-09-01) — tier 10c: `prepend`, and the MRO becomes a list: 117 → 118

`metaprog-prepend`. 118 derivations, 83/83 controls, 136/136 agreement, ten theorems
axiom-clean. Mismatches 5 → 4, tier 10 at 4/6.

### The structural change `prepend` forces

Up to tier 8, instance dispatch could be a **walk over `Cls.super?`**, because "the next place
to look" was always reachable from where you were. `prepend` breaks that:

```ruby
module Logger; def speak; "logged: " + super; end; end
class Person;  prepend Logger; def speak; "hi"; end; end
```

`Person.ancestors` is `[Logger, Person]`, so `Logger#speak` wins — and the `super` inside it has
to run **`Person#speak`**, which is not `Logger`'s superclass and which nothing about `Logger`
names. There is no walk from `Logger` that finds it.

So the ancestor order is built once as a list:

- **`mroList?`** — `prepends.reverse ++ (self :: includes.reverse)` per class, concatenated up
  the `super?` chain. `none` if the walk leaves the table, the same refusal `ancestorsUp` makes.
- **`searchMro`** — the first entry that defines the name, and which entry it was.
- **`afterInMro`** — everything after a given entry. This *is* `super`, stated as a list
  operation: not "the superclass of where I was declared" but **"keep going from where I was
  found"**. Tier 7's `c.super?` walk was the special case of that for an MRO with no mixins.

`Frame` gained **`recvClass`**, because `afterInMro` needs to know *which* MRO to resume in, and
`defClass` alone cannot say (a prepended module belongs to no hierarchy of its own).
`Ctx.inMethod` fills it from the `self` type; `Ctx.inCtor` takes it as an argument.

Singleton dispatch kept the old walk (`lookupUpS`) — there is no prepend form for it in this
model — which is why the two lookups are now visibly different functions rather than one with a
`sing : Bool` switch.

### `zsuper` needed a rule, and its arity premise is soundness

`super` with no argument list is a different `Expr` head (`Expr.zsuper`), and until now it had
no rule at all — `Judge.superCall`'s docstring said so. `Judge.zsuperCall` covers the case this
rung writes: a **parameterless** running method, where "forward my arguments" forwards nothing.

The arity premise is not tidiness. `zsuper` forwards the current method's arguments, so if the
two arities disagree Ruby raises `ArgumentError` — inside the family. `paramEnv d.params []`
forces the *target* to take none; `dcur.params = []` (recovered by looking the running method up
in the receiver's own MRO) is the other half. Control (fff) is
`class C < B; def f(x); super; end; end; C.new.f(2)`, which really raises.

The general rule wants the running method's parameter list at the types those locals hold *now*
— Ruby forwards current values, so a reassigned parameter forwards its new one — which means
putting the parameter list in `Frame` beside `methName`. Mechanical, since every body-entering
rule has the `Defn` at hand; no rung asks.

### **A near-miss worth recording: the rung nearly passed with its feature bypassed**

When `Cls` grew its third `List String` field, `mergeCls`'s positional `⟨…⟩` silently bound
`includes := prepends`. Consequence: `Logger` landed *after* `Person` in the MRO, dispatch found
`Person#speak`, the `zsuper` inside the module was **never reached**, and `validate` answered
`true`. The rung "passed" with the feature it exists to test entirely bypassed — and it would
have passed the `checkrungs` cross-check too, because the program's *result class* is `String`
either way.

Two things caught it, and it is worth being precise about which:

- Not the ratchet number, which went up.
- The **derivation term**. Writing `r112` by hand meant writing a `zsuperCall` premise, and that
  did not compile against a table where `zsuper` was never reached. This is the second time
  (clink 18's prelude bug was the first) that the hand-derivation requirement caught something
  the `Bool` was happy with, which is the argument for keeping it.

Fixes: `mergeCls` now uses **named** fields, so that class of mistake is a compile error; and
control (ddd)/(eee) pin the ordering by *execution* — the same program under `prepend` returns
`"m"` and under `include` returns `1`, and each raises when combined with the other's follow-up.

### `ancestorsUp` and `mroList?` now agree, and are still separate

Both compute the same list of names for a class with flat mixins. They are kept apart because
their `none`s mean different things: `mroList? = none` is "dispatch cannot proceed", while
`ancestorsUp = none` is "the ancestor chain is **incomplete**", which is the claim
`isAAnswer`'s negative direction rests on. Collapsing them would make one function carry two
obligations.

State after this clink: **118 rungs climbed** of 136, 118/118 cross-checked, 83/83 negative
controls rejected, corpus agreement **136/136**, all ten soundness theorems axiom-clean.

## Clink 24 (2026-09-01) — tier 10d: `method_missing`, and a table that must be complete: 118 → 119

`metaprog-method-missing-fixed-arity`. **Tier 10 is now at 5/6 — every rung it targets**, the
sixth being the permanent `ty_language_gap`. 119 derivations, 86/86 controls, 136/136 agreement,
ten theorems axiom-clean. Mismatches 4 → **3, all in tier 12.**

### The mechanics are `callMethod` with two edits

`Judge.callMissing` looks up `"method_missing"` instead of `m`, and pushes a **`.sym`** onto the
front of the argument list, because Ruby passes the missing name as a Symbol. That second edit
is also why tier 10 needed a `PrimSig` row for `Symbol#to_s` — the idiomatic body calls `to_s`
on the name immediately, and there was no row for it.

`paramEnv`'s length check then does the rest of the work for free, which is why
`metaprog-method-missing-fixed-arity` validates and its splat sibling stays a permanent
`ty_language_gap`: `def method_missing(name, *args)` has a parameter list no `Ty` describes. The
pair is the point — the gap is the *rest parameter*, not `method_missing` dispatch.

### The premise that matters is about when the rule does *not* fire

`mroGet? κ.classes n m = none` is the obvious guard (a fallback that can fire while an ordinary
method exists gives the wrong type for every call — control (hhh)).

`¬ ObjectMethod m` is the one that is easy to miss, and it is the interesting content of this
clink. This judgment's class table holds only what the **program** declared, so `mroGet?` misses
for `to_s`, `inspect`, `hash`, `==`, `class` — every method `Object` provides — and Ruby runs
*those*, not `method_missing`.

The failure mode without it is not a permissive rejection, it is a **wrong answer**. Control
(ggg):

```ruby
class G; def method_missing(n); 5; end; end
G.new.to_s + 1
```

`Object#to_s` returns a String, so this raises `TypeError`. Route it to `method_missing` and the
checker says `Integer`, accepts `+ 1`, and has mis-typed a value's class. Every other unsoundness
on this ladder has been "accepts a program that raises"; this one is "reports the wrong type",
which is worse in the sense that it would propagate.

### `ObjectMethod` is the one table here whose *completeness* is the soundness condition

Worth stating as a general point, because it inverts the convention every other table on this
ladder follows. `PrimSig`, `IterSig`, `BuiltinCls`, `NilQSafe`, `Comparable` are all lists of
things the checker is **willing to claim** — a missing row costs a rung, and the direction of
error is conservative. `ObjectMethod` is a list of names the checker must **refuse** to claim, so
a missing row is an unsoundness and the direction of error is *not* conservative.

Handled by generation rather than by judgement: the 51 names in `Object.new.methods` under CRuby
4.0.5, plus six (`initialize`, `initialize_copy`, `initialize_clone`, `initialize_dup`,
`method_missing`, `respond_to_missing?`) that are private or protected — so absent from that list
— but still defined on `Object` and still reached first. The docstring carries the regeneration
command and says explicitly which direction of drift is dangerous: a name a future Ruby *adds*
to `Object` and that is not added here.

Stated as data (`objectMethodNames : List String`) with a one-constructor relation over it, so a
derivation discharges the premise with `not_objectMethod rfl` and the `rfl` is the kernel
checking the name against the list — rather than fifty-seven constructors and a case split.

### What is left: three rungs, and none of them is tier 10 or tier 11

- `narrow-union-case-when` and `narrow-and-guard` — the aliasing design clink 17 deferred to a
  fourth threaded state.
- `narrow-nilable-and-union` — whose recorded target is wrong, per clink 14.

Tiers 1–8 are complete; tiers 9, 10 and 11 are at *every rung they target*.

State after this clink: **119 rungs climbed** of 136 (tier 9 at 19/22, tier 10 at 5/6, tier 11 at
8/10, tier 12 at 7/12 — the fractions below 1 being the eleven permanent negatives and the two
`Ty` language gaps, plus tier 12's three), 119/119 cross-checked, 86/86 negative controls
rejected, corpus agreement **136/136**, all ten soundness theorems axiom-clean.

## Clink 25 (2026-09-01) — tier 12: aliasing, and `case`/`when`: 119 → 120

`narrow-union-case-when`. 120 derivations, 90/90 controls, 136/136 agreement, ten theorems
axiom-clean. **Mismatches 3 → 1**, and the one left is `narrow-and-guard`.

### Clink 17 deferred this and named the design; the design turned out to be design (3), fixed

Clink 17 listed four ways to make `case v when Integer` narrow `v` when the condition tests a
*temporary*, rejected three, and deferred to the fourth (a fourth threaded state). The one it
rejected as "nearly works" was `Ty.sameAs (name) (τ)` carried in `Env`, and the reason for
rejecting it was **block capture**:

> It breaks on block capture: `t = v; blk { v = "s" }; if t.is_a?(Integer) then v + 1 …` keeps
> the alias alive across a call that changed `v`'s *value*, and `capIntact` only requires the
> *type* to be intact.

That is exactly right, and it is fixable in one line per rule rather than by threading a fifth
index: **the rules that carry a caller's environment out across a block call apply
`killAliases` to what they carry out.** There are eight of them — `closCall`, `yieldExpr`,
`iterBlock`, `iterClosPass`, `callDefBlk`, `callMethodBlk`, `callSMethodBlk`, `selfCallBlk` —
which is *every* rule in the judgment through which a block body can run, and the list is
closed because a method body cannot see the caller's locals at all.

What made design (3) worth revisiting rather than paying for the fourth index: clink 17's own
lesson was *state a rule needs must thread, or its soundness becomes a list of places somebody
has to remember*. The environment **already threads**. Putting the alias in the environment's
value type gets the threading for free, and — the part clink 17 missed — makes every place that
could invalidate an alias a place that **already writes to the environment**. That is what turns
"a list of places to remember" into a finite, readable enumeration.

### The invalidation argument, in full, because it is the whole soundness story

An alias `t ~ v` can go stale in exactly four ways:

1. **`t` is reassigned.** The binding is overwritten; nothing needed.
2. **`v` is reassigned.** `Judge.vasgn`'s conclusion is
   `envSet (killAliasesTo Γ' x) x τ` — once `v` holds a new object, nothing else holds the same
   one. Control (jjj), which raises `TypeError`.
3. **A block reassigns `v`.** The eight rules above. Control (kkk) — and note the shape: the
   block reassigns `v` at the *same* union type, so `capIntact` passes and the type survives.
   Only the alias must not.
4. **One branch of an `if` does (2) and the other does not.** Nothing needed: the branch that
   invalidated has `v : τ` where the other has `t : sameAs v τ`, and
   `joinT (sameAs v τ) τ` is a **union** — which is not a `sameAs`, so the alias is simply gone
   at the join. `narrow-union-case-when`'s own outgoing environment shows this: `__dt_t1` leaves
   as a *union of aliases*, one per `when` arm, and therefore as no alias at all.

Case 4 falling out of the existing join is the strongest evidence that this is the right place
for the fact.

### `Ty.sameAs` is inert everywhere except `narrowEnvs`

`Judge.varAlias` reads an aliased name at the alias's **payload**, so no *expression* ever has
type `sameAs`: it is a fact about a binding, not about a value. Beyond that: no `PrimSig` row,
not `EqSafe`, not `NilQSafe`, not `Comparable`, `isADispatchOk` refuses it, `envToSpine` strips
it (so it never enters a closure's captured spine, where the target name could mean something
else), and `expectedClasses` answers `[]` so a rung that somehow claimed one would fail loudly.

### `Module#===`, and why it is not `is_a?` with the arguments swapped

`case v when C` desugars to `C === v`. The *answer* is the same ancestor test, so `narrowCond?`
produces the same `.isA` kind — but the **guard** is different, and getting that right is the
content of `Judge.caseEqQuery`. `Module#===` is implemented directly as the ancestor test; it
does **not** call `obj.is_a?`. So a user-written `is_a?` cannot affect it (`isADispatchOk` is
the wrong question here), while a `def self.===` on the class object can — which is what
`smroGet? cn "===" = none` excludes. Control (mmm).

### Two mechanical findings worth keeping

**A conclusion of the form `f τ` for a non-injective `f` cannot be unified with a concrete
type.** The first draft folded the alias strip into `Judge.var`'s conclusion (`stripAlias τ`),
and every one of the **137** `Judge.var` uses in `Rungs.lean` stopped elaborating. Splitting it
into `var` (with an `isAliasTy τ = false` premise, leaving the conclusion's `τ` a bare variable)
and `varAlias` cost one mechanical `rfl` per use site and nothing else. This is the same shape as
clink 16's `joinSpine I₁ I₂ = I₃` and clink 23's arity premise: **put the function in a premise,
not in the conclusion.**

**`String.isPrefixOf` is not axiom-clean.** The alias rule was first restricted to names
beginning `__dt_`, and `chk_sound`'s axiom list grew `Classical.choice` — Lean's
`String.isPrefixOf` is compiled by well-founded recursion and its termination proof needs it.
Replaced by `desugarTemps.contains`, a `List String` of whole names, which is choice-free like
every other table in the package. The direction of error if the desugarer ever emits a name past
the end of that list is conservative: no alias, the rung is not typed, and the ratchet says so.

### What is left: one rung

`narrow-and-guard` (`if x && x > 1`). The alias machinery handles the temporary, but the
condition is an entire `seq` in condition position, so `narrowCond?` cannot see it — the outer
`if`'s refinement has to come from a **compound** condition, which means `narrowCond?` returning
a *conjunction* of refinements and recognizing the `&&`/`||` desugaring.

State after this clink: **120 rungs climbed** of 136, 120/120 cross-checked, 90/90 negative
controls rejected, corpus agreement **136/136**, all ten soundness theorems axiom-clean
(`propext`, `Quot.sound`).

## Clink 26 (2026-09-01) — tier 12: `if x && x > 1`, and the ladder is climbed: 120 → 121

`narrow-and-guard`, the last rung. **`RATCHET OK`: every rung in the corpus matches its
recorded target.** 121 derivations, 92/92 controls, 136/136 agreement, eleven theorems
axiom-clean (`propext`, `Quot.sound`).

### Three separate things had to line up

```
if (seq (vasgn local __dt_t1 (var local x))
        (if (var local __dt_t1) (send (var local x) ">" [int 1]) (var local __dt_t1)))
   (send (var local x) "+" [int 1])
   (int 0)
```

**1. The refinement is consumed in the same expression that establishes it.** `x > 1` inside the
condition needs `x : Integer`, and it gets that from the **inner** `if`, whose condition is the
temporary — i.e. from clink 25's alias. Without aliasing this rung is not typeable at all, which
is why clink 12 filed both `&&` and `case/when` under the same finding.

**2. The outer refinement is one-sided.** A truthy `&&` means the *first* conjunct was truthy;
a falsy one could have been either conjunct, so the else-branch learns **nothing**. `NarrowSides`
(`both` | `thenOnly`) is that distinction — the first asymmetric refinement on the ladder.

And it is a **soundness** requirement, not caution, which was worth checking rather than
assuming. Control (nnn):

```ruby
x = 3
if x && x > 5 then 0 else x + "!" end
```

`3 > 5` is false, so the else-branch runs with `x` an ordinary `Integer` and `3 + "!"` raises
`TypeError`. Refine the else-branch and `x` gets `falsyTy Int = .never` — which makes the whole
branch **vacuous**: `x + "!"` becomes `.never` by strictness, `joinT Int never = Int`, and the
program validates. That is the sharpest control on the ladder for `Ty.never`'s dead-branch
reading (clink 13), because it is the one place that reading can be reached by a branch which is
*not* dead.

**3. The right conjunct must not assign to a local.** The refinement lands on the environment at
the **end** of the condition, and the condition's value is the *right* conjunct's — so
`x && (x = b[0]; true)` is truthy while leaving `x` `nil`. `noLocalAsgn` is a **whitelist**, and
that direction matters: a walk looking for `vasgn` would report a constructor it does not cover
as clean, whereas a whitelist reports anything it has not been taught about as unsafe. Control
(ooo) is that program, which really raises `NoMethodError`.

### A gap closed on the way: `NarrowCond` was decorative

`NarrowCond` has been in `Judge.lean` since clink 13 as the *specification* of the recognizer —
"evaluating this condition performs this test on this variable, **and** evaluating it cannot
invalidate the answer". Nothing tied `narrowCond?` to it. So the one human-checkable statement of
why each refinement is licensed was not load-bearing: `chk` could have recognized a shape the
judgment never licensed, and no proof would have noticed.

`narrowCond?_sound` closes it. Worth noting what it does *not* say: that the refinement
*functions* are right about Ruby. That is a claim about the semantics, and it is checked the way
every such claim on this ladder is — by executing the controls.

### State: the ladder is climbed

**121 rungs of 136**, and the 15 that are not climbed are not work items:

- **12 permanent negatives** (`unsafe_program`) — programs that really raise, kept as the
  soundness regression tests. A `true` on any of them is a bug.
- **3 `Ty` language gaps**, each naming a specific missing constructor: an optional/rest arity
  spine (`proc-arity-leniency`, `metaprog-method-missing-splat`) and a length-indexed array
  (`narrow-nilable-and-union`).

Tiers 1–8 complete; tiers 9, 10, 11 and 12 at every rung they target. 121/121 cross-checked
against the real semantics on the prelude-booted heap, 92/92 negative controls rejected, corpus
agreement 136/136 with 0 disagreements, and all eleven soundness theorems axiom-clean.

What the ratchet is *for* now changes: the number can no longer go up without new corpus rungs,
so the next move is more Ruby, not more rules. The three `Ty` gaps are the obvious sources, and
each one is a grammar extension with a rung already written against it.

## Clink 27 (2026-09-01) — tier 13a: where a constant lives: 129 → 130

`const-assign-read` (`LIMIT = 10; LIMIT + 1`), the smallest thing tier 13 is. Two new rules
(`Judge.casgn`, `Judge.constEnv`), one new field on `Ctx`, one new argument to
`Ctx.afterStmt`, and **three new premises on rules already on file** — which is where the
interest is: the premises, not the rules.

### The placement question, and why the three obvious answers are wrong

A constant is a binding, so it needs somewhere to live. The corpus rung's own description
predicted the shape of the argument, and got the conclusion half right:

> It cannot be folded into `Env` (locals shadow per-scope and constants do not) and it cannot
> be a pre-pass table (`chk` would then accept `X + 1; X = 10`, which raises NameError).

Three candidate homes, and each fails for a different, checkable reason:

1. **A syntactic pre-pass table** (what `CTable` and `DefTable` are, built by `extendClasses`/
   `extendDefs`). Fails twice over. A constant's *type* is not syntactic — `LIMIT = compute`
   needs the judgment to know what `compute` answers — and a whole-program table is
   order-blind, so `X + 1; X = 10` would certify. That program raises `NameError`.
2. **`Env`.** Fails on method bodies. `paramEnv` builds a *fresh* environment containing just
   the parameters, because that is what a Ruby method body sees; a constant assigned at top
   level is visible inside every method body regardless. Putting constants in `Env` means
   either they vanish at every call (so `def size; SIZE; end` is untypeable — the tier's
   second rung) or every call rule has to re-seed them, which is ten rules and every
   derivation on file.
3. **A fourth threaded component** (`Judge κ Γ I Σ e τ Γ' I' Σ'`). Correct, and unaffordable:
   it re-indexes every one of ~100 rules and all 129 derivation terms.

**`Ctx.consts` is the fourth answer and it gets all three properties without any of the
costs.** It is in `Ctx`, so `Ctx.inMethod`/`inCtor` and every `{κ with …}` in a call rule
carry it into the callee for free — and that is not a trick, it is the right semantics: a
constant assigned before the call really is assigned when the body runs. And it grows at
`JudgeSeq.cons`, the one rule that knows statement order, which is why `X + 1; X = 10` has no
derivation for exactly the reason `foo(); def foo; end` has none.

The price is one signature change: `Ctx.afterStmt` takes the statement's **type** now
(`κ.afterStmt e σ`), because that is what a `casgn` binds. `σ` is already bound in
`JudgeSeq.cons` (its first premise produces it) and in `chkSeq`, so the change is visible in
two places and in **zero derivation terms** — the extra argument is determined by unification.

Keys are the constant's absolute path, `"::LIMIT"`, which is Ruby's own notation and makes the
disjointness from `Env`'s locals syntactic rather than a convention: no local name contains a
colon. Nothing yet *reads* a nested path — `constKey` is a one-liner waiting for clink 28.

### `casgn` binds nothing, and `constEnv` is the third `const` rule

`Judge.casgn` types `X = e` at `e`'s type (Ruby's own answer: `(X = 10) + 1` is `11`) and
threads `Γ'`/`I'` straight through. It does **not** create the binding; `Ctx.afterStmt` does.
The consequence is deliberate: a `casgn` buried inside a larger expression types and is
invisible to later reads. Conservative, in the direction that costs a rung rather than
soundness.

`Judge.casgn` also has **no side condition at all**, which is worth stating rather than
leaving as an absence. A constant assignment cannot raise anything in the type-error family:
re-assigning an initialized constant is a *warning*, and so is assigning over a class's name.

### The three new premises, all soundness, all found by asking what breaks

The rules already on file assumed something that stops being true the moment `casgn` exists:
that a `const` naming a declared class *is* that class object. Four programs say otherwise,
and all four are now controls (p13a–p13d) run under the real semantics:

- `X = 5; class X; end` raises **TypeError** ("X is not a class"). Each statement is fine in
  isolation, so without a premise `chk` types both. → `classStmt` and `moduleStmt` grew
  `constGet? κ n = none`. Both print as *sound* rejections, i.e. the semantics agrees the
  programs really are type-stuck.
- `class X; end; X = 5; X.new` raises **NoMethodError**. Here the declaration comes first and
  is legal; what is illegal is the allocation, because `X` is `5` now. The class table still
  has an `X` row, so the old two-route `const` would have answered `.clsOf "X"`. →
  `constCls` and `constBuiltin` grew the same premise.

That premise is what makes the three `const` rules **disjoint rather than merely ordered**:
`chk`'s three-way `match` on `.const n` could be written in any order and answer the same,
and `chk_sound` supplies each rule's negative hypothesis from the arm that bound it.

Worth noting which direction the fix went. The alternative was a premise on `casgn`
(`clsGet? κ.classes n = none`), and it does not work: it cannot see a `class X` that comes
*later*. A whole-program pre-pass collecting every class name (the `collectBlocks` trick)
would, and was rejected for a sharper reason — for `collectBlocks` an unvisited constructor
merely fails to register a block, which is conservative, whereas for a name-collector an
unvisited constructor **hides a declaration**, and completeness over `Expr` would become a
soundness condition. The premises on the reading rules need no such argument.

`X + 1; X = 10` is control (p13d) and is the one that prints as *conservative*: `NameError`
is not in the `NoMethodError`/`ArgumentError`/`TypeError` family this package calls
type-stuck, so the semantics reports the program as safe even though Ruby refuses to run it.
The rejection is required by Ruby, not by our definition — recorded rather than smoothed over.

### State

**130 rungs of 232**, tier 13 at 1/13. 130/130 cross-checked against the real semantics,
96/96 controls rejected (four new), corpus agreement 232/232 with 0 disagreements, all
soundness theorems axiom-clean (`propext`, `Quot.sound`).

Next: `const-in-class` and the scoped forms, which need the two things this clink deliberately
did not build — a lexical nesting path (`Ctx.cref`) and a story for constants assigned in a
**class body**, which no rule judges today.

## Clink 28 (2026-09-01) — tier 13b: a class body's constants, and why they are typed where they are written: 130 → 133

`const-in-class`, `const-frozen-array`, `const-frozen-hash`. Clink 27 put constants in
`Ctx.consts` and grew the table at `JudgeSeq.cons`, which handles every constant assigned as
a **top-level statement**. A constant assigned in a *class body* is not one, and the
difference turns out to be the whole clink.

### The problem: `Ctx.afterStmt` gets the wrong type

`extendConsts` is called from `Ctx.afterStmt e τ`, where `τ` is the type of the statement
`e`. For `X = 10` that is exactly what is wanted — `τ` *is* the constant's type. For
`class Box; SIZE = 3; … end` it is `.any`, the type of a class statement, and nothing about
`SIZE` is anywhere in reach. The class body is not judged as a sequence; `classMethods?`
reads it *syntactically*, which is also how `extendClasses` builds the `CTable` row.

So the constant's type has to be readable off the initializer's **syntax**. That is
`constLitTy?`: the scalar literals, an array literal (element types joined by the existing
`elemTy`), a hash literal, and `.freeze` of any of them.

### `constLitTy?` is a guess; `JudgeConsts` is what makes it sound

The restriction to literals is *not* the soundness argument, and it was important to get that
the right way round. `constLitTy?` claims "this expression evaluates to a value of this type",
and the claim is discharged by a new premise on `classStmt`/`moduleStmt`:

```
JudgeConsts κ cs      -- for each (name, init): constLitTy? init = some τ ∧ Judge κ [] .ivar0 init τ [] .ivar0
```

Two consequences worth stating:

- **`constLitTy?` may be widened freely.** A wrong row makes the premise fail, which costs a
  rung and never produces a wrong type. It is a completeness knob, like fuel.
- **The type is `constLitTy?`'s, not a synthesized one.** That is what pins the syntactic
  table and the judgment together by construction: the table cannot record a type no
  derivation licensed, and no derivation can license a type the table will not record.

The initializer is judged in the **empty** local environment, coming back empty, with the
empty ivar spine — a class body is a fresh scope that cannot see the enclosing method's
locals and must not leave any behind. `κ` is the context at the class statement, so the
tables in force are the ones that really are in force when the body runs.

### Why the judgment has to happen at the definition site

The tempting alternative is to skip `constLitTy?` entirely: store the *initializer* in the
class table and judge it on demand at each **read**. Then any expression works, not just
literals. It is unsound, and the counterexample is short:

```ruby
class Helper; def f; 1; end; end
class Box; V = Helper.new.f; end          # V is an Integer
class Helper; def f; "s"; end; end        # reopened; the later `f` wins in `mergeCls`
```

`κ.classes` only ever grows, so a read of `V` after the reopening judges `Helper.new.f` at
`String` — for a constant holding an `Integer`. Judging under a deliberately *emptied* table
does not save it either: `constBuiltin`/`caseEqQuery` are each *more* permissive with an
empty class table (`class Integer; def self.===(o); 1 + "a"; end; end` is the witness), so
"emptier is more conservative" is simply false here. Definition-site judgment has no such
question to answer, which is why it is worth the literal restriction.

### Lexical resolution, from `Frame.defClass`

The binding lands at `"::Box::SIZE"`, and the bare `SIZE` inside `Box#size` finds it because
`constGet?` now tries a **list** of paths, innermost first: `constKeyIn f.defClass n` then
`constKey n`. `Frame.defClass` is already exactly the right thing to ask — it is where the
running method was *found*, which for a `def` written inside `class Box` is `Box`, and for an
inherited method is the ancestor whose body the `def` is in. Both are Ruby's lexical cref for
that `def`, which is what Ruby resolves a bare constant against.

Outside any method there is no frame, so only the top-level path is tried — and that is why
`class Box; SIZE = 3; end; SIZE` is rejected. Ruby raises `NameError` for it (control p13f).

`constGet?` is also read by the *negative* premises added in clink 27
(`classStmt`/`constCls`/`constBuiltin`), and widening it to a path list only makes those
stricter, so nothing on file moved.

### `PrimSig.freezeId`, and a predicate deliberately not twinned

`= {...}.freeze` is how every frozen table in the target is written, and `Object#freeze`
returns the receiver, so the row is receiver-polymorphic in the way `objEq` is
argument-polymorphic: `PrimSig σ "freeze" [] σ`.

Its guard is `NilQSafe`, **reused rather than twinned** as a `FreezeSafe`. The two conditions
are the same condition — "this receiver's method table is the builtin one" — and a second
copy would be a second thing to keep true. Control (p13g) is the program that needs the
guard: `class C; def freeze; 1 + "a"; end; end; C.new.freeze` raises `TypeError`, and it is a
*sound* rejection, so the guard is load-bearing rather than decorative.

### What `const-frozen-hash` says by climbing

It types, and the type is `.any`, which nothing consumes. So the rung climbs and the
capability does not arrive — which is the ladder's sharpest statement of §Frontier item A:
`cvss.rb` reads all seven of its metric tables exactly this way and puts the result into
Float arithmetic, so a `Hash#[]`/`fetch` answering `.any` types the *read* and rejects the
file. The rung is where a parameterised hash type would first become visible.

### One knob turned

`Rungs.lean`'s two whole-corpus `rfl`s needed `maxRecDepth 8000` (from 512). They reduce
`chk` over every rung in a single term, so the depth grows with the corpus; it can only turn
a proof into an error.

### State

**133 rungs of 232**, tier 13 at 4/13. 133/133 cross-checked against the real semantics,
99/99 controls rejected (three new), corpus agreement 232/232, axiom-clean.

Next in tier 13 is the scoped forms (`M::X`, `Outer::Inner::Y`, `M::X = 4`), which need
`cpath` and a **nesting path** rather than a single owner — `constKeyIn` takes one string
today, and `Frame.defClass` is one string too.

## Clink 30 (2026-09-01) — tier 13d: three class-body declarations: 135 → 138

`const-private-constant`, `const-attr-reader`, `const-alias`. Three new `ClsMember` kinds,
and the shape of the clink is that **two of the three vanish before any rule sees them**.

### `attr_reader` is an expansion, and that is the whole story

`splitMembers` turns `.attrR ["x", "y"]` into the two `Defn`s it stands for —
`⟨"x", [], .var .ivar "@x"⟩` — so `mroGet?` finds ordinary methods, `callMethod` judges an
ordinary body, and `r146`'s derivation does not contain the string `attr_reader` anywhere. The
ivar's name is the reader's with an `@`, which is the only fact there is about `attr_reader`,
and it is stated once, in `attrDefns`.

Control (p13l) is what makes the expansion honest rather than a shortcut:
`class C; attr_reader :z; def initialize(v); @v = v; end; end; C.new(1).z + 1` raises
`NoMethodError`, because `@z` was never assigned and `ivarRead` correctly answers `nil`. A
checker that gave a reader the type of the constructor parameter with a matching *name* would
certify it. Sound rejection.

### `alias` cannot be a `clsMember?` case

An alias copies a method, and a member kind on its own cannot see the method it copies. So
`splitMembers` collects aliases into a seventh component and `classMethods?` resolves them
(`resolveAliases`) before handing back the same six-tuple everything downstream reads — which
is why `extendClasses` needed no change at all.

Two decisions there, both recorded because both are visible in Ruby:

- **An unresolvable alias makes the whole class unreadable** (`none`), not skipped. Skipping
  would be "sound" by this package's definition (`alias b a` with no `a` raises `NameError`,
  outside the family) and would put a class in the table missing a method, failing a later
  dispatch for the wrong reason. Control (p13k).
- **Ruby's ordering requirement is not enforced.** `splitMembers` keeps each kind's source
  order but loses the interleaving between kinds, so `class C; alias b a; def a; 1; end; end`
  types here and raises `NameError` in Ruby. Fixing it means keeping the members in one
  ordered list instead of five, which is a change to tier 7's data structure for a rung nobody
  has written.

### `private_constant` is the one that is precision rather than soundness

It declares nothing, so `splitMembers` drops the member and `r145`'s derivation is
`const-in-class`'s. What it *does* is hide the constant from a scoped read: `Box::SECRET`
raises `NameError` while a bare `SECRET` inside `Box#get` still reads it.

`NameError` is outside the type-stuck family, so a checker that treated the member as a pure
no-op would still be **sound** — and would certify `Box::SECRET`, a program Ruby refuses to
run. The choice to implement it anyway is the reason `Ctx.privConsts` exists: control (p13j)
would otherwise be a control that *passes* validation, which is a failure in this harness even
though no soundness theorem would notice. Where the fact lives is fixed by what it is about:
one premise on `Judge.constPath` and nowhere else.

It is a second syntactic pass over the class body (`privNames`) rather than a tuple
component, because `splitMembers` has already dropped the member by the time anything wants
the answer, and `Ctx.afterStmt` is where it is needed.

### The general shape, now visible three times

Tier 10 read `include`/`extend`/`prepend` declaratively off the class body's syntax; tier 13d
does the same for three more statements. The shared caveat: all six are matched at the exact
syntax the desugarer emits, with the arguments required to be bare constants or bare symbols.
`attr_reader(*names)` is not read, so the class does not enter the table and nothing using it
types — conservative, and the same trade `include some_expr` already made.

### State

**138 rungs of 232**, tier 13 at 9/13. 138/138 cross-checked, 104/104 controls rejected (three
new, two of them sound rejections), corpus agreement 232/232, axiom-clean.

The four left in tier 13 are three rungs and one thing: `const-scoped-nested`,
`const-scoped-class-ref` and `const-class-of-const` all need a class or module **declared
inside another one** to enter the class table, which `classMethods?` refuses and
`extendClasses` does not recurse into. That is a change to the *class* namespace — qualified
`Cls.name`s and lexical resolution of bare class names — not to the constant one.
(`const-class-of-const` additionally wants `Object#class`.)

## Clink 31 (2026-09-01) — tier 13e: nested namespaces, and the name that matches the runtime: 138 → 140

`const-scoped-nested`, `const-scoped-class-ref`. The clink's one real decision is what a
nested class is *called*.

### Qualified names, because CRuby has them

`module M; class Box; … end; end` gives a class whose `name` is the string `"M::Box"`. So the
`CTable` key is `"M::Box"`, `Ty.clsOf "M::Box"`, `Ty.inst "M::Box" spine`. That is a choice —
the alternative was an unqualified `"Box"` plus a separate namespace structure — and the reason
to make it is that `CheckRungs.lean` compares a rung's `Ty` against **the class name the
semantics reports**. With qualified names the two agree because they are the same string; with
unqualified ones they would agree by a convention that has to be maintained in
`expectedClasses`.

The rest of tier 7 then needed *nothing*: dispatch was already a table lookup on a string, so
`newInst`/`callMethod`/`mroGet?` work on `"M::Box"` unchanged. **The whole cost of a namespaced
class is naming**, which is the finding.

### Two rules where one lookup would not do

A path step can name a value or a namespace, and those live in different tables:

- `constPath` (tier 13c, generalized here) — the constant table, `"::Outer::Inner::Y"`;
- `constPathCls` (new) — the class table, `"Outer::Inner"`, answering `.clsOf` of the
  qualified name.

They are kept disjoint by `constPathCls`'s `envGet? κ.consts … = none`, exactly as `constCls`
is kept disjoint from `constEnv`, and for the same reason: `M::Box = 5` rebinds the path to the
`5`, and `M::Box.new` then raises `NoMethodError` (control p13m, a sound rejection).

`constPath`'s base was also **generalized from `.const owner` to any expression** and now
threads its outgoing state, which is what makes `Outer::Inner::Y` type at all: the base of the
outer step is itself a `cpath`. Only the *write* side (`cpathAsgn`) still requires a syntactic
base, because `extendConsts` matches on it to know which key the binding lands on.

### `JudgeNested`: where a nested class statement's obligation lives

A nested `class` statement is not a statement of any sequence, and `JudgeSeq` is the only thing
that would judge one — so nothing would have typed it. `JudgeNested` is that obligation, and it
says of a nested declaration exactly what `classStmt` says of a top-level one, recursively:
readable body, mixins are declared modules, the qualified name is not already a constant, its
constants type, its own nested declarations are well-formed.

Its `String` index is the prefix, and it is there for one premise only — without a qualified
name there is nothing to check `M::Box = 5; module M; class Box; end; end` against.

`clsMember?` refuses a nested class **with a superclass**, deliberately: the superclass name
would need resolving against the nesting too, and refusing the member makes the *enclosing*
class unreadable rather than silently dropping the nested one.

### Two termination traps, both about kernel reduction rather than correctness

Both cost a rebuild-and-stare, and both are worth recording because the failure mode is
identical and silent:

1. `nestedClasses`/`addNestedConsts`/`chkNested` recurse into bodies that come *out of*
   `classMethods?`, which Lean cannot see as subterms — so there is no structural measure and
   the recursion has to be **fuel-bounded**. `nestFuel = 512`, and unlike `chk`'s fuel this one
   bounds breadth as well as depth (a unit per declaration visited). Completeness knob: a
   dropped table entry is a rejected use.
2. And the fuel has to be matched **first**, with *every* recursive call spending a unit. Write
   `chkNested (fuel) (κ) (pfx) : Nested → Bool` matching the list first and Lean compiles it by
   **well-founded** recursion — which type-checks, `#eval`s correctly, and then does not
   kernel-reduce, so `Rungs.lean`'s `rfl`s fail with "not definitionally equal" and no hint as
   to why. The same trap caught `chkOwner?`, which calls `chk` at the *same* fuel and thereby
   made the whole `chk` mutual group well-founded — every rung's `rfl` broke at once. Both are
   fixed by matching on fuel and decrementing.

   Diagnosing it: replace the `rfl` theorems with `#eval` of the same predicate. `#eval` uses
   the compiler and `rfl` uses the kernel, so `#eval` answering `[]` while `rfl` fails *is* the
   signature of a well-founded definition.

### One model gap found on the way (`found-issues.md` A3)

Control (p13n) checks that a nested class body is really checked, using
`class NotAModule; end; module M; class Box; include NotAModule; end; end`. CRuby raises
`TypeError`. **The model runs it to a value** — it does not enforce `Module#include`'s argument
check at all — so the control prints as *conservative* rather than *sound*.

Nesting is irrelevant; the flat form diverges too, and it has been printing the same misleading
label in this harness since tier 10 (`class K; …; class P; include K; end; P.new.m`). So
`classStmt`'s `allModules` premise is justified against CRuby, verified directly, and
*unsupported* by the model. No rung is affected (none includes a non-module, which is also why
`run_agreement.sh` never caught it); what is affected is what a control's label means.

### State

**140 rungs of 232**, tier 13 at 11/13. 140/140 cross-checked, 106/106 controls rejected (two
new), corpus agreement 232/232, axiom-clean — now with `chkOwner?_sound` and
`chkNested_sound` in the list.

One rung left in tier 13: `const-class-of-const`, which wants `Object#class` (the inverse of
`newInst`) and `Module#to_s`. Also recorded as owed: `private_constant` inside a *nested*
declaration is not read (`privNames` does not recurse), which is precision, not soundness.

## Clink 32 (2026-09-01) — tier 13f: `Object#class`, `Module#to_s`, and tier 13 is at target: 140 → 141

`const-class-of-const` (`M::Box.new.class.to_s`). Two rules, each the inverse of something
already on file, and **tier 13 is now at every rung it targets** — 12 climbed, the 13th the
tier's permanent negative.

### Two inverses

`Judge.classOf` is `newInst`'s inverse: `.inst n _` in, `.clsOf n` out, forgetting the ivar
spine exactly as the value does. Control (p13p) is what says the forgetting is right —
`C.new.class.v` looks the reader up on the *class* object, misses, and raises `NoMethodError`.

`Judge.clsToS` is `constCls`'s: a class object in, its name out.

### One rule needs no guard, and that is a fact about the grammar

`classOf` has no override guard at all, where every comparable rule has one (`is_a?` carries
`isADispatchOk`, `Module#===` and `to_s` carry `smroGet? … = none`, `nil?`/`freeze` carry
`NilQSafe`). The reason is that `class` is a **keyword**: `def class` cannot be written, so
there is no user method to dispatch to instead. Worth writing down because "this rule has no
guard" otherwise reads as an omission, and here the absence is the argument.

`clsToS` does need one, and gets it for free from where it sits in `chk`: the arm is reached
only after `smroGet?` missed, so the miss *is* the premise.

`Module#to_s` is a `Judge` rule rather than a `PrimSig` row for the reason that has now come up
three times: the guard needs the class table, and `PrimSig` relates types to types and cannot
see it.

### The arity shape

Both rules take `JudgeAll κ Γ₁ I₁ args [] Γ₂ I₂` rather than requiring `args = []` in the
syntax. That is `newInstNoInit`'s shape, and the reason is not style: `chk`'s guard tests
`argTys = []`, the *types*, and nothing in scope there says the expression list is empty. The
`JudgeAll` premise is exactly what the guard establishes. Getting this wrong is a
`Type mismatch` at the derivation, not a soundness hole — but it is the second time in this
tier that the proof was the thing that noticed a rule had been stated one notch too specific.

### State: tier 13 complete

**141 rungs of 232**, tier 13 **12/13 — every rung it targets**. 141/141 cross-checked against
the real semantics, 108/108 controls rejected (two new, both sound rejections), corpus
agreement 232/232 with 0 disagreements, all soundness theorems axiom-clean (`propext`,
`Quot.sound`).

Six clinks for the tier, and the summary of what a constant cost:

| clink | rungs | the idea |
|---|---|---|
| 27 | 1 | `Ctx.consts`, grown at `JudgeSeq.cons`; three disjointness premises on rules already on file |
| 28 | 3 | class-body constants: `constLitTy?` guessed, `JudgeConsts` discharged, at the *definition* site |
| 29 | 2 | `M::X`: the base is judged, because `M = 5; M::X` raises |
| 30 | 3 | `attr_reader` expanded, `alias` resolved, `private_constant` recorded |
| 31 | 2 | qualified names for nested declarations, `JudgeNested`, two kernel-reduction traps |
| 32 | 1 | `Object#class`/`Module#to_s` |

What tier 13 did *not* need, having been predicted to: a whole-program constant table, a
fourth threaded index on `Judge`, any change to `Env`, or any change to tier 7's dispatch.
What it did need that was not predicted: **four new premises on rules already on file**, every
one of them because `casgn` can rebind a name a class declaration owns.

§Frontier item B is discharged. The next-cheapest whole-file target (`semver.rb`) needs D
(`Regexp` plus the `String` rows, tier 15) and E (`begin`/`rescue`, tier 16); item A (a
parameterised `Hash`) is still the widest unblocker, and `const-frozen-hash` is now the rung
that shows why.

## Clink 33 (2026-09-01) — tier 14a: an optional parameter, and a table that stopped being trusted: 141 → 142

`param-optional` (`def greet(name, greeting = "hi")`). One rung, and the reason it is its own
clink is that it turned a *function used in a premise* into something a theorem covers.

### The problem an optional parameter poses

`paramEnv : List Param → List Ty → Option Env` is a **function**, and it appears in the
premises of a dozen call rules (`paramEnv d.params argTys = some Γb`), discharged by `rfl` in
every derivation on file. An omitted optional parameter holds the value of its *default
expression*, so its type comes from an expression that has to be **judged** — and a function
cannot judge.

The three ways out, and why the third one won:

1. **Make `paramEnv` a relation** (`ParamEnv κ ps τs Γ`, with a `Judge` premise for each
   defaulted parameter). Correct and general — it is what `def pad(s, n = s.length)` needs,
   since the default reads an earlier parameter and must be judged in the environment built so
   far. It also re-indexes every call rule and replaces ~50 `rfl`s with hand-built terms.
2. **Add a premise to each call rule** discharging the defaults. Same blast radius, less
   generality.
3. **Restrict defaults to expressions whose type is a theorem** — and prove the theorem.

### `constLitTy?_sound`, and what it says

`constLitTy?` already existed, from tier 13b, reading a type off a literal's syntax. Clink 28
paired it with `Judge.classStmt`'s `JudgeConsts` premise, which discharged it *at the class
statement*. There is no equivalent place for a parameter default, so instead:

```
constLitTy? e = some τ → Judge κ Γ I e τ Γ I
```

Read the quantifiers: `κ`, `Γ` and `I` are arbitrary and **unchanged across the conclusion**.
The expression types at that type in *any* context and leaves no state behind. That is a strong
claim, and it is exactly why the function is restricted to literals — nothing it accepts reads a
variable, dispatches a method the program could redefine, or writes anything.

Two consequences worth stating:

- **`paramEnv` stays a function** and needs no new premise anywhere. The `.opt` rows are
  licensed by a theorem rather than trusted like a `PrimSig` row.
- **`JudgeConsts` is now redundant as an obligation** (it is always satisfiable) while
  remaining useful as a statement of intent. Clink 28 could have been done this way; it is
  better that it was not, because the premise is where the specification says out loud that a
  class body's constants are typed at the definition site.

One row had to be tightened to get the proof: `constLitTy? (.hash pairs)` used to answer
`.cls "Hash"` unconditionally — correct about the *type*, since tier 5's hash type carries
nothing about its pairs — and now requires the pairs to be literals too (`constLitPairs?`).
Without that the theorem is false, because `hashLit`'s premise is `JudgePairs`.

### Greedy matching is safe, and the argument is short

Optional parameters match **greedily, left to right**. Ruby does not: `def f(a, b = 1, c)`
called with two arguments binds `a` and `c` and defaults `b`. Greedy binds `a` and `b`, then
meets a `.req` with no argument left, and answers `none`.

So greedy either agrees with Ruby or fails, and there is no argument count at which it succeeds
with a binding Ruby would not have made. Control (d3) is that program, declined.

### One control retired, three added

The control `def f(x = 1); x; end; f()` was in the file *to measure this gap*
("safe; optional param unsupported"). It is now certified, so it was retired rather than left
failing — the honest bookkeeping for a control whose whole content was an absence. What
replaced it:

- (d) `def pad(s, n = s.length)` — the part of the gap that remains, and the rung this clink
  does not climb.
- (d2) `def g(x = "s"); x + 1; end; g` — **sound rejection**: the default's type really is
  what the body is checked against, and here that makes the program raise `TypeError`. So
  `constLitTy?`'s answer is checked by execution, not only by the theorem.
- (d3) the greedy-matching program above.

### State

**142 rungs of 232**, tier 14 at 2/15. 142/142 cross-checked, 110/110 controls rejected,
corpus agreement 232/232, axiom-clean — four new theorems (`constLitTy?_sound`,
`constLitTys?_sound`, `constLitPairs?_sound`, `constLitTy?_nilQSafe`).

What tier 14 has left is two things, not thirteen: **`ParamEnv` as a relation** (the
non-literal default, and it is the same shape `.rest` and `.key` defaults will want), and
**keyword arguments**, which are a change to the *call* shape — a `kwargs` node is the last
element of the argument list and is not a value, so `JudgeAll` cannot type it and every
dispatch rule has to learn to split positional from keyword arguments. That is the expensive
one, and §Frontier item C is right that it is also the one where getting it wrong is unsound
(a missing required keyword raises `ArgumentError`).

## Clink 34 (2026-09-01) — tier 14b: rest parameters, and an array that is provably empty: 142 → 144

`param-req-then-rest`, `param-rest`. Two `paramEnv` rows, one `PrimSig` row, and one `IterSig`
row — and the `IterSig` row is the interesting one.

### A rest parameter is an array literal that nobody wrote

`paramEnv [.rest (some x)] τs = some [(x, .arrayOf (elemTy τs))]` — the *same* `elemTy` an
array literal uses, because the value is an array built from exactly those arguments. So
`tag(1, 2, 3)` gives `rest : arrayOf Int`, and `f(1, "a")` gives `arrayOf (union Int String)`,
which control (d5) shows is not a nicety: a checker taking the *first* argument's type would
certify `a[1] + 1` and the program raises `TypeError`.

**Only as the last parameter**, and the argument is clink 33's: Ruby fills post-rest required
parameters before the rest (`def f(*a, b)` with three arguments binds `a = [1, 2]`, `b = 3`), so
swallowing everything is right exactly when nothing follows. With something following,
`paramEnv` answers `none`. Control (d4) is that program, declined — and it is worth a control
precisely because the failure mode here is a *wrong binding* rather than a rejection.

`paramEnvB` allows one thing after the rest: a `&b`, which is the only parameter kind Ruby lets
follow a rest that this greedy walk can still be right about.

### `arrayOf .never` is a real statement, and this is where it gets used

`total()` binds `ns` to `arrayOf (elemTy []) = arrayOf .never`. Tier 6's `elemTy` docstring
already argued that `.never` is the *most precise* element type for an empty array; nothing had
ever consumed it. Here it has to be consumed:

- the block is judged with `b : .never`;
- `a + b` is `.never` by strictness (`primNever`);
- and `IterSig.inject`, which requires the block to return the accumulator's type, **fails on a
  call that cannot possibly go wrong**.

`IterSig.injectEmpty` is the new row, and the placement of its side condition is the whole
content of it. It is keyed on the **receiver's element type** being `.never`, not on `ρ` being
`.never`:

> `arrayOf .never` says every element of this array does not return a value; `.never` is
> uninhabited; so the array has no elements, the block never runs, and the result is the seed
> whatever the block would have returned.

Keyed on `ρ` instead it would be a much weaker and shakier claim — a block that never returns
for a *non-empty* array is a different situation, and one where the program may well be
type-stuck. Keyed on the receiver the argument is one line and does not mention the block at
all.

`r152`'s derivation shows the payoff directly: two calls to the same `inject` in one program,
taking **different `IterSig` rows** — `.inject` for `total(1, 2, 3)` and `.injectEmpty` for
`total()`.

The proof of `iterSig?_sound` needed a `cases τ` for the first time, because which `inject` row
applies is now decided by the receiver's element type rather than by anything `iterParams?`
returns.

### State

**144 rungs of 232**, tier 14 at 4/15. 144/144 cross-checked, 112/112 controls rejected (two
new, one sound), corpus agreement 232/232, axiom-clean.

Tier 14's remaining eleven are still two things: the `ParamEnv` relation (`n = s.length`,
`param-all-kinds`) and keyword arguments (six rungs, and the call-shape change).

## Clink 35 (2026-09-01) — tier 14c: keyword arguments, where the arity *is* the soundness: 144 → 147

`param-keyword`, `param-keyword-default`, `param-shorthand-kwarg`. §Frontier item C, and it is
the first thing on this ladder that changed the **call shape** rather than adding a rule to it.

### Why keywords could not be folded into `JudgeAll`

`Expr.kwargs` is the last element of a call's argument list and **is not a value**. It has no
`Ty`, so `JudgeAll κ Γ I args argTys` cannot type it, and every rule whose premise is that
`JudgeAll` is therefore unable to see a keyword call at all. So the argument list has to be
*split*:

```
args = pos ++ [.kwargs entries]      -- Judge.callDefKw's first premise
JudgeAll κ Γ I pos posTys …          -- positional, as before
JudgeKw   κ … entries kws …          -- keyword, into name/type pairs
paramEnvK d.params posTys kws = some Γb
```

`Judge.callDefKw` is `callDef`'s twin rather than a generalization of it, and only `callDef`
got one — the three rungs are all implicit-self calls to top-level `def`s. The explicit-receiver
and singleton twins are owed, and each is the same five premises.

The split is stated as `args = pos ++ [.kwargs entries]` in the rule (the readable form) and
computed by `splitKw?` in `chk`, with `splitKw?_sound` as the bridge. Worth noting the shape:
`splitKw?`'s first pattern (`[.kwargs es]`) *overlaps* its second (`e :: rest`), which is what
makes `[.kwargs es, x]` answer `none` — a `kwargs` node anywhere but last is not read.

### Three binders became one

`paramEnv`, `paramEnvB` and the keyword binder are the same left-to-right walk differing only in
what they can bind *from*, so there is now one `paramBind (blk) (ps) (τs) (kws)` and the older
names are abbreviations at empty inputs. Every `paramEnv … = some Γb` premise on file still
discharges by `rfl`. One behaviour improved on the way: `paramEnv` used to refuse a
`Param.block` outright, and now binds it to `.nilT`, which is what Ruby does when a method with
`&b` is called without a block.

`.rest`'s side condition also got its *real* form. Tier 14b said "the rest parameter must be
last"; the condition is actually **`noPositionalParams`** — no parameter after it may consume a
positional argument. `def f(*a, b)` fails it; `def f(*a, c:, **kw, &blk)` passes. Those were the
same condition before keywords existed.

### Where the soundness is, and it is not where positional arity is

A positional arity mismatch is an `ArgumentError` too, and `paramEnv`'s length matching refused
it *for free* — nobody had to think about it. Keywords are matched **by name**, and two
name-directed failures had to be built, both `ArgumentError`, both inside the family:

- **a missing required keyword** — `paramBind`'s `.key` with no default and no matching entry
  answers `none` (control e1, and the corpus's `param-missing-keyword-unsafe`);
- **an unexpected keyword** — `paramBind`'s `kws.isEmpty` check at the *end* of the walk. This
  is the one that is easy to miss: every parameter is bound, every argument is used, and the
  call still raises (control e2). Without the check the leftover keyword is silently ignored.

Two more controls, both sound rejections: (e3) a Hash where a keyword is wanted is *not* a
keyword in Ruby 3, and (e4) a keyword's value type is what the body is checked against.

**No assumption is added to `κ.asms`.** `callDef` registers `⟨m, argTys, ρ⟩` for
assume-then-verify; an `AsmTable` key is a `List Ty` and cannot distinguish a keyword call from
a positional one at the same types, and an assumption is *believed* rather than re-derived — so
a wrong key would be unsound. A keyword-recursive method therefore does not type. Conservative,
and cheaper than widening the key.

### `param-keyword-default` is where tier 14 and tier 12 meet

One `def`, two calls, and the *same* `if` typed twice with **opposite branches dead**:

- `build(name: "x")` — `version` takes its `nil` default, so it is `.nilT` (a keyword default is
  `constLitTy?`'s answer, exactly as an optional positional default is). `nonNilTy .nilT` is
  `.never`, the else-branch is dead, and `name + "@" + version` types by `primNever` with no
  claim about `String#+` at all.
- `build(name: "x", version: "1")` — `version` is a `String`, the else-branch is live and
  ordinary.

The precision of `.nilT` (rather than a nilable) is what makes the first call's else-branch dead
rather than merely unreachable-looking, and that precision comes from `constLitTy?` reading the
default literally.

### One elaboration lesson, recorded because it cost a detour

`r155`'s derivation needs `(τ₁ := …) (τ₂ := …)` pinned on both `if'`s. The reason is not the
proof: `Judge.if'`'s type index is `joinT τ₁ τ₂`, and until *both* branch types are known the
elaborator cannot see that it is the `String` the surrounding `+` wants — so it postpones the
`rfl`s inside the branches and never returns to them. The error is an
`Application type mismatch` printing metavariables for *variable names*, which is the signature
of exactly this. Pinning the two types fixes it, and the pinned values are worth reading anyway:
`.never` on the right is the dead branch.

### State

**147 rungs of 232**, tier 14 at 7/15. 147/147 cross-checked, 116/116 controls rejected (four
new, all four **sound** rejections), corpus agreement 232/232, axiom-clean — with
`splitKw?_sound` and `chkKw_sound` added.

What tier 14 has left is now three things, and none of them is about keywords-as-such:

- **`ParamEnv` as a relation** — `param-optional-uses-earlier` (`n = s.length`), the only way to
  type a default that reads an earlier parameter.
- **A parameterised `Hash`** — `param-kwrest` binds `**kw` at the bare `.cls "Hash"`, so
  `kw["a"]` is `.any` and `.any.nil?` has no rule. §Frontier item A again, and
  `param-all-kinds` wants `Hash#length` off the same type.
- **A hash's keys** — `arg-kwsplat-call` (`build(**kw)`), which `JudgeKw` has no constructor
  for, because matching `**h` by name needs to know what names are in `h`.

## Clink 36 (2026-09-01) — tier 15a: the `String`/`Regexp` rows, and one free rung: 147 → 157

`str-interpolation-nonstring`, `str-percent-w`, `regexp-match-p`, `regexp-match-nil`,
`regexp-sub`, `regexp-gsub`, `regexp-split`, `regexp-extended-flag`, `str-methods`,
`str-start-with`. Ten rungs, nine `PrimSig` rows and one `Judge` rule — the cheapest clink per
rung on the ladder, and §Frontier item D predicted exactly that ("cheap — most of the rows are
total `String -> String`").

### A `Regexp` is opaque, and that is forced rather than chosen

`Judge.regexpLit` answers `.cls "Regexp"` and **nothing anywhere reads the pattern or the
flags**. `regexp-extended-flag` is the rung that checks ignoring the flags is enough, and it is:
what a flag changes is *which strings match*, an answer this type language never computes.

The reason it is forced is `regexp-interpolated`: `semver.rb` interpolates four constants into
`SEMVER_REGEX`, so a pattern can be built at runtime. Any reasoning about pattern text would
work on literals and fail on precisely the patterns the target writes, so answering
`.cls "Regexp"` for every regexp — literal or computed — keeps the two cases indistinguishable,
which is what the `String` rows need and all they need.

### One row that is not boring

`PrimSig.strMatch` answers `T.nilable(MatchData)`, and that makes `regexp-match-captures`
(target `true`) and `regexp-no-match-unsafe` (permanent negative) **two readings of one
signature**: whether `m[1]` is safe depends on whether the match succeeded, which is a fact
about the pattern and the subject, not about their types. So the row cannot separate them and
does not try. `regexp-match-nil` is the half that *is* typeable — asking a nilable whether it is
nil, which `NilQSafe`'s recursive `nilable` case has covered since tier 2.

What follows for `regexp-match-captures` is worth stating plainly: **it is not climbable by
typing.** Both the pattern and the subject are literals, so a checker *could* decide it by
evaluating the match — but that is execution, not typing, and doing it would make the checker's
answer depend on a regexp engine. This is the same shape as `narrow-nilable-and-union`'s
recorded-target problem (clink 14): a rung whose target says `true` and which no sound rule can
reach. Left as a mismatch rather than retargeted, and recorded here.

### `str-percent-w` climbed with nothing written, twice over

`%w[a b c]` is not a syntactic form by the time this checker sees it (the desugarer emits an
array of string literals), and `Array#length` had arrived in clink 34 with **rest parameters**,
for a completely unrelated reason. A free rung, and the second time a tier has collected one
(§2026-09-01 counted eight at the corpus's expansion).

### `str-interpolation-nonstring` completes a pair

r165 (`"hello #{name}"`, a String) climbed with **no `__as_string` row at all**: `caseEqQuery`
refined the else-branch to `.never` and the join was `String`. Here the interpolated expression
is an `Integer`, so the *then*-branch is the dead one and the row is needed
(`PrimSig.intAsString`). The two derivations are the same term with the branches' roles swapped,
which is the clearest thing on the ladder about what `Ty.never`'s dead-branch reading buys.

### Six controls, and two of them are about the model rather than the checker

(f1) is `regexp-no-match-unsafe` in miniature — a **sound** rejection, and the direct evidence
that `strMatch`'s `nilable` is load-bearing. (f5) `"abc" + /b/` is kept because `.cls "Regexp"`
is the first thing since tier 5 that `.cls` names and that is *not* a String, so "any `.cls`
will do" has become a mistake someone could make. (f6) records `regexp-gsub-block` as declined
for want of a block-carrying row rather than for want of `gsub`.

(f3) and (f4) — `"abc".delete_prefix(1)` and `"abc".sub(1, "-")` — are why
`strDeletePrefix`/`strSub` name their argument types instead of leaving them unconstrained.
CRuby raises `TypeError` for both, verified directly; **the model declines both** rather than
raising. So those two rows are justified against Ruby and uncorroborated by the model:
`found-issues.md` A4, the same shape as A3 and much narrower.

### State

**157 rungs of 232**, tier 15 at 13/19. 157/157 cross-checked, 122/122 controls rejected (six
new, three sound), corpus agreement 232/232, axiom-clean.

Tier 15's remaining six: `regexp-match-captures` (not climbable — above),
`str-interpolation-in-method` (`__as_string` on an instance, i.e. dispatch to a user `to_s`
plus the obligation that it returns a `String`), `regexp-gsub-block` (a higher-order `String`
row of tier 9c's kind), `regexp-interpolated` (needs `::Regexp` as an absolute constant path and
`Regexp.new`), and `regexp-last-match` (`=~` plus `Regexp.last_match`, which is *global state*
and the first thing on this ladder that is).

## Clink 37 (2026-09-01) — tier 16a: the loop, the `next` guard, and `case/when` over values: 157 → 161

`ctl-while`, `ctl-until`, `ctl-next`, `ctl-case-when-string`. Three rules and one `PrimSig`
row; `begin`/`rescue` is deliberately a separate clink.

### `while`: the fixed point, made trivial

A loop body's outgoing environment feeds its own *next* iteration, so a rule that let the body
change the environment would need a fixed point over `Env`. `Judge.while'` instead requires the
condition **and** the body to leave every type where they found it, and then the fixed point is
trivial: every iteration is typed by the same two derivations, by induction on the number of
iterations, and the loop's exit state is its entry state. Its type is `.nilT`, which is what
Ruby's `while` evaluates to, and a non-terminating loop produces no value so that is vacuously
safe.

This is the **third appearance** of clink 11's rule — a callee may not retype state its caller
can still see — with the loop as the callee. And it is not a restriction on assignment:
`n = n + i` and `i = i + 1` both assign and both keep their types, which is all the premises
ask. Control (g1) is the program that needs it: a loop that changes `x` from Integer to String
raises on the *second* iteration, which a checker typing the body once against the entry
environment would never see.

**`until` is not a rule.** The desugarer emits `while (cond).!`, so `ctl-until` is `ctl-while`
plus one `PrimSig.notBool` — tier 2's decision to make `!` an ordinary send rather than syntax
(clink 1) paying off again.

One thing had to be stated carefully: the rule is **four premises, not two** — a derivation and
an equation each (`Γc = Γ`, `Γb = Γ`). Writing the conclusion's `Γ` directly in the premise makes
the elaborator unify the body's *outgoing* environment structurally with the incoming one, which
resolves it in the wrong direction (`?Γ' := []`) and fails on any body that assigns. Same shape
as `callMethod`'s `Iout = Iself`, and the same reason.

### `next` has no rule, and both obvious rules are unsound

- Typed **`.never`** it breaks `map { next }`: the element really is `nil`, and
  `arrayOf .never` claims the array is *provably empty* (`IterSig.injectEmpty` reads it that
  way, and clink 34 relies on that reading). Control (g3).
- Typed **`.nilT`** it breaks the sequence: `JudgeSeq` takes the last statement's type and would
  miss that the statements after the `next` do not run on that path.

Both failures are about the **sequence**, so — exactly as for `.ret` in clink 15 — the rule
belongs to the sequence. `JudgeSeq.nextGuard` is `guard`'s twin with `ρ` fixed at `.nilT`,
carrying the same narrowing: the statements after `next if c` run only when `c` was falsy, so
they are typed in the else-branch's refined environment. `.nxt` remains underivable on its own,
and `next e` (with a value) is owed rather than forbidden.

That is now **two** statement kinds whose rule lives in `JudgeSeq` because the fact is about
statement order, and the pattern is worth naming: a construct that *leaves* a sequence early
cannot be typed by a rule that only sees the construct.

### `case/when` over values is a `PrimSig` row, not `caseEqQuery`

`case t when "pypi"` desugars to `"pypi" === t` — a send whose **receiver is the `when` clause's
literal**. So it is not tier 12's `caseEqQuery` (which wants a class object and consults the
class table for a `def self.===`); it is `PrimSig.caseEqPrim`, guarded by `EqSafe` exactly as
`==` is, because `Object#===` is `==` unless someone overrode it and `EqSafe` is precisely the
receivers whose method table is the builtin one.

The two are **disjoint** because `.clsOf` is not `EqSafe`, so no program has a derivation reading
one `===` two ways. Control (g4) is the guard's justification: a user-written `def ===` is
dispatched to instead, and `.inst` is not `EqSafe`, which is what refuses it. Sound rejection.

`chk`'s `===` branch had to learn to fall through: it had committed to `m = "==="` before
looking at the receiver, so a value receiver reached `none` instead of `primSig?`.

### State

**161 rungs of 232**, tier 16 at 8/15. 161/161 cross-checked, 126/126 controls rejected (four
new, three sound), corpus agreement 232/232, axiom-clean.

Tier 16's remaining seven are two things: **`begin`/`rescue`** (`ctl-rescue`,
`ctl-begin-rescue-else-ensure`, `ctl-raise-custom`, `ctl-rescue-in-block`, and the permanent
negative `ctl-rescue-wrong-class-unsafe`), which is §Frontier item E and the decision core of
`vulnerability.rb`; and two rungs blocked elsewhere — `ctl-break` (a `break` changes the
*enclosing send's* result, not the block's, so it cannot be typed from inside the block without a
`mayBreak` scan whose completeness would be a soundness condition) and `ctl-return-early` (needs
to know a non-empty array's `[0]` is non-nil, which is the length-indexed-array gap).

## Clink 38 (2026-09-01) — tier 16b: `begin`/`rescue`, and the environment problem it poses: 161 → 163

`ctl-rescue`, `ctl-raise-custom`. §Frontier item E, and in this target it is **not error
handling**: `Vulnerability` defines its own `Uncomparable < StandardError` and uses raise/rescue
as the *comparison protocol*, so a checker that cannot follow exceptions cannot type the
decision core at all.

### The environment is the whole difficulty

A handler runs at an **arbitrary point inside the body**: whatever the body had done so far has
happened, and whatever it had not has not. So the handler cannot be typed in the body's incoming
environment, nor in its outgoing one, nor in the join of the two — `v = 1; v = "s"; v = 2` has
the same types at both ends and a *different* one in the middle, and a handler reading `v` there
would be typed at a type the value does not have.

The precise answer is a judgment that collects the body's intermediate environments. The cheap
sound answer is **`noLocalAsgn body`** — tier 12's whitelist, reused unchanged: a body with no
local assignment anywhere has no intermediate state to get wrong. That is what `Judge.begin'`
carries, alongside `while'`'s two equations (`Γb = Γ`, `Ib = I`) for ivars.

The price is recorded rather than hidden: control (h5) is safe Ruby declined for this reason,
and it is also why `ctl-begin-rescue-else-ensure` and `ctl-rescue-in-block` are not climbed —
both assign in the body.

`else` and `ensure` are out of scope in the rule's conclusion (`els = none, ens = none`).
Neither is hard; `ensure` runs on every path, so its type is discarded and its assignments would
have to join everywhere.

### `raise` is `.never`, and that is the same reading twice

`raise` does not return, so **no claim about its value can be falsified** — which is exactly what
`primNever` says about a send with a non-returning argument, arrived at from the other side:
there the *subexpression* does not return, here the expression itself does not.

Its premise is soundness rather than shape: `raise 5` raises `TypeError` ("exception
class/object expected"), inside the family. So the first argument must really name an exception
class, and `excName?` decides that two ways — a builtin name from `ExcCls`'s list, or a declared
class whose `Cls.super?` chain *reaches* one. `ctl-raise-custom` needs the walk
(`Uncomparable < StandardError`), and the walk is fuel-bounded for `nestedClasses`' reason,
answering `false` when it runs out. Controls (h2) and (h3) are `raise 5` and `raise Plain` for a
declared non-exception class, both sound rejections.

**`ExcCls` is deliberately not folded into `BuiltinCls`.** That relation is kept to the classes
`builtinAncestors` can answer `is_a?` for, and an exception name admitted there would produce a
`.clsOf` nobody can answer `is_a?` for. So there is a third `const` rule (`Judge.constExc`) with
`constBuiltin`'s two disjointness premises.

### The control that is the point of the tier

(h1) is the corpus's `ctl-rescue-wrong-class-unsafe` in the controls file too:
`begin; 1 + "a"; rescue ArgumentError; 0; end` raises, because the handler catches the wrong
class. A checker that read *any* `begin` as discharging the type-error family would certify it.
`Judge.begin'` does not look at the rescued classes when typing the body at all — the body's
`1 + "a"` simply has no derivation — and that is the whole answer.

(h4) is the other side, and its shape is worth stating: a handler is typed **whether or not it
can be reached**. The program is safe (the body cannot raise) and is declined anyway, because a
handler that would raise if reached is refused rather than excused by a reachability argument
this judgment does not make.

### `PrimSig.excMessage`: the first row guarded by a *name*

`rescue … => e` binds `e` at `.cls "ArgumentError"`, and `Exception#message` is total on one.
Every other guarded row keys on a type *shape* (`EqSafe`, `NilQSafe`); this one keys on the
receiver's name being in `ExcCls`, because `.cls n` is one constructor for `String`, `Hash`,
`Regexp`, `MatchData` and every exception class. Without the guard the row fires for
`.cls "String"`, where `message` is a `NoMethodError` (control h6, sound).

`rescueBind?` only offers a binding for a **single builtin** exception class. A user exception
would want `.inst n .ivar0` and a multi-class rescue their union; neither is hard and no rung
asks, so `ctl-raise-custom`'s handler has no `=> e`.

### One mechanical finding worth recording: `primSig?` outgrew its splitter

`split at h` in `primSig?_sound` began failing with `timeout at whnf, maximum number of
heartbeats (200000)` — and **`set_option maxHeartbeats` did not help**, at file level or on the
declaration. The budget being exceeded is not the proof's; it is the one Lean uses when building
the *matcher splitter* for a 33-row match over `(Ty, String, List Ty)`, generated in a nested
context that does not inherit the option. (Verified the option was applied at all by setting it
to `1` and watching every other error change.)

The fix is structural and small: `primSigStr?` splits the fourteen `.cls "String"` rows into
their own match, and `primSig?` delegates after its five guarded rows (which apply to a `String`
receiver too, so they must come first). Two smaller matches, one extra lemma
(`primSigStr?_sound`), no heartbeat option at all. **The lesson generalizes: when a `split`-based
proof over a table stops working, split the table, not the budget.**

### State

**163 rungs of 232**, tier 16 at 10/15. 163/163 cross-checked, 132/132 controls rejected (six
new, four sound), corpus agreement 232/232, axiom-clean — with `excCls?_sound`,
`chkRescues_sound` and `primSigStr?_sound` added.

## Clink 39 (2026-09-01) — tier 17a: the collection rows, and `arrayOf`'s invariance comes due: 163 → 172

`lib-spaceship-int`, `lib-hash-key-p`, `lib-array-queries`, `lib-array-uniq-compact`,
`lib-array-flat-map`, `lib-array-filter-map`, `lib-array-find`, `lib-array-join`,
`lib-array-each-with-index`. Nine rungs, ten `PrimSig` rows and six `IterSig` rows — and three
findings that are not "one more row".

### The guard moves from the receiver to the element

`include?` calls `==` on the elements; `uniq` hashes them; `Hash#key?` hashes its *argument*. So
for the first time a row's guard is about something other than its receiver, and the predicate is
`NilQSafe` for the third time — asking the same question it always has ("is this value's method
table the builtin one?") one level down. Control (i3) is the justification: a user-written `==`
is dispatched to, and `.inst` is not `NilQSafe`, which is what refuses it.

### Two result types computed by narrowing functions

`compact`'s result is `arrayOf (nonNilTy τ)` and `filter_map`'s is `arrayOf (truthyTy ρ)` —
tier 12's refinement functions used on a **result** rather than in a branch, which is the first
time either has appeared outside `narrowEnvs`. `truthyTy` rather than `nonNilTy` for
`filter_map`, because Ruby drops `false` as well as `nil`.

That is a small piece of evidence for tier 12's design: the refinements were written as total
functions on `Ty` rather than as part of the `if` rule, and it is exactly that which lets them be
reused here.

### `Array#<<` discharges the obligation tier 5 wrote down

Tier 5 ended with "`arrayOf`'s invariance is not yet load-bearing — there is no rule for
`Array#<<` — and the tier that adds one inherits the obligation". Here it is, and the row is
**invariant**: the argument's type must be *exactly* the element type.

That looks needlessly strict, and it is what keeps clink 34's `IterSig.injectEmpty` honest.
`arrayOf .never` is read as "provably empty" (nothing inhabits `.never`), and that reading has to
survive the existence of a row that adds elements. It does, and it survives **by** the
invariance: pushing onto an `arrayOf .never` would need an argument of type `.never`, and no
expression has one. So the two rows are consistent, and neither is safe without the other's
shape.

The price is `lib-array-push` (`xs = []; xs << 1; xs.length`), which does not climb: the empty
literal is `arrayOf .never`, nothing can be pushed onto it, and a send does not retype its
receiver's *binding*. Widening it means a rule that writes to `Env` off a receiver expression,
which nothing in this judgment does. Control (i2) records it, and the control's note is the
important half — it must be declined rather than smoothed over, because smoothing it would break
`injectEmpty`.

### `flat_map` is the first iterator dispatched on the block's return type

`iterResult? "flat_map" _ [] ρ` matches on `ρ` being `.arrayOf σ`. Every other row decides
applicability from the receiver's element type or the call's arguments; this one needs the block
to have returned an array. Ruby also accepts a non-array return (included as-is), which has no
row because the result's element type would be a union nothing consumes — control (i6).

### State

**172 rungs of 232**, tier 17 at 9/23. 172/172 cross-checked, 138/138 controls rejected (six new,
two sound, one "model declined"), corpus agreement 232/232, axiom-clean.

**Session total: 129 → 172 rungs**, and mismatches 81 → 39. Tier 13 complete; tiers 14–17 open.

What is left divides into four things, and only one of them is more rows:

1. **A parameterised `Hash`** (§Frontier item A, still the widest unblocker): `lib-hash-fetch`
   (62 sites in the slice), `lib-hash-dig`, `param-kwrest`, `param-all-kinds`, and
   `const-frozen-hash`'s *usefulness*. `Ty` needs a keyed hash, and it has to be a **spine**
   rather than a list payload, for the reason `ivar0`/`ivarCons` are (`Expr`'s derived `BEq` and
   `Ty`'s kernel reduction).
2. **A pair type** (§Frontier item F): `lib-array-zip`, `lib-array-to-h`, `lib-array-partition`,
   `lib-multiple-assign`.
3. **The length-indexed array** (§Frontier item G, flagged since tier 12): `lib-array-first-last`,
   `lib-array-sort-by-max-by`, `ctl-return-early`, `regexp-match-captures`, and every
   `a, b = s.split("-")` in the slice.
4. **`ParamEnv` as a relation**, `Struct`, `Comparable`, `=~`/`Regexp.last_match` (global state),
   `gsub` with a block, `break`, `else`/`ensure`, and the eight whole-file rungs of tier 18.

## Clink 40 (2026-09-01) — a flagged `Ty` gap that was not one: 172 → 173, and 3 gaps → 2

`metaprog-method-missing-splat`, **retargeted from `false` to `true`** and climbed with nothing
added. No new rule, no new row; the finding is the retargeting.

### What the flag said, and why it was wrong

The rung had been a recorded `ty_language_gap` since tier 10, and the recorded reason was:

> Its true signature is "one Sym, then zero or more of anything" — and `Ty`'s arrow spine
> (`arrow0`/`arrowCons`) has no vararg/rest-arity constructor at all. There is no `Ty` value that
> honestly describes this parameter list.

Every sentence of that is true, and it is about **signatures** — which this judgment does not
write. Tier 6's finding was exactly that: `callDef` types a method's body once per *call-site
argument shape*, in an environment made of just its parameters at just those types, so there is
no signature to describe and no arity to spine. `paramBind` binds `*args` to
`arrayOf (elemTy <the remaining argument types>)`, which is the *second* of the two fixes the
original description itself proposed ("or modeling a rest param as `arrayOf Ty`").

So the rung was climbable the moment tier 14b's rest-parameter rows landed (clink 34, written for
`param-rest`), and it took two clinks for anyone to notice — the tier summary went to 6/6 with a
`MISMATCH` in the *other* direction, which is what surfaced it.

### The lesson, and the one gap it does not close

**A gap phrased in terms of signatures should be re-read before it is believed** in a checker
that has none. The `arrow0`/`arrowCons` constructors are still unused after tier 9 predicted they
might never be needed, and this is the second piece of evidence for that prediction.

`proc-arity-leniency` (`proc { |x, y| x }.call(1)`) is *not* fixed by the same work, and its own
flag deserves the same re-reading: it is not a `Ty` gap either. What it needs is for `Ty.clos` to
record whether a callable is a **proc or a lambda**, because only a proc's arity is lenient
(`y` gets `nil`); a lambda raises `ArgumentError`. That is a field on an existing constructor, not
a new one, so the corpus entry is left targeting `false` but its reason is now recorded as
misfiled too.

**Flagged `Ty` language gaps: 3 → 2**, and the one that is unambiguously real is
`narrow-nilable-and-union`'s length-indexed array — which §Frontier item G shows the slice asking
for from four directions.

### State

**173 rungs of 232**, 38 mismatches. Tiers 1–3, 5, 7, 8, 10 and 13 at every recorded target;
173/173 cross-checked, 138/138 controls, corpus agreement 232/232, axiom-clean.

## Clink 41 (2026-09-01) — tier 17b: `Ty.hashOf`, the widest gap on the list: 173 → 177

`lib-hash-fetch`, `lib-hash-dig`, `param-kwrest`, `param-all-kinds`, plus **four rungs retyped**
(`hash-lit`, `hash-index`, `class-instance-in-hash`, `const-frozen-hash`). §Frontier item A, and
the first `Ty` grammar change this ladder has made since tier 9's `clos`.

### Uniform, not keyed, and `cvss.rb` is why

`Ty.hashOf (key val : Ty)` — `arrayOf` with two parameters. A per-key map would be more precise
for a *literal*, and it is not what the target needs: `cvss.rb` reads its seven frozen metric
tables as `TABLE.fetch(metric)` with `metric` a **variable**, so no statically-known key is
available and the useful fact is "every value in this table is a Float". A keyed type would
answer nothing there while costing a third use of the binding spine.

Invariant, for `arrayOf`'s reason, and now with `arrayOf`'s *precedent*: clink 39's `Array#<<`
showed that invariance is what keeps `arrayOf .never`'s "provably empty" reading honest, and
`hashOf .never .never` (the type of `{}`) inherits both the reading and the argument.

### `fetch` is total; `[]` is not; and the difference is `KeyError`

This is the row that makes 62 call sites typeable, and its justification is one sentence:

> `h.fetch(k)` answers the **value type, not a nilable one**, because a missing key raises
> `KeyError` — which is *outside* the type-stuck family — so if the key is absent, execution ends
> there and no claim about the result can be falsified.

That is the same argument `NameError` gets in tier 13, reused a second time, and it is worth
noticing that the argument is what makes the row *useful* rather than merely sound: `Hash#[]`
answers `nilable val` and nothing consumes a nilable, so a checker with only `[]` types the read
and rejects everything downstream. `{"a"=>1}.fetch("zz")` really does raise, and this checker
certifies it — correctly, and deliberately, which is why that program is a *note* in the controls
file rather than a control (a control must be rejected).

The key **argument** is not required to match the key **parameter**, because a missing key is
`nil` in Ruby rather than an error — and requiring a match would reject safe programs:
`param-kwrest` reads a symbol-keyed hash with a `String` key on purpose. What the argument does
carry is `NilQSafe`, on every row, because every one of them hashes it.

### The premise shape did not change, and that is the nicest part

`JudgePairs` now reports two joined types, folded exactly as `elemTy` folds an array literal's
elements — and its *constructor arity is unchanged*, so **every hash derivation on file is
character-for-character the one that was there**. Only the four rungs' recorded `ty` fields moved.

`hash-lit`'s old note is worth quoting, because it was the first statement of this gap on the
ladder (clink 4): "the keys' and values' types are derived and then discarded — `JudgePairs`
carries no type in its conclusion, because `Ty` has nowhere to put one… the first place *these
subterms must be well-typed* and *and here is the type* came apart". They are back together.

### `param-all-kinds` is the checklist rung

`def f(a, b = 2, *rest, c:, d: 4, **kw, &blk)` types now, and reading its derivation is reading
four clinks at once: `paramBind` is one walk with three entry points (35), the two defaults come
from `constLitTy?` licensed by `constLitTy?_sound` (33), the rest parameter's
`noPositionalParams` side condition holds because only keyword/kwrest/block parameters follow it
(35 correcting 34's "must be last"), and `**kw` gets a `hashOf` (this clink). `blk.nil?` was
always free.

### And a third table split, for the same mechanical reason

`primSig?` outgrew its splitter *again* (this time the failure was `timeout at «LCNF compiler»`
rather than `at whnf` — same cause, different phase, and again `set_option maxHeartbeats` does
not reach it). Same fix: `primSigArr?` and `primSigHash?` join `primSigStr?`, and `primSig?` is
now five guarded rows, three delegations and the scalar rows. That is three splits for one
lesson, so it is worth stating as a rule: **a `PrimSig` table should be split by receiver
shape from the start**, one function per receiver family, delegated from a small `primSig?`.

Two rows had to be *added* to keep what `.cls "Hash"` used to have: `EqSafe (.hashOf k v)` and
`NilQSafe (.hashOf k v)`. Without them `h == other` and `h.freeze` would have silently stopped
typing — and `const-frozen-hash` is exactly the rung that caught it, since its whole program is
`{...}.freeze`.

### State

**177 rungs of 232**, 34 mismatches. tier 14 9/15, tier 17 11/23. 177/177 cross-checked,
140/140 controls rejected (two new, one sound; one control retitled and one retired), corpus
agreement 232/232, axiom-clean.

**Session total: 129 → 177 rungs**, mismatches 81 → 34, flagged `Ty` gaps 3 → 2.
§Frontier's items B, C, D, E and A are all discharged; F (a pair type) and G (the
length-indexed array) remain, and they are what the last two `lib-*` clusters and every
`a, b = s.split("-")` in the slice are waiting for.

---

## Clink 42 (2026-09-01) — a detour: the semantic denotation (`Denote/`). **177 rungs, unchanged**

No rung moved and none was meant to. This clink builds the thing every clink so far has
gestured at in prose: **what a `Ty` means**, as a predicate over the real machine. The
full design record is [`Denote/notes.md`](Denote/notes.md); this entry is the *why now*
and the two decisions that were genuinely open.

**Why now, and why not sooner.** Everything proved in this package to date is syntactic:
`validate_sound_syntactic` says `chk` agrees with `Judge`, and `Judge` is the
specification. That is the right order — a checker with no ladder was the original
complaint — but it means the ladder's headline number rests on 41 clinks of docstring
argument about what each `PrimSig` row claims. The one extensional check on file,
`CheckRungs.lean`'s `expectedClasses`, is a `Ty → List String`: it compares the *class name*
of a run's result, and its own docstrings admit three times over that it cannot look inside
an array, inside an object, or at a Proc at all. Those three admissions are precisely the
constructors the last ten clinks added (`arrayOf`, `hashOf`, `inst`, `clos`), so the
cross-check has been getting weaker exactly where the type language has been getting
stronger. A recursive denotation is what stops that drift, and it is cheap to build *now*
because `Semantics/` already imports the real `stepFn`.

**Decision 1: machine-indexed, not heap-indexed — forced by the model, not chosen.** The
brief was `Ty → Heap → Value → Bool`, and it cannot hold for a Proc:
`RubyCore.Closure.captured`/`.home` are `FrameId`s, so **a closure's captured environment is
not in the heap**. Handed a bare heap, `callClosure` would run a lambda's body against
`frames.getD cl.captured default` — a default frame, wrong `self`, no captured locals — and
the call modelled would not be the call the program makes. The rejected alternative worth
recording is the one that *keeps* the signature: quantify over all machines with that heap.
It looks conservative (a stronger obligation) and it is broken — a machine with the right
heap and arbitrary frames sends `captured` at garbage, so the obligation is false for procs
that are fine. What was built instead: master `denM : Ty → Machine → Value → Prop`, heap-only
view `den`, and **`denM_heap_only`** proving the machine argument is irrelevant for every
arrow-free/`clos`-free type. The brief's signature is met exactly on the fragment where it
means something, and a theorem — not a comment — draws the line (`FirstOrder`, a hypothesis
of four results rather than a caveat in prose). Bonus that fell out: because the frames are
in hand, `Ty.clos`'s captured spine gets *real* semantic content, and `closB` decides it. So
the arrow is the only genuinely undecidable arm, not one of three.

**Decision 2: the arrow gathers, it does not curry.** `Ty`'s arrow is a params spine
(`arrowCons A (arrowCons B (arrow0 R))`), and reading a spine as curried is the obvious
move — `A → (B → R)`. It would be wrong about Ruby: `f.call(a, b)` is one call with two
arguments, and the curried reading is a claim about an `f.call(a)` that raises
`ArgumentError`. So `denApp` accumulates arguments down the spine and states the obligation
once at the `arrow0`, and `denM_arrowOf` proves the spine version equals the flat
argument-list version (`ArrowFlat`) — the form to cite. Four things are load-bearing in the
arrow and each is argued in `Denote/notes.md`: partial correctness (a proc that raises or
diverges owes nothing — required for consistency with `Ty.never`'s reading), codomain checked
at the *post* machine (a call can reopen a class, and the nominal arms are `isA` at the heap
they are given), domain at the pre machine, and variance as a consequence of quantifier
position rather than a rule.

**What is proved, and what is only stated.** Proved and axiom-clean: `denM_heap_only`,
`den_iff_denM`, `denB_sound` (at *every* type — by its own induction, because
`FirstOrder τ = false` does not localise: `nilable (arrow0 int)` is higher-order without
being an arrow), `denB_iff` (an `↔` on the first-order fragment), `closB_sound`,
`denM_arrowOf`, `ArrowStable.mono`, and `arrowCheck_of_arrowFlat` with its usable
contrapositive `not_arrowFlat_of_arrowCheck_false`. Stated but not proved, deliberately:
`ArrowStable` (the arrow at every reachable machine — what a call-it-later arrow *should*
mean; only `ArrowStable.here` is provable, and the gap is Ruby's open classes) and
`ClosArrow` (the shape of the `Judge.closCall` soundness bridge). Not attempted: `Judge`
soundness itself, which needs an evaluation relation for `Ratchet.Expr` while the only
executable one is over `RubyCore.Expr`; `subTy` soundness; narrowing soundness. All three are
now *statable*, which is the whole return on this detour.

**The gate.** `Denote/Examples.lean` is 31 `#guard`s that run real programs under the real
`stepFn` from the real prelude-booted heap and ask the denotation about the value produced —
so `lake build Denote` fails if the two ever disagree. They deliberately exercise the three
things `expectedClasses` cannot: element types (`[1,2,3] : arrayOf int` yes,
`arrayOf float` no, `[] : arrayOf never` yes, `[1,2,3] : arrayOf never` no), ivar spines
(`Box.new(1)` against `{@x: int}`, plus the lazy-nil `@y : nilT`), and Procs — a lambda's
captured `x = 7` read out of `Machine.frames`, and both halves of the arrow:
`(Integer) → Integer` survives every sample, `(Integer) → String` is refuted by the first.

### State

**177 rungs of 232**, unchanged — this clink adds no rung and no `PrimSig` row, and
`Ratchet/` is untouched. New: `Denote/` (6 Lean files, a new `lean_lib` on the default
target), 31 semantic `#guard`s, 12 theorems, axiom-clean.

---

## Clink 43 (2026-09-01) — the semantic ratchet's scaffolding. **177 rungs / 0 of 83 rules**

A second ladder, and the reason for it is a sentence from clink 42's own notes: every
soundness result in this package is *syntactic* — `validate_sound_syntactic` says `chk`
agrees with `Judge`, and `Judge` is taken as the specification. Clink 42 gave a `Ty` a
meaning; this clink builds the ladder that uses it to justify `Judge`'s **rules**, one at a
time. **Nothing is discharged.** What exists is the framework, the 83 obligations, the
count, and the endpoint. The per-rung procedure is [`Denote/Sem/notes.md`](Denote/Sem/notes.md).

**Two ladders, measuring different things.** `run_ratchet.sh` says 177 of 232: *reach*, how
many corpus programs `validate` types. `run_denote.sh` now says 0 of 83: *justification*, how
many `Judge` rules have been proved sound against the semantics. The two are independent —
every rung of the first can be climbed with none of the second — and conflating them would
hide exactly the gap worth watching.

**Decision 1: the obligations are derived from the inductive, not written down.** This is the
clink's real content. `SemJudge` and its seven companions were given **exactly** their
syntactic twins' signatures, which makes a rule's proof obligation its own constructor type
with one constant substituted:

```
Judge.intLit      :  ∀ {κ Γ I n},  Judge κ Γ I (.int n) .int Γ I
Obl.Judge.intLit  :=  ∀ {κ Γ I n},  SemJudge κ Γ I (.int n) .int Γ I
```

`derive_semantic_obligations` does that for all 83 constructors of the eight-member family.
The alternative — transcribing 83 obligations by hand, premises like
`PrimSig (.arrayOf τ) "include?" [σ] .bool` and all — was rejected for three reasons, each of
which is a property the derivation *has*:

1. **The denominator is live.** It is read out of `Judge`'s constructor list on every build.
   Add a rule to the checker and 83 becomes 84, reported as undischarged, the same day. Note
   this is the *opposite* of the corpus norm ("a ratchet whose number depends on a live sample
   is not a ratchet") and for the opposite reason: the corpus is a sample, the rule set is the
   specification, and a committed copy of a specification is how drift starts.
2. **An obligation cannot be weakened**, because there is nothing to edit. A rung that will
   not close leaves exactly three moves: prove it, fix a `StateOk`/`SemJudge` definition, or
   fix the rule in `Ratchet/Judge.lean`.
3. **The premises stay.** Nothing substitutes `PrimSig`/`EqSafe`/`NarrowCond` — they are the
   rule's hypotheses. So `Obl.Judge.prim` quantifies over the whole `PrimSig` relation, and
   discharging it means justifying ~90 rows of builtin behaviour from the semantics. That is
   what `Judge.prim` claims; seeing the cost stated is a feature of deriving the obligation
   rather than writing a friendlier one. The ladder's report says "a rung is one rule, not one
   unit of work" for this reason.

And the gate that makes the number mean something: the ladder counts a rule only when a
declaration `Sem.<Family>.<rule>` exists **and `isDefEq` says its type is the derived
obligation**. Checked against a decoy — a `Sem.Judge.intLit : True` is not counted; a
`Sem.Judge.fltLit : Obl.Judge.fltLit` is.

**Decision 2: the copied `Expr` stays; it gets a function across instead.** Clink 42 parked
`Judge` soundness because "it needs an evaluation relation for `Ratchet.Expr` and the only
executable one is over `RubyCore.Expr`". The obvious fix is to delete one copy, and it is the
wrong trade: `Ratchet/` importing nothing from `../lean/RubyCore/` is what makes a divergence
a **deliberate fork to notice** instead of a build error to paper over, and that isolation is
why this restart exists at all. So `Denote/Sem/Trans.lean` is `toRuby`, 48 arms, **no default
case** — a constructor added on either side breaks the build. Side effect worth naming: it
closes clink 42's stated `Ty.clos` `idx` gap, because a live Proc's `RubyCore.Closure.body`
and a table entry's `Ratchet.Expr` body are now comparable (`closTblOk`).

**Decision 3: adequacy is stated, not laddered.** `AdequacyTarget` — the eight
`Judge … → SemJudge …` statements — is one **mutual induction**, so 80 of 83 cases proves
nothing: there is no partial credit in a `Judge.rec` application. Each individual rung, by
contrast, is independent and stays climbed. Writing the induction first would mean writing 83
`sorry`s and this package has none, so the file states the target and generates `AdequacyHyps`
(the conjunction of all 83, folded over the same constructor list), which becomes provable
exactly when the ladder reads 83/83. The terminal clink is then one anonymous-constructor term
plus the induction.

**What `StateOk` had to decide, and the three places a rung is expected to stall.** A rule's
obligation is only as strong as what a machine "conforming to `(κ, Γ, I)`" is required to
satisfy, so `StateOk` is eleven components — one per `Ctx` field plus the two threaded pieces —
and the two that are `True` (`ClosuresOk`, `PrivConstsOk`) say so with docstrings rather than
by omission, because a component quietly skipped is where an unsound rule would hide. Two
earned their reasoning: `EnvOk` gives `Ty.sameAs` its first meaning outside the checker's own
bookkeeping (the two locals hold the *same object*, by the model's `equal?` — which is what
`Judge.narrowEnvs`' soundness will have to consume), and `AsmsOk` is a claim about *running*
calls, which puts the conditionality `Judge`'s own docstring describes ("read a derivation with
a non-empty `κ.asms` as a conditional claim") into every obligation's statement rather than
into a comment. The three predicted stall points are recorded **in advance** in
`Denote/Sem/notes.md` — `StateOk`'s components, `SemJudgeNested`'s one-level reading, and the
`m'.stack = m.stack` frame-balance conjunct on the frame-pushing rules — because a rung that
will not close is information about a definition, and it is worth knowing which one to suspect
before the first attempt.

**Also parked, deliberately: stuck-freedom.** `SemJudge` is partial correctness about the
*value*. Whether a well-typed program can reach a `NoMethodError`/`ArgumentError`/`TypeError`
is `../type-safety-by-reachability.md`'s property, is stated here (`StuckFree`,
`StuckFreeTarget`), and is **not counted**: a rung owing both a value-typing proof and a
stuck-freedom proof would be two rungs wearing one number, and the two have genuinely
different shapes (one is about the value at a `.value` outcome, the other about every outcome).

### State

**177 rungs of 232** (untouched; `Ratchet/` is not modified) and **0 of 83 `Judge` rules
discharged**. New: `Denote/Sem/` (4 Lean files), `Denote/Ladder.lean`, `Denote/Adequacy.lean`,
two exes (`semladder`, `denotereport`), `scripts/run_denote.sh` reworked into the ratchet's
runner. Axiom-clean; no `sorry` and no new axioms anywhere.

---

## Clink 44 (2026-09-01) — the first nine rungs of the semantic ratchet. **177 rungs / 9 of 83 rules**

Clink 43 built the second ladder and discharged nothing. This clink climbs it for the first
time: **9 of 83 `Judge` rules** are now proved sound against the real `stepFn` — the six pure
literals (`intLit`, `fltLit`, `symLit`, `truLit`, `flsLit`, `nilLit`), both local reads
(`var`, `varAlias`) and `seq`. Axiom-clean, no `sorry`, `Ratchet/` untouched.

**The shape held.** `Denote/Sem/notes.md` predicted a leaf rung would be "invert the run":
`match fuel with | 0 | 1 | k+2`, the first two contradicting `.outOfFuel` and the third
delivering the value to the empty continuation. That is exactly `evals_pure`, and once it
existed each of the six literals is three lines. What the note did *not* predict is that the
inversion does not return the machine it started from — `evalFrom` rewrites `ctl` and `kont`,
and the value step rewrites `ctl` again — so nothing could be discharged until conformance was
proved blind to the control word. That is the clink's real content.

**Decision 1: prove `ctl`/`kont` invisible to the denotation, rather than restating `StateOk`
over a projection.** The alternative considered and rejected was to re-express `StateOk` as a
predicate on the tuple it actually reads (heap, frames, stack, tables) so that the control word
could not appear in it by construction. Rejected because it changes what every one of the 83
obligations *says* in order to make nine of them easier, and because it is false to the model:
two `StateOk` components genuinely quantify over **runs** — `denM`'s arrow arms through
`Returns`, and `AsmsOk` through `SendReturns` — and a run does depend on the whole machine. The
reason those two survive is sharper than "conformance is heap-only", and worth having on file
as a proof rather than as a restriction: `applyIn` and `sendIn` *overwrite* `ctl` and `kont` on
the way in, so the run a call denotes is literally the same run from both machines
(`applyIn_reCtl`, by `rfl`). `denM_ctl` is the induction that carries this through
`denM`/`denApp`/`denSpine` simultaneously; `StateOk_reCtl` is the eleven-component corollary.

**Decision 2: `Judge.seq` is discharged as the identity, and that is the finding, not a
shortcut.** `SemJudgeSeq κ Γ I es τ Γ' I'` and `SemJudge κ Γ I (.seq es) τ Γ' I'` are the same
proposition — `JudgeSeq` exists so the *context* can grow between statements
(`Ctx.afterStmt`), which is a fact about `JudgeSeq`'s own rules and not about what a sequence
means. So `Sem.Judge.seq := fun h => h`. The alternative — unfolding `SemJudgeSeq` and
re-proving it — would produce a longer proof of the same thing and hide the fact that the two
definitions were deliberately made to coincide. Note this rung is genuinely cheap while
`JudgeSeq`'s own four rules (still 0 of 4) are where the sequencing content lives.

**Decision 3: two local-read rungs, not one.** `Judge.var`'s `isAliasTy τ = false` premise
exists for a mechanical reason (`Judge.varAlias`'s docstring: a conclusion `stripAlias τ`
cannot be unified with a concrete type), and the semantic side inherits the split for free:
`EnvOk` states `denM (stripAlias τ) m (m.getLocal x)`, so `var` needs `stripAlias τ = τ` from
its premise and `varAlias` needs `stripAlias (.sameAs y τ) = τ` by computation. Both are the
first rungs to **consume** a `StateOk` component instead of only re-establishing one. Neither
touches `EnvOk`'s identity conjunct — that is `Ty.sameAs`'s real content and it is
`Judge.narrowEnvs`' to consume.

**Definitions changed: none.** No `StateOk` component and no `SemJudge*` definition needed
fixing for these nine, which is a mild vote of confidence in clink 43's guesses. The one edit
outside `Denote/Rules/` is a single `import Denote.Rules` in `Denote/Ladder.lean`: the ladder
counts what is in its own environment, so a rung in an unimported file does not exist.
`Denote/Rules.lean` is the indirection, so adding a rung never touches the counting mechanism.

**`Judge.strLit` stalled, and it is the fourth stall point** — written up at length in
`Denote/Sem/notes.md` §The fourth stall point. In one paragraph: a string literal *allocates*,
so it is the first rule whose post-machine differs from its pre-machine in the **heap**, and
two things are missing. `StateOk` does not say the heap's core classes exist, so
`denM (.cls "String") m' v` — which resolves the name "String" through the heap's constant
table — is not derivable from conformance at all; that is a real missing component and every
rule concluding a builtin class type will want it. And `denM` does not survive a heap
extension: transporting an arbitrary `τ` across the push hits the arrow arm, which quantifies
over *runs*, and a run from the extended heap allocates at shifted object ids, so it is not the
run from the unextended one. `AsmsOk` has the same shape. The tempting fix — quantify the arrow
over reachable machines, as `Denote/Arrow.lean`'s `ArrowStable` already does — **conflicts with
`denM_ctl`**, because the machines reachable from `m` are not those reachable from `m` with its
control word rewritten; any reachability-indexed arrow has to be seeded by something coarser.
That is a `Denote/Den.lean` change with `DenB`, `Arrow.lean` and the 31 `Examples.lean` guards
downstream of it, so it is its own clink rather than a detour inside this one. The rung is left
undischarged and visible on the ladder, which is the behaviour clink 43 designed for: a rung
that will not close is information about a definition, not a thing to work around.

### State

**177 rungs of 232**, unchanged (`Ratchet/` untouched; `run_ratchet.sh` and
`run_check_rungs.sh` still read 177/232, 177/177 and 140/140), and **9 of 83 `Judge` rules
discharged**. New: `Denote/Rules/Core.lean` (the two shared lemmas plus their supporting
`rfl`/induction helpers), `Denote/Rules/Lit.lean` (the nine rungs), `Denote/Rules.lean` (the
import list). `Denote/Examples.lean`'s 31 `#guard`s green. Axiom-clean throughout — every new
file ends in its own `#print axioms`, and each reports only `propext`/`Classical.choice`/
`Quot.sound`.

---

## Clink 45 (2026-09-01) — the allocation stall broken, and a soundness bug in `Judge.vasgn`. **177 rungs / 16 of 83 rules**

Seven rungs — `Judge.strLit` and the six companion base cases — and one **soundness bug in
the checker**, found by reading an obligation rather than by searching for a witness. The
ladder reads **16 of 83**.
`Ratchet/` untouched (177/232, 177/177 + 140/140); `Denote/Examples.lean`'s 31 `#guard`s green;
axiom-clean, no `sorry`.

Clink 44 left `strLit` undischarged with its reason written out (§The fourth stall point): a
string literal allocates, `StateOk` said nothing about the heap's core classes, and `denM`
did not survive a heap extension. Both are now fixed, and the *shape* of the second fix is the
clink's content.

**Decision 1: the arrow is where the problem is, so the arrow is what changed.** Transporting
`denM τ` across a heap push is easy for every arm that reads the heap and impossible for the
one that reads *runs*: a run from a heap with one more object in it allocates at shifted ids,
so it is not the run from the heap without it. Three options were on the table.

* *Transport the arrow anyway.* This is an allocation-equivariance simulation over the whole
  interpreter. Rejected as not a lemma.
* *Wrap the `StateOk` components instead* — define `EnvOk`/`AsmsOk` as "…at every allocation
  future", leaving `denM` alone. Rejected because it only moves the problem: `Judge.vasgn`
  would then have to *establish* `EnvOk` at every future for the type it just bound, which is
  the same unprovable fact one level out. The right place for a monotonicity requirement is
  the definition that is not monotone.
* *Quantify the arrow arm.* Taken. `denM`'s two arrow arms and `AsmsOk` now read
  `∀ m₂, Ext m m₂ → …`.

`Ext` (`Denote/Ext.lean`) is deliberately **not** `Reaches`. Clink 44 recorded that seeding the
arrow with reachability conflicts with `denM_ctl` (the machines reachable from `m` are not
those reachable from `m` with its control word rewritten) and that any fix needs something
coarser. `Ext m m₂` — same frames, same stack, a heap that only grew — is that: it reads
neither `ctl` nor `kont`, so `denM_ctl` survives verbatim (`Ext_reCtl`), and it is reflexive
and transitive, so `Ext.refl` recovers the old reading (the change **strengthens** `denM`) and
`Ext.trans` makes the arm monotone by construction. `denM_ext` (`Denote/Grow.lean`) therefore
re-derives nothing at all about runs — the arrow case is two projections.

The price is stated rather than hidden: `Ext` pins the frame array, so the arrow this seeds is
stable under *allocation*, which is strictly weaker than `Denote/Arrow.lean`'s `ArrowStable`
(stable under *execution*). A call rung will want the stronger one, and the pinning is what
keeps the `clos` arm's captured-scope read (`closLocal m cl`, a `Machine.frames` index) a
rewrite rather than a second transport problem.

**Decision 2: `Saturated` is imported from the model's own metatheory, not restated.** The
sub-problem that nearly ate the clink is invisible until you look: `ancestors` is **fuel-bounded
by `h.objs.size + 1`** (a `partial def` would be opaque to the kernel — `RubyCore/Heap.lean`
L73), so pushing an object moves the *fuel*, and the ancestor walk before and after the push
are two different computations. `RubyCore/Proof/AncestorsGrow.lean` had already solved exactly
this, for exactly this reason, with `Saturated` ("one more unit of fuel changes nothing") and
`ancestors_congr_grow`. Re-deriving it here would be a second copy of a proof about the same
`stepFn`, which is the thing `Semantics/Interp.lean`'s module docstring argues against one
layer down. So `Denote/Ext.lean` is the **first file in the package to import
`RubyCore.Proof.*`** — the model's metatheory, not just its interpreter — and the isolation
boundary that moves is the one that was already deliberately open (`Semantics/ → ../lean`),
not `Ratchet/`'s.

`Saturated` is not free: it is a real hypothesis, `RubyCore.Proof.saturatedB` is the `Bool`
that checks it, and it is now a `StateOk` component (`HeapSaturated`). `CoreOk` is the other
new component — the boot classes are what they are — with four clauses, each used exactly once
by this rung. It will grow: `arrayLit`, `hashLit` and most of `prim` conclude a builtin class
type too.

**The finding nobody predicted: `Heap.get` is total, so a dangling reference is well-typed.**
Past the end of the heap `Heap.get` answers `default`, whose `klass` is `0` — which is
`Boot.basicObjectId`. So at a heap of size `n` the value `.ref n` is not an error; it is an
instance of `BasicObject` with no ivars, and after the push it is a `String`. Nothing in
`StateOk` forbids `Γ` from typing a local that holds one, so the transport has to survive it
rather than assume it away. That is what `Ext`'s two fresh-id clauses are (`freshIvars`,
`freshBasic`), and what `CoreOk.basicSelf` is for — it collapses "any class the dangling read
was an instance of" to the one case.

Worth recording what this *avoided*. The obvious alternative was a heap-closedness /
value-boundedness invariant ("no dangling references anywhere"), threaded through `denM`'s
recursion into array elements, hash entries and ivars, and re-established at every allocation.
It was not needed, and the reason is a two-line fact: `default.payload` is `.none`, so
`arrElems?`/`hshEntries?`/`procClosure?` already answer `none` at a dangling reference, which
makes `arrayOf`/`hashOf`/`clos` **vacuous** there instead of in need of transport. `denM_ext`
consequently has **no side condition on the value** at all.

**Definitions changed** (all expected, per `Denote/Sem/notes.md`'s "editing (1) or (2) is
expected"):

| What | Why |
|---|---|
| `denM`'s two arrow arms | Decision 1 — the only non-monotone arm |
| `AsmsOk` | same shape as the arrow, same fix |
| `StateOk` + `sat`, `core` | the fourth stall point's item 1 |
| `Arrow.lean`: `ArrowExt` added, `denM_arrowOf` restated | `ArrowFlat` kept — it is what `ArrowCheck`'s refutation direction is stated over, and the 31 guards go through it unchanged |
| `evals_pure` | generalised to a separate post-machine variable; that is the entire difference between a pure literal's inversion and an allocating one's |
| `StateOk_reCtl` | now a corollary of `StateOk_ext`; there is one place where "component `X` survives a change to the machine" is proved, not two |

`DenB.lean` needed nothing — it already answered `false` on both arrow arms, and the clink 42
docstring explaining why ("an arrow denotes a universally quantified statement about
unboundedly many runs") is now more true, not less.

**And then the wall: `Judge.vasgn` does not close, for a reason that is not about assignment.**
Written up as §The fifth stall point. In one paragraph: `Evals` runs an expression with
`kont := []`, but `.vasgn`'s first step is `withKont m (.eval rhs) (.asgnK kind x)`, so the
premise `SemJudge … e …` is about a *different run* and using it needs a **decomposition
lemma** — a run of `e` under continuation `K` passes through the state that delivers `e`'s
value to `K`. The lemma is **true**: `stepFn` is head-local in `kont` (`applyKont` and `unwind`
read only the head and pop one; all thirteen `kont :=` sites in `Interp*.lean` are pushes), and
the two exceptions — `applyKont` at `[]` and `unwind` at `[]` — are exactly the passing-through
point and a case that cannot end in `.value`. It is also **large**: measured, the one-liner
`cases e <;> unfold <;> simp only [withCtl, withKont] <;> cases h <;> rfl` closes 12 of
`evalExpr`'s 43 arms, five of the rest delegate into ~1700 lines of `Interp/{Dispatch,Send,
Reflect}.lean`, and behind those sit the builtins, which are kont-transparent but only by
inspection.

Three conclusions, and they are why the rung was left undischarged rather than half-attempted.
It is not a `Denote/` lemma — it is a structural fact about `RubyCore`'s abstract machine and
belongs beside `stepFn`, where the metatheory already handles the continuation stack by a typed
invariant (`KontOk`) rather than by decomposition, which is the technique that avoids needing
it. It blocks **every** compound rung, so the ladder's next number is gated on one decision
rather than on many small ones. And the tempting shortcut — redefining `Evals` to quantify over
continuations — is a **weakening of all 83 obligations at once**, silently, including the ten
already climbed, because `Evals` sits on the left of `SemJudge`'s implication; it is recorded
in the notes as a thing not to do.

**Decision 3: exhibit a model of `StateOk`, because two of its components are now claims
about the heap.** Every obligation begins `∀ m, StateOk κ Γ I m → …`. While `StateOk` was
eleven components read off `Ctx`, "is it satisfiable" was a theoretical question; adding
`HeapSaturated` and `CoreOk` made it a real one, since a false heap fact would make all 83
obligations vacuously true and the ladder would keep climbing while measuring nothing.
`Denote/Sanity.lean`'s `stateOk_boot` is the witness: `StateOk ctx0 [] .ivar0` at the **real
prelude-booted machine**, axiom-clean.

It is stated **conditionally on one `Bool`** rather than `decide`d, and the reason is
structural: the booted heap is the output of `Interp.run 200_000` over the whole prelude
(`RubyCore/PreludeBoot.lean`), so kernel reduction of it is not on the table. `native_decide`
would buy a theorem for the price of `Lean.ofReduceBool`, which this package does not spend.
So `bootOkB` is a `#guard` — the same status `Denote/Examples.lean`'s 31 guards have, and the
same trade `RubyCore/Proof/AncestorsGrow.lean` argues for `saturatedB` ("a hypothesis the
harness can check beats an `axiom`, and beats a proof nobody has finished"). Verified against
a decoy, as the ladder's `isDefEq` gate was: misspelling `"String"` in `coreOkB` fails the
guard and the build.

The witness is the *empty* context, and that is the honest claim: it does not exhibit a model
of a non-empty `Γ`, `κ.classes` or `κ.asms`. It is nevertheless the interesting instance, being
exactly the state a whole-program judgment starts in.

**Decision 4: the six companion base cases, and saying out loud that they are cheap.**
`Judge` is one of eight mutual inductives, and six of the other seven start at a base case —
the empty argument, keyword, pair, rescue, constant and nesting lists. All six are discharged
(`Denote/Rules/Nil.lean`), four of them vacuously. They are climbed *in their own families'
constructor order*, which is the discipline as written; they are not padding (a `SemJudgeAll`
whose base case did not force `vs = []` and `m' = m` would be the wrong definition) and they
are not work (the ladder's own report already says "a rung is one rule, not one unit of
work"). `JudgeSeq` is the one family whose first constructor is absent, for the same reason
`Judge.vasgn` is: `JudgeSeq.last` runs its statement under a pushed `.seqK`.

**And then the finding the whole apparatus exists for: `Judge.vasgn` is UNSOUND.** Written up
with its reproducer in `found-issues.md` §F1 — the first entry in that file about the checker
rather than about the model, and the header now says why it is there.

```ruby
x = 1
f = lambda { x }
x = "a"
f.call + 1        # CRuby: TypeError.  validate: true, type Integer.
```

`Judge.lambdaLit` records the creation-site environment into the type
(`.clos idx (envToSpine Γ) …`). A Ruby block captures **by reference**, so that spine is a
claim about a *binding*, not about a value — which is exactly what `Ty.sameAs` is, and
`Judge.vasgn` already knows it about `sameAs`: it applies `killAliasesTo Γ' x` and its
docstring enumerates the three ways an alias goes stale. It does the same job for no
`Ty.clos`. `capIntact` is a different guard (it stops a block *body* from retyping a captured
local); nothing stops ordinary code after the literal.

Three things about this are worth more than the bug.

1. **No search was involved.** This is not a witness found by `Plausible` or by the concolic
   engine. The obligation's conclusion asks for `StateOk` at the post-machine, whose `EnvOk`
   component asks for `denM (clos idx cap σ) m' f`, which is
   `denSpine cap m' (closLocal m' cl)` — the captured *frame's* locals, read after the
   assignment, and `Machine.setLocal` writes through the captured chain. Reading the
   obligation is what produced the program; the program was then run to confirm it (CRuby:
   `TypeError`; the model: `uncaught` with `Semantics.typeStuck = true`).
2. **It names one rule.** `lambdaLit`'s obligation is true (the spine does match `Γ` at the
   moment of creation) and `closCall`'s is true given a spine that denotes. `vasgn` is the
   rule that claims to leave the rest of `Γ` alone and does not. That precision is the
   difference between this ladder and the corpus ladder, where a whole-program `false` says
   only that *something* is out of the fragment.
3. **The corpus could not have found it**, and did not: 232 agree, 140 negative controls
   reject, and no rung writes the shape. §Architecture's "a ratchet whose number depends on a
   live sample is not a ratchet" has a dual, which this is: a ratchet whose *soundness
   evidence* depends on a live sample is not soundness evidence.

Not fixed, per the working procedure — `Ratchet/` is untouched by this clink and the rung
stays undischarged. `found-issues.md` §F1 carries the shape of the fix (a `killClosuresOver x`
beside `killAliasesTo x`; `vasgnAlias` has the identical hole) and the negative control the
corpus should gain.

### State

**177 rungs of 232**, unchanged (`Ratchet/` untouched; `run_ratchet.sh` and
`run_check_rungs.sh` still read 177/232, 177/177 and 140/140), and **16 of 83 `Judge` rules
discharged** — the ten above plus the six companion base cases. New: `Denote/Ext.lean`,
`Denote/Grow.lean`, `Denote/Rules/Alloc.lean`, `Denote/Rules/Nil.lean`,
`Denote/Sanity.lean`. Modified:
`Denote/Den.lean`, `Denote/Arrow.lean`, `Denote/Sem/State.lean`, `Denote/Rules/Core.lean`,
`Denote/Rules/Lit.lean`, `Denote/Rules.lean`. `Denote/Examples.lean`'s 31 `#guard`s green.
Axiom-clean throughout — every new file ends in its own `#print axioms`, and each reports only
`propext`/`Classical.choice`/`Quot.sound`.

---

## Clink 46 (2026-09-01) — the soundness bug fixed, and the regressions that pin it. **178 rungs / 235, 16 of 83 rules**

Clink 45 found `Judge.vasgn` certifying a type-stuck program and, per the working procedure,
left it alone (`found-issues.md` §F1). This clink fixes it. `Ratchet/` is modified for the
first time in three clinks; the semantic ladder is untouched at **16 of 83**, because the rule
is now *true* but proving it still needs the continuation lemma (§The fifth stall point).

**The bug, in one sentence.** `Judge.lambdaLit` records the creation-site environment into
`Ty.clos`'s captured spine; a Ruby block captures **by reference**, so that spine is a claim
about a *binding* — exactly what `Ty.sameAs` is — and `Judge.vasgn`, which already kills
aliases to the assigned name, killed no closure over it.

**Decision 1: fix it where `killAliasesTo` already lives, and make the fix the identity on
closure-free environments.** `killClosOver` (over `Env`) and `killClosOverSpine` (over an ivar
spine) widen to `.any` every entry whose type records a capture of the assigned name; `capStale`
is the walk that decides. The alternative — a *premise* that no such binding exists, rejecting
the whole program — was rejected because it is a worse error for the same rejection and because
the identity property is what let 177 derivation terms in `Ratchet/Rungs.lean` stay untouched.
That property is not luck: it is the same one `killAliases`' docstring claims for the alias
operations, and it is why an invalidation belongs in the *outgoing state* rather than in a
premise whenever it can.

Three sub-decisions inside it, each of which could have gone the other way:

* **`.any`, not "drop the binding".** Dropping makes a later *read* of the name underivable
  (`Judge.var` needs `envGet?` to answer). `.any` keeps the name bound and is unusable on
  purpose — it matches no `PrimSig` row, is not `EqSafe`, and is not a `.clos`, so `f.call`
  has no rule.
* **Precise, not blanket.** A capture only goes stale if the recorded type *differs* from the
  new one, so `x = 1; f = lambda { x }; x = 2` still types. That is the same boundary
  `capIntact` draws for a block body that assigns to a captured local, and
  `corpus/235-lambda-capture-reassigned-same-type` is a **positive** rung, so a blanket
  erasure would now fail the ladder rather than pass it quietly.
* **The whole type, not the outermost `clos`.** A stale capture can sit under a `nilable`, in
  an array element, in an `inst`'s ivar spine, or inside another closure's captured spine
  (`g = lambda { x }; f = lambda { g }`). `capStale` walks all of them, and erasing the
  *outermost* type is sound because every value inhabits `.any`.

**Decision 2: the premise, for the half that cannot be widened — and it is a second bug.**
Checking the first fix produced a second reproducer:

```ruby
x = 1
x = lambda { x }
x.call + 1        # CRuby: NoMethodError (Proc + Integer)
```

Here the stale record is in the type being **bound**, and in the rule's own type index, so
there is nothing left to widen: `killClosOver` runs before `envSet` and the conclusion's `τ`
is the RHS's type either way. Widening the conclusion (`killClosTy x τ τ`) is not available —
`Judge.varAlias`'s docstring records why a conclusion of the form `f τ` for a non-injective
`f` is unusable: every derivation would have to write its type out. So it is a **premise**,
`capStale x τ τ = false`, and the thing that made it free is that it is an **`autoParam`**
(`:= by rfl`). `Judge.vasgn h` still elaborates; the 163 `vasgn` occurrences in `Rungs.lean`
needed no edit. The one place it is not free is `Ratchet/Proof/ChkSound.lean`, where the
premise has to come from the checker's own guard — three extra `split at h` lines, and that is
the whole cost of keeping `chk` and `Judge` in step.

**What was checked and left alone.** The `Ctx` fields the rule cannot rewrite (`selfTy`,
`blockTy`, `consts`) could in principle carry a `.clos` over the assigned name. Both routes
are closed today for reasons that are *not* stated as premises, and `found-issues.md` §F1
records that rather than claiming more: a method frame captures nothing, so `setLocal` cannot
reach the frame such a closure captured, and inside a block frame `capIntact` already requires
the whole enclosing environment's types to survive. The ivar route (`@f = lambda { x }`) was
probed directly, is rejected today for an unrelated reason, and is now covered by
`killClosOverSpine` anyway.

**Decision 3: three corpus rungs, not one.** Two permanent negatives (one per bug) and one
**positive**. The positive is the one worth arguing for: without
`lambda-capture-reassigned-same-type`, `capStale` could be strengthened to a blanket erasure
and every gate would stay green while the checker quietly stopped typing a common shape. A
soundness fix wants a precision control for the same reason a `PrimSig` row wants a
neighbouring negative.

They are **appended out of position** — tier 9 rungs at 233/234/235 — because the corpus
numbers by list position and `corpus/042`, `corpus/135` and `corpus/136` are cited by number
in `AGENTS.md`, `Ratchet/Judge.lean`, `Ratchet/Ty.lean`, `Ratchet/Rungs.lean`,
`CheckRungs.lean` and here. Inserting in place would renumber ~125 rungs and invalidate every
one of those references; the tier field is what the report groups by, so position is cosmetic.
The reasoning is a comment in `scripts/generate_corpus.py` so the next person does not
"tidy" it.

Both unsafe programs are **also** `CheckRungs.lean` controls, for the reason `corpus/042`'s
twin is: that is the place where a rejection is labelled *sound* by running the program.
Both report `rejected (sound: really type-stuck)`.

**The number that matters is not 178.** The corpus ladder read **232/232 agree and 140/140
controls with this bug in place**, and it could not have found it — no rung wrote the shape,
and a corpus is a sample. The semantic ladder found it by *reading an obligation*
(`Obl.Judge.vasgn`'s conclusion asks for `EnvOk` at the post-machine, whose `clos` arm reads
`closLocal m' cl` — the captured frame, which `setLocal` writes through), which is the whole
argument for having a second ladder measuring justification rather than reach. §Architecture's
"a ratchet whose number depends on a live sample is not a ratchet" has a dual, and this is it:
a ratchet whose *soundness evidence* depends on a live sample is not soundness evidence.

### State

**178 rungs of 235** (was 177 of 232 — three new tier-9 rungs, one of them climbed), **21
permanent negatives**, **142/142** `CheckRungs` controls, **177/177** hand derivations
unchanged and unedited, **235/235** corpus agreement, and **16 of 83 `Judge` rules discharged**
(unchanged; `Judge.vasgn`'s obligation is now true but still needs the continuation lemma).
Modified: `Ratchet/Ty.lean` (`capStale`, `killClosOver`, `killClosOverSpine`),
`Ratchet/Judge.lean` (`vasgn`, `vasgnAlias`), `Ratchet/Validate.lean`,
`Ratchet/Proof/ChkSound.lean`, `CheckRungs.lean`, `scripts/generate_corpus.py`. New:
`corpus/233`, `corpus/234`, `corpus/235`. Axiom-clean; no `sorry`.

---

## Clink 47 (2026-09-01) — the fixed rule, discharged. **178 rungs / 235, 17 of 83 rules**

Clink 46 fixed `Judge.vasgn`'s soundness bug and left the rung undischarged. This clink
discharges the twin, **`Judge.vasgnAlias`** — and the proof is the point, because it is where
the fix stops being a patch that rejects a counterexample and becomes the thing the semantics
asks for.

**The one sentence.** `capStale`, the function `Judge.vasgn` uses to decide which bindings to
widen, is the **side condition of `denM_setLocal`** (`Denote/Local.lean`) — the transport of a
type's meaning across a rebinding. Checker guard and semantic transport are one predicate. A
fix that had been merely *sufficient to reject the program* would have shown up here as a
transport that needed some other hypothesis.

**Why `vasgnAlias` and not `vasgn`.** `vasgn`'s right-hand side is an arbitrary expression,
which runs under a **pushed** continuation (`withKont m (.eval rhs) (.asgnK …)`), while its
premise `SemJudge … e …` is about a run under the *empty* one. Consuming it needs the
continuation-decomposition lemma (§The fifth stall point) — a fact about `RubyCore`'s abstract
machine that gates every compound rung, measured in clink 45 and unchanged. `vasgnAlias`'s
right-hand side is a `.var`, so the whole run is four concrete `stepFn` steps
(`evals_four`). Discharging it is the sharpest available statement of the split: **the rule is
sound and provably so; the general one waits on a machine lemma, not on assignment.**

### Three definitions moved, each a correction

**1. `Later`, and why the arrow needed a *second* relation.** `Ext` (clink 45) pins the frame
array — which is what makes `denM_ext`'s `clos` case a rewrite, and what makes it useless the
moment a rule rebinds a local. The arrow and `AsmsOk` quantify over runs, so they need the
*widest* domain every machine change lands in; the `clos` arm reads `Machine.frames` and must
**not** be monotone under a rebinding, since that is exactly the fact §F1 turned on. So: two
relations, `Ext ⊆ Later`, and the split is forced rather than chosen. `Later` allows a
rebinding and forbids a frame push, which is the clause the first *call* rung will have to
spend. Each rung that needs the arrow to survive one more step kind widens it by one clause,
and the destination was already written down — `ArrowStable`, the arrow at every reachable
machine. The alternative considered and rejected: make `capStale` fire on arrow types, so
arrow-typed bindings get widened away. That works for `EnvOk` and does **nothing** for
`AsmsOk`, which lives in `Ctx` and cannot be widened — so the quantifier had to move anyway,
and moving it once is cheaper than moving it and also coarsening `capStale`.

**2. `StateOk.frameInRange` — there is a current frame.** `Machine.getLocal` and
`currentFrame` are *total*: at a machine whose `stack.headD 0` is past the end of the frame
array they answer `nil` and the default frame, and `setLocal` is a no-op. That is not an error
state, it is a machine where `Γ` describes bindings that do not exist — and where
"the value `x` names after `x = e` is the value assigned" is **false**. One inequality, and
`Denote/Sanity.lean`'s guard checks it at the booted machine along with the other two.

**3. `EnvOk`'s identity conjunct is `Value` equality, not `Value.identEq` — and the difference
is a model bug.** The first reading used the model's own `equal?`, on the argument that
`Ty.sameAs` claims object identity. `Value.identEq` is not that: on `Float` it is `a == b`, so
it calls `0.0` and `-0.0` the **same** object (two different values, and an assignment through
one is not visible through the other) and `NaN` and itself **different** ones (`Float`'s `==`
is false at `NaN`, so `identEq v v` is not reflexive). The second made `Obl.Judge.vasgnAlias`
false at a local holding `NaN`, for a reason with nothing to do with aliasing. In this model a
`Value` *is* the object reference, so object identity is `Value` equality; the model's `equal?`
quirk is now a `found-issues.md` §F1 entry of its own and the denotation does not inherit it.

### What the machine lemmas cost

`Denote/Local.lean` is the file, and the only part that is not bookkeeping is the **lockstep**.
`setLocal` writes to the first frame on the current frame's captured chain that binds `x`, or
to the current frame; `getLocal` reads by walking the same chain. Everything else in the file
falls out of "`setLocal` is one `Array.set!` at an index no lemma needs to name" — the target
is left abstract (`∃ T, frames' = frames.set! T (write T)`, which is `rfl`), so the field
lemmas are three-line case splits and the two walk lemmas (`= v` at `x`, unchanged elsewhere)
are one induction each.

The exception is `getLocal_setLocal_self`: "the value `x` names after the write is the value
written". The *disjunction* is not enough there — the rule binds `x` and the obligation asks
about the value that binding names — so `setLocal.owner` and `getLocal.go` have to be shown to
stop at the **same** frame, by an induction that runs both walks at once (`any (·.1 == x)`
against `find? (·.1 == x)`). The fuel-exhaustion case is the one worth recording: `owner` falls
back to the *starting* frame, which is where the read begins, so the read finds the write
immediately — the walk running out is not a hole.

### Two more corrections the rung forced, both invisible to the ladder

Both are cases where the obligation quantifies over a `Γ` no derivation builds, and the
definition was wrong there.

* **Nested aliases.** `killAliasesTo` peeled one `sameAs` layer, so `sameAs x (sameAs z ρ)`
  survived an assignment to `x` as an alias to `z` that nothing justifies. `killAliasTy` now
  collapses an alias to `x` with `deAlias` (peel all layers). `vasgnAlias` binds
  `sameAs x (stripAlias σ)` and `stripAlias` has already peeled one, so no rung is affected.
* **`capStaleCtx`.** `selfTy`, `blockTy` and `consts` can each hold a frame-sensitive type, and
  `Ctx` is an **input** to every rule — nothing rewrites it, so nothing can widen them. They
  became a fourth premise, `autoParam`-discharged like `hcap`. Sound rather than precise: a
  method frame captures nothing, so an assignment inside a method body cannot reach the frame
  `blockTy`'s closure captured, but the premise refuses the case where the two merely share a
  name. Recovering that precision needs a `StateOk` component stating frame-chain
  disjointness; no rung has asked for one, and `found-issues.md` §F1 says so.

### State

**178 rungs of 235** and **17 of 83 `Judge` rules discharged** (`Judge.vasgnAlias`). Corpus
agreement **235/235**, hand derivations **177/177**, negative controls **142/142** — all
unchanged, and `Ratchet/Rungs.lean` was again not edited: `capStaleCtx` is an `autoParam` and
the two new `Ty` functions are the identity on everything on file. New: `Denote/Local.lean`,
`Denote/Rules/Asgn.lean`. Modified: `Ratchet/Ty.lean` (`deAlias`, `killAliasTy`, `capStale`'s
spine clause), `Ratchet/Judge.lean` (`capStaleCtx` + the premise), `Ratchet/Validate.lean`,
`Ratchet/Proof/ChkSound.lean`, `Denote/Ext.lean` (`Later`), `Denote/Den.lean`,
`Denote/Arrow.lean`, `Denote/Grow.lean`, `Denote/Rules/Core.lean` (`evals_four`),
`Denote/Sem/State.lean` (`FrameInRange`, `EnvOk`, `AsmsOk`, `StateOk_setLocal`),
`Denote/Sanity.lean`. Axiom-clean; no `sorry`; `Denote/Examples.lean`'s 31 `#guard`s green.

## Clink 48 (2026-09-01) — seven more rungs, and two stall points that are about the *shape* of the judgment. **178 rungs / 235, 24 of 83 rules**

Seven rungs, none of them behind the continuation wall, and two findings that are worth more
than the rungs: `Judge.defStmt`'s obligation is **false**, and `SemJudgeAll`'s is **unprovable
as stated** — both for reasons that are the semantic judgment's shape rather than a bug in any
rule. `Ratchet/` was not touched, and the two numbers it owns did not move.

### What was discharged

* **`Judge.selfExpr`** (`Denote/Rules/Read.lean`) — one `stepFn` step, and the rung *is* the
  `SelfTyOk` component: `κ.selfTy = some σ` is both the rule's premise and the component's
  non-trivial case.
* **`Judge.ivarRead`** (same file) — the one that cost a definition, below.
* **`Judge.regexpLit`** (`Denote/Rules/Regexp.lean`) — `strLit`'s shape (allocate, then answer
  `.ref` at the fresh id, via `ext_push` + `StateOk_ext`) with one new feature: the arm is
  **partial**. A pattern `Rx.parse` rejects steps straight to `.unsupported`, which is not a
  `.value`, so `Evals` is unsatisfiable there and the branch imposes nothing
  (`evals_of_unsupported`). Worth having by name: it is the shape **every** gated construct in
  the model takes on this ladder, and it is why a gate costs a rung nothing rather than
  blocking it.
* **`JudgeSeq.last`** (`Denote/Rules/Seq.lean`) — and this one is a **correction of a recorded
  claim**. `Denote/Rules/Nil.lean` said `JudgeSeq.last` was behind the continuation wall. It is
  not: `evalExpr`'s `.seq` arm is `| [e] => .next (withCtl m (.eval e))`, so a *singleton*
  sequence pushes no continuation and its run under `kont := []` **is** its statement's run
  under `kont := []`, one step later. The wall is real for `JudgeSeq.cons`, whose first
  statement runs under `.seqK rest`. Measured, not argued: one `rfl` step lemma.
* **`JudgeRescues.cons`** (`Denote/Rules/Rescue.lean`) — the only `cons` rule in the family the
  wall does not block, for a signature reason: `JudgeRescues` threads **no outgoing state**
  (its rule pins `Γ' = Γh ++ Γ` and `I' = I` as premises, because a handler's assignments must
  not escape a clause that may not have run), so the premise about the head handler is about
  *the same run* the conclusion asks about. Nothing to decompose, nothing to transport.
* **`JudgeConsts.cons`** and **`JudgeNested.cons`** (`Denote/Rules/Cls.lean`) — list
  bookkeeping plus `classMethods?`'s injectivity at the head. These are the two rungs the
  one-level-deep `SemJudgeNested` was *designed* to make provable: the recursion is carried by
  the constructor's own premise, so the `cons` case needs no induction principle over
  nestings. The recorded risk in its docstring is unchanged — `Judge.classStmt` is what will
  say whether one level is enough, and `classStmt` is blocked by the sixth stall point below.

Three of the seven companion families (`JudgeRescues`, `JudgeConsts`, `JudgeNested`) are now
complete.

### Definitions changed, and why each is a correction

**1. `SelfSpineOk` now says the spine is *complete*.** `Judge.ivarRead` types `@x` as
`(ivarGet? I x).getD .nilT`, so at a spine silent about `@x` it claims `@x : Nil`. The old
component was `denSpine I m (ivarOf …)` — a **lower** bound, and `Denote/Den.lean` says so of
`denM`'s `inst` arm in as many words ("ivars the type does not mention are unconstrained") —
so a conformant machine could hold `@x = 7` at `I = .ivar0` and the rule would be false of the
semantics. The second conjunct (`ivarGet? I x = none → ivarOf … x = .nil`) is exactly the
invariant `Judge.ivarRead`'s own docstring already named: *"the default is sound only because
the spine is complete"*. Two decisions inside it that were **not** forced:

* Stated as "reads as `nil`" rather than "is absent from the object". The weaker of the two,
  and the one `Judge.ivarAsgn` can re-establish at a `nil` right-hand side (nothing removes an
  ivar entry, and CRuby cannot tell an unset `@x` from `@x = nil` through a read).
* **No matching clause on `EnvOk`.** The asymmetry is the rules': `Judge.var` requires
  `envGet? Γ x = some τ`, so there is no rule typing an unbound local, while `ivarRead` is
  total in `x` on purpose — in Ruby reading an unset ivar is legal and yields `nil`.

Cost: `StateOk_ext`/`StateOk_setLocal` each gained a line (the second needs
`ivarGet?_killClosOverSpine_none` — widening a spine does not change which names it mentions),
and `Denote/Sanity.lean`'s boot `Bool` gained a fourth frame clause (`selfIvarsEmptyB`: the
toplevel `self` carries no ivars). That clause is **measured, not assumed** — the prelude runs
before that machine exists and could have set an ivar on `main`; the `#guard` says it did not.

**2. `CoreOk` grew the `Regexp` row** (`regexpNamed`/`regexpSelf`/`regexpBasic`), which is the
growth that structure's docstring predicted for every rule concluding a builtin class type.
`coreOkB` measures all seven clauses at the booted heap.

**3. `Denote/Join.lean` is new, and it carries `LawfulBEq Ty`.** Two theorems the ladder will
spend repeatedly — `denM_joinT_left`/`denM_joinT_right`, "a join is an upper bound" — plus the
union plumbing they need (`unionMems`/`dedupTys`/`unionOf` against `denM`, three small
inductions). The reason it is a file rather than three lines in a rung: six rules consume
`joinT` (`if'`, `ifNoElse`, `arrayLit`, `hashLit`, `beginRescue`, `while'`) and every one of
them needs the same fact, which is about the *type language* and not about any rule.

The `LawfulBEq Ty` instance is the part worth recording. `joinT`/`joinTy` are written with
`==` guards, and reading a guard as an **equation** is what a proof about them needs —
`Ratchet/Ty.lean` derives `BEq` **without** `LawfulBEq`, and `Ratchet/` may not be edited from
this side of the isolation boundary. So it is proved here, once, by structural induction over
the twenty constructors (mismatched pairs close by `Bool.noConfusion`, matching pairs by the
defeq cast to the field-wise `&&`). It is not a claim about the checker; it is the missing half
of a `deriving` clause, and it deletes the day `Ty` adds `deriving LawfulBEq`.

### The sixth stall point: a declaration statement makes the incoming `κ` stale

**`Judge.defStmt`'s obligation is false**, and it is not §F1 again — the rule is fine and the
checker gives the right answer. `SemJudge` concludes `StateOk κ Γ' I' m'`: conformance with the
**incoming** `κ`. For `def foo; 1; end; def foo; "s"; end`, the second statement's `κ.defs`
still holds the first `foo` (put there by `JudgeSeq.cons`/`Ctx.afterStmt`), a conformant
machine really has that method installed, and `RubyCore`'s `defineMethod` **replaces** — so
`DefsOk κ.defs m'` asks for a body the heap no longer has. `casgn`, `cpathAsgn`, `classStmt`,
`moduleStmt` and any `.seq` containing one are false for the same reason.

Checked rather than assumed, both halves:

```
$ export-json <that program, then `foo`> | ratchet --stdin
{"type":"String","validate":true}        # CRuby prints s — the checker reads defGet?, i.e. the newest entry
```

Two defects are tangled, and only the first is fixable inside `State.lean`: (1)
`DefsOk`/`ClassesOk` quantify over the *whole* table while the checker only consults the first
match, which makes `StateOk` unsatisfiable after any redefinition — a **vacuity** risk of the
kind `Denote/Sanity.lean` exists to police; (2) `κ` is not threaded through the judgment, and
fixing (1) does not help, because the live entry is still the stale one. The conclusion would
have to be at `κ.afterStmt e τ` — expressible for `SemJudge`, **not** expressible for
`SemJudgeSeq`, whose accumulated context is a fold over statement types its signature does not
carry. That is a design decision about the semantic judgment, so it is written down and left
for its own clink rather than half-done here; `Denote/Sem/notes.md` §The sixth stall point has
the full statement, including why the fold direction is evidence the change is the right one.

### The seventh: an argument list is not a snapshot

Found by inspection while attempting `JudgeAll.cons`, and the honest status is **unprovable as
stated, one `PrimSig` row away from being a soundness bug.** `SemJudgeAll` concludes
`DenAll τs m' vs` — every argument's type at the machine the *whole list* left behind, which is
the right machine for the consumer — so the `cons` rung must transport the first argument's
type across the evaluation of every later argument. No such transport exists: `Ext` demands a
heap that only grew, and an arbitrary Ruby expression can mutate.

What makes it harmless **today** is the table, not the judgment: `PrimSig` has no row that can
change a value's type in place. No `[]=`, `push`, `concat`, `replace`, `clear`, `insert`,
`unshift`, `store` or `map!` row exists; the only mutator is `arrayPush` (`<<`), whose
signature forces the pushed element to have the array's own element type — and at
`.arrayOf .never` (the empty literal) every push is rejected for want of a `never` argument. So
the dependency is recorded in both directions: the day an `Array#[]=` row is added, this stall
becomes a `found-issues.md` §F entry, and a rung is not what will catch it.

**A second defect in the same family, same inspection:** `SemJudgePairs` reads a hash literal's
pairs as *all keys then all values*, while `JudgePairs.cons` — and `evalExpr`'s `.hash` arm —
interleave. They coincide at one pair and diverge at two, so the `cons` obligation is stated
over an evaluation order the machine never performs; being a hypothesis, the effect is vacuity
rather than falsity, and `Judge.hashLit` would find nothing usable to consume. One-line fix,
left for the clink that attempts the rule so that a rung checks it rather than an eye.

### And a soundness bug, found by asking what `Judge.lambdaLit`'s obligation needs

The rule concludes `.clos idx (envToSpine Γ) …` for `.send none "lambda" [] (some block)` with
**no premise about the name being free**. So the rung has to know how a conformant machine
dispatches `lambda` — and `StateOk` permits a machine whose `Object` carries a user method of
that name. In CRuby a toplevel `def` is a private instance method **on `Object`**, and `Kernel`
is included *in* `Object`, so the user's definition shadows `Kernel#lambda`:

```ruby
def lambda; 5; end
f = lambda { 1 }
f.call + 1
```

CRuby: `NoMethodError` (type-stuck). `validate`: **`true`, type `Integer`**. Two entries came
out of it, and the pair is the interesting part:

* **`found-issues.md` §A5 (model).** The model cannot shadow the name *at all* —
  `Interp/Send.lean`'s `finishSend` special-cases `"lambda"`/`"proc"` at an implicit-self send
  with a literal block **before any method lookup** — so it returns `2` where CRuby raises.
* **`found-issues.md` §F2 (checker).** Against the *model*, `Judge.lambdaLit` is right, and
  that is why the rule's obligation is still climbable: the model's dispatch is unshadowable.
  The wrong answer is about **Ruby**, and it arrives through the divergence. This is the first
  entry where the two soundness statements come apart, and the moral is about the other gate:
  `run_agreement.sh` (CRuby vs the model, 235/235) is exactly what would have caught it, and it
  never saw this program.

The checker needs the premise **either way** — the day the model shadows, `lambdaLit` becomes
unsound against the model too — and it is `Judge.bareName`'s shape (`defGet? κ.defs m = none`,
plus the class table for a `lambda` defined in a class body). Not fixed here: this clink ran
under an explicit "do not modify `Ratchet/`" constraint, and the premise moves 14 derivations
plus the two committed ladder numbers. It wants its own clink with a negative-control rung, so
that the fix is pinned by a program rather than believed.

### And a third finding, which upgrades the sixth stall point to a soundness bug

The stall point above says a rule cannot re-assert conformance with the incoming `κ` after a
statement that declares something. The question it invites — *a call runs statements too* — has
a two-line answer:

```ruby
def bar; 1; end
def foo; def bar; "s"; end; 1; end
foo
bar + 1
```

`validate`: `true`, type `Integer`. CRuby **and** the model: `TypeError, no implicit conversion
of Integer into String`. The two executors agree, so unlike §F2 this is a wrong answer about
the model as well as about Ruby — the §F1 shape exactly, written up as `found-issues.md` §F3.

`Ctx.afterStmt` grows `κ.defs` at the statement boundaries of the sequence being typed;
`Judge.vcallDef` concludes at the **same `κ`** it started from; `Heap.defineMethod` *replaces*.
So the nested `def` is recorded where it cannot help and invalidates what the caller's context
still claims. Every call rule is exposed (`callDef`, `callDefKw`, `callMethod`, `selfCall`,
`closCall`, `iterBlock`, …) — a *family*, not a rule.

Three things this changes about the write-up above rather than adding to it:

* **The sixth stall point is not bookkeeping.** It was recorded as "the obligation's shape is
  wrong"; it is also "the checker is wrong", and the second follows from the first by reading
  what `DefsOk` asks of the post-machine.
* **It is an argument for the signature change over the premise.** A per-rule premise ("this
  body declares nothing `κ` records") fixes the calls; threading the context
  (`Judge … κ'`) fixes the calls *and* `defStmt`'s own false obligation. Two problems, one fix.
* **No witness search was involved, again.** That is now three findings (§F1, §F3, and §F2's
  model divergence) produced by reading an obligation rather than by running programs, against
  a corpus of 235 agreeing rungs and 142 negative controls that covers none of them.

Not fixed here: `Ratchet/` was out of bounds this session, and the fix moves derivations and
both committed numbers. The regression to add with it is the program above, as an
`unsafe_program` rung.

### State

**24 of 83 `Judge` rules discharged** (`selfExpr`, `ivarRead`, `regexpLit`, `JudgeSeq.last`,
`JudgeRescues.cons`, `JudgeConsts.cons`, `JudgeNested.cons`), three companion families
complete. Corpus agreement **235/235**, hand derivations **177/177**, negative controls
**142/142** — unchanged, and `Ratchet/` was not edited at all. New: `Denote/Join.lean`,
`Denote/Rules/Read.lean`, `Denote/Rules/Regexp.lean`, `Denote/Rules/Seq.lean`,
`Denote/Rules/Cls.lean`, `Denote/Rules/Rescue.lean`. Modified: `Denote/Sem/State.lean`
(`SelfSpineOk`, `CoreOk`, `ivarGet?_killClosOverSpine_none`), `Denote/Sanity.lean`
(`selfIvarsEmptyB`, seven-clause `coreOkB`), `Denote/Rules.lean`, `Denote/Rules/Nil.lean` (the
corrected claim), `Denote/Sem/notes.md` (stall points six and seven), `found-issues.md`
(§A5, §F2, §F3), `AGENTS.md`. Axiom-clean
throughout; no `sorry`; `Denote/Examples.lean`'s 31 `#guard`s green.

## Clink 49 (2026-09-01) — the two soundness bugs fixed, and the model taught to shadow. **178 rungs / 238, 24 of 83 rules**

Clink 48 found two wrong answers by reading obligations and left both unfixed, under an
explicit "do not modify `Ratchet/`" constraint. This clink lifts it and pays them off: §F3 (a
method body's `def` escaping the checker's context), §F2 (`Judge.lambdaLit` with no premise
that the name is free) and §A5 (the *model* unable to shadow `Kernel#lambda` at all). Plus
three corpus rungs — two regressions and one climb target.

### §F3, and the decision that made it five lines instead of twenty premises

The bug is a family: every rule that types a **call** concludes at the `κ` it started from, so
a `def` inside the body invalidates a table the caller still trusts. The obvious fix is a
per-rule premise ("this body declares nothing `κ` records") on `callDef`, `callDefKw`,
`callMethod`, `selfCall`, `closCall`, `iterBlock`, `yieldExpr`, … — twenty rules, twenty `chk`
arms, twenty `chk_sound` cases.

**It went at the lookup instead**, and the reason is the observation that makes the whole
family one place: *a rule can only type a call by first fetching the body.* `defGet?` for a
top-level method, `defGet? c.methods`/`mroGet?` for an instance or singleton method,
`closGet?` for a Proc or a block a method may `yield`. Two functions, filtered by one new
`declFree : Expr → Bool`:

* no premise was added to any rule,
* no derivation term in `Rungs.lean` moved (177/177 still check),
* exactly **one** `chk_sound` case changed — and not for the filter.

That one case is the part worth recording, because it is where the filter *would* have been
unsound if applied naively. `Judge.bareName`'s premise is `defGet? κ.defs m = none`, and after
the change that no longer means "this name is not a method of the program": a `def x` whose
body declares is still a `def x`, and a `vcall x` reaching it is not a `NameError`. So
`bareName` reads a new raw lookup, **`defDeclared?`**, and `chk`/`chk_sound` follow. A filter
on a lookup used in *negative* position weakens the premise; noticing which uses are negative
is the whole safety argument for doing it this way.

**Alternatives rejected.** (1) The per-rule premise, above — same soundness, twenty times the
churn, and it would have had to be repeated for every future call rule. (2) Refusing to
*record* declaring bodies (`extendDefs`/`clsMember?`), which is the same idea one step earlier
but misses the inline block bodies `iterBlock` types straight from the syntax. (3) Threading
the context through the judgment (`Judge κ Γ I e τ Γ' I' κ'`), which is the **right** fix and
is still recorded as such: it repairs this *and* `Judge.defStmt`'s false semantic obligation
(`Denote/Sem/notes.md` §The sixth stall point). It changes every derivation on file and wants
its own clink; what is here is the conservative half.

**What it costs, and it is a real cost:** a method whose body declares is now **uncallable** by
this checker rather than callable-and-wrong. Nothing else can reach it either — typing a body
needs a rule for every statement in it, so a method that merely *calls* an unrecordable one is
rejected in turn. No rung on file wanted the precision (177/177, 35 mismatches — one more than
clink 48's 34, and that one is the new climb target below).

`declFree` is its own structural recursion, mutual with list/pair/kwarg/rescue walkers rather
than written with `List.all`, for the reason `exprEq`'s docstring gives at length: a helper
outside the nested-inductive bundle pushes the group onto **well-founded** recursion, and then
it stops reducing in the kernel — which every `rfl`-discharged `defGet? … = some d` premise in
`Rungs.lean` depends on. Recorded gap: it does not walk `Param` defaults
(`def f(x = (def bar; end; 1))`), because that puts a third inductive in the bundle.

### §F2 and §A5 — the two halves, and why both were needed

`lambda { … }` is an implicit-self send; in CRuby a toplevel `def lambda` is a private method
on `Object` and `Kernel` is included *in* `Object`, so the user's method wins.

* **Checker:** `Judge.lambdaLit` gained `nameFree κ m = true` — no top-level `def` of the name
  and no class or module declaring it. An `autoParam`, so the 14 `Judge.lambdaLit` uses in
  `Rungs.lean` did not move; `chk`'s guard gained a conjunct and `chk_sound` destructures one
  more `&&`. Deliberately coarse (any class, not `self`'s class): sharpening it means walking
  the ancestor chain, and nothing wants the precision.
* **Model:** `finishSend` special-cased `"lambda"`/`"proc"` **before any method lookup**, so
  the name was unshadowable — the model returned a Proc where CRuby raised. It now takes the
  shortcut only when `methodOn` finds nothing user-defined, which is the same `builtin.isNone`
  test the `X.new { … }` arm three lines below already used. `mkLam` is computed from the same
  flag, so a shadowed call passes an ordinary Proc as its block, as CRuby does.

**Both halves were needed and neither is redundant.** Without the model fix the corpus rung
could not exist (a disagreement aborts `run_ratchet.sh` before the ladder is reported).
Without the checker fix the program would be certified the day the model started shadowing —
the rule was *accidentally* sound, against a model that could not express the counterexample.

**The model change is verdict-neutral, measured rather than asserted:** tier-0 difftest before
and after, **992 agree / 306 gated / 0 disagreements** out of 1304, byte-identical verdict
counts (run at `difftest/reports/20260901-231451-tier0-lean` and `…-231858-…`, the second with
the change stashed). Ratchet corpus agreement 238/238.

### Three corpus rungs

* `236-nested-def-redefines-unsafe` and `237-shadowed-lambda-unsafe` — the two regressions,
  `expect_validate: false`/`unsafe_program`, each also a `CheckRungs.lean` control so the
  rejection is labelled *sound by running the program*: both report `rejected (sound: really
  type-stuck)`. Permanent negatives 21 → 23; controls 142 → 144.
* `238-yield-two-types-string-to-s` — a **climb target** (`expect_validate: true`, currently
  `false`), from a program handed over as "safe but not typed":

  ```ruby
  def hello; yield 1; yield "str"; end
  s = ""
  hello { |v| s += v.to_s }
  s
  ```

  CRuby and the model both give `"1str"`. The description does not say "yield is unsupported",
  because that is not what is wrong — bisected: one yield types, `yield 1; yield 2` types, and
  `"a".to_s` **alone** does not. The table has `intToS` and `symToS` and no `String#to_s`, so
  the block body has no rule at `v : String`. Recorded as one missing `PrimSig` row rather
  than fixed, because a row is a trusted claim about the semantics and adding one belongs with
  the pass that justifies it. The rung is worth keeping past that fix: two yields at different
  types is the smallest program that checks `yieldExpr` re-types the body **per yield site**.

### State

**178 rungs of 238**, **24 of 83 `Judge` rules** (unchanged — no rung was climbed here; the
two `Judge` changes are premises and a lookup filter, and `Obl.Judge.lambdaLit` grew a premise
with it). Corpus agreement **238/238**, hand derivations **177/177**, negative controls
**144/144**, mismatches **35** (34 + the new climb target), permanent negatives **23**.
Tier-0 model difftest **0 disagreements**, verdict-identical before and after the `finishSend`
change. Modified: `Ratchet/Judge.lean` (`declFree`, `defDeclared?`, the two filtered lookups,
`nameFree`, `lambdaLit`'s premise, `bareName`'s premise), `Ratchet/Validate.lean`,
`Ratchet/Proof/ChkSound.lean` (one case), `CheckRungs.lean` (two controls),
`scripts/generate_corpus.py` + `corpus/` (three rungs), `../lean/RubyCore/Interp/Send.lean`,
`found-issues.md` (§A5/§F2/§F3 marked fixed, each with its fix), `Denote/Sem/notes.md`,
`AGENTS.md`. Axiom-clean; no `sorry`; `Denote/Examples.lean`'s 31 `#guard`s green.

## Clink 50 (2026-09-02) — the four `.const` rungs, and the wall measured rather than estimated. **178 rungs / 238, 28 of 83 rules**

Four rules discharged (`Denote/Rules/Const.lean`), both of the definitional changes they
forced are corrections rather than conveniences, and — the part worth reading if you only
read one thing — the **fifth stall point was measured**, and it is a smaller job than
`Denote/Sem/notes.md` said.

### What was discharged

All four rules whose expression head is `Expr.const n`, which is the whole of the `.const`
family: `constCls` (a class the program declared), `constBuiltin` (`BuiltinCls`),
`constExc` (`ExcCls`), `constEnv` (a constant the context types). They are leaf rungs in
`Denote/Rules/Lit.lean`'s sense — `evalExpr` answers in one step and `evals_pure` inverts it —
so the content is entirely *which conformance component says the value is in the type*.

The three that conclude `.clsOf n` share one lemma, `semJudge_const_clsOf`, whose single
hypothesis is "if the machine resolves `n` at all, it resolves to the class `classNamed?`
names". They differ only in how they produce it.

### The scope gap, and the component that closes it

`denM (.clsOf n)`'s probe resolves the name through the **toplevel** constant table
(`classNamed?` → `constLookup`, i.e. `Object`'s own `consts`). The machine does not:
`evalExpr`'s `.const` arm runs CRuby's two-phase rule, lexical over `m.currentFrame.cref`
first and inheritance from `m.currentFrame.defmod` second. They agree at a toplevel frame and
differ at `class A; class Foo; end; end`. Nothing in `Ctx` records where the frame is
standing, so nothing in `StateOk` made the two values the same and none of the three rules'
obligations was derivable — stall point (1), a missing component.

**`ConstScopeOk`** (`Denote/Sem/State.lean`) is that component: `∀ n, constResolveAt m n =
constLookup m.heap n`, with `constResolveAt` the machine's own resolution transcribed from
`evalExpr` so a rung can rewrite with it.

*Not forced, and the alternatives were live.* Three shapes were considered:

* **`m.currentFrame.cref = [Object]`** — decidable in one `Bool` and trivially true at boot,
  but it says *every* conformant machine is at toplevel, which would make every call rung
  vacuous the moment one exists. Rejected: a component must not constrain frames the rules it
  is not about will need.
* **One-directional** (`constLookup … = some w → constResolveAt … = some w`) — enough for the
  three rungs and satisfiable by strictly more machines. Rejected once `constEnv` was
  attempted: it gives existence and agreement but not the converse, and `constEnv`'s value
  comes *from the machine*, so the other direction is the one it needs.
* **Restricted to class names** (`classNamed? m.heap n = some k → constResolveAt m n = some
  (.ref k)`) — the weakest form the three `.clsOf` rungs need, and satisfiable inside a class
  body that shadows a non-class constant. Rejected for the same reason as the previous one
  plus one more: it is three rules' premise wearing a component's name, and the next `.const`
  rule would need a fourth shape.

The cost is stated rather than hidden, in the component's own docstring: a machine standing
inside a class body that shadows a toplevel constant is **not conformant**, so the four
obligations say nothing there. That is the honest scope of the rules as written — none of them
has a premise about the frame, and each concludes about the *toplevel* name.

`Denote/Sanity.lean` proves it at the real booted machine from a new decidable clause,
`topScopeB`: `cref = [Object]`, `defmod = Object`, and every *other* ancestor of `Object` owns
no constants. The third is the one that is not obvious and is why the proof is not a one-liner
— `constLookupFrom` walks `ancestors h Object = [Object, Kernel, BasicObject]`, so it can
answer where `constLookup` (which reads `Object`'s own table and stops) answers `none`.
Measured: `Kernel` and `BasicObject` own zero constants at the booted heap.

### `ConstsOk` restated over the lookup function — the second correction

`Judge.constEnv` did not close under the old `ConstsOk`, and the reason is a defect the sixth
stall point had already named for `DefsOk`/`ClassesOk`: the component quantified over the
**table's entries** while the checker only ever consults the **lookup function**.

`Ctx.consts` is keyed by absolute path — `"::LIMIT"` at toplevel, `"::A::X"` for a constant
declared in `class A` — and the old component asked for `constLookup m.heap (stripColons p)`,
i.e. a toplevel constant literally spelled `A::X`. No heap has one. So the component was
*unsatisfiable* at any context with a nested constant (vacuity, not falsity — precisely the
failure mode `Denote/Sanity.lean` exists to police), and at the same time it said nothing
about the name `constGet?` consults when the rule fires.

`ConstsOk` now reads `∀ n τ, constGet? κ n = some τ → ∃ v, constResolveAt m n = some v ∧
denM τ m v`, and takes the whole `Ctx` rather than one field, because `constGet?` consults
`κ.frame`'s class before the toplevel path. `constEnv`'s rung is then three lines and spends
no `ConstScopeOk` at all: the component is already stated at the machine's own resolution.
This is the fix the sixth stall point recommends, applied to the first component that could
be shown to need it.

`CoreOk` grew one clause (`coreNamed`) and it is an **implication**, not an existence claim:
a name on the fixed twenty-two-element `coreClsNames` list is bound to a class *if it is bound
at all*. Stated that way because one of the twenty-two does not exist in the model — there is
no `IOError` — and `ExcCls.ioError`'s case is discharged by `const_miss_no_value` (the miss
branch gates or raises; no value, nothing to be wrong about) rather than by a fact about the
heap. Two general lemmas came out of that case and both are reusable:
`evals_of_uncaught` (a second step landing on `.uncaught` means no run returned) and
`stepFn_raiseErr_nil` (a `raiseErr` at an empty continuation escapes in one step).

### The fifth stall point, measured

`Denote/Sem/notes.md` sized the continuation-framing lemma as "~1700 further lines … and past
those sit the builtins … ~24k lines", with `evalExpr` alone closing 12 of its 43 arms by
`rfl`. That estimate was made by inspection and it is **too pessimistic**. Measured this
clink, against the real `stepFn`:

```
cases e <;> simp only [evalExpr, frameR, withCtl, withKont] <;> (repeat' split) <;> rfl
```

closes every arm of `evalExpr` whose body does not delegate, and the residue is **not** a
long tail of hard goals: it is one goal per *helper function*, each of exactly the same shape
(`helper (pk m K) args = frameR K (helper m args)`). Checked on `startArgs`, the worst case in
the residue: the same one-liner reduces it to a single goal naming `finishSend`, i.e. to
`finishSend`'s own framing lemma. So the lemma is a **dependency chain of one-line lemmas over
a bounded helper set** — `RubyCore/Interp/{Dispatch,Send,Reflect,Support}.lean` declare on the
order of thirty machine→`StepResult` helpers — rather than a line-count proportional to the
interpreter.

Two things this does not settle, recorded so the next attempt starts from them rather than
from optimism: (1) the builtins really are the open question — whether `invoke`'s descent into
`Builtins/` is `rfl`-transparent in `kont` at kernel speed is untested, and it is where the
24k lines actually live; (2) the lemma still belongs in `RubyCore/Proof/`, next to `stepFn`,
not in `Denote/` — the argument in `Semantics/Interp.lean`'s docstring (a second copy of a
proof about the same `stepFn` is a second thing to drift) applies unchanged.

### Two rules that are reachable but were not taken, and why

`Judge.bareName` and `Judge.lambdaLit` are both one-step-ish and both stalled on the same
thing, which is now written up as the **ninth stall point**: a rule with a *negative* premise
about a table (`defDeclared? κ.defs m = none`, `nameFree κ m = true`) needs conformance to be
an **upper** bound on the table, and every component of `StateOk` is a lower bound. Recorded
rather than fixed: the fix is a fixed-list component in `CoreOk`'s shape, and the rung that
spends it has to walk `startArgs`/`finishSend`/dispatch to the `NameError`, which is the
fifth stall point's machinery arriving early.

### State

**178 rungs of 238**, **28 of 83 `Judge` rules** (24 → 28: `constCls`, `constBuiltin`,
`constExc`, `constEnv`). Corpus agreement unchanged at **238/238** (nothing under `Ratchet/`
or `corpus/` was touched), hand derivations **177/177**, negative controls **144/144**,
mismatches **35**, permanent negatives **23**. Modified: `Denote/Sem/State.lean`
(`constResolveAt`, `ConstScopeOk` + its two transports, `coreClsNames`, `CoreOk.coreNamed`,
`ConstsOk` restated over `constGet?`, `constGet?_entry`/`findSome?_entry`, the `StateOk` field
and both transports), `Denote/Local.lean` (`setAt_cref`/`setAt_defmod` and their
`currentFrame_setLocal_*` corollaries), `Denote/Sanity.lean` (`topScopeB`, `constOwn_object`,
`firstM_none`, `constScope_of_topScope`, `coreOkB`'s eighth clause), `Denote/Rules/Const.lean`
(new), `Denote/Rules.lean`, `Denote/Sem/notes.md`, `AGENTS.md`. Axiom-clean
(`propext`/`Classical.choice`/`Quot.sound` only); no `sorry`; `Denote/Examples.lean`'s 31
`#guard`s green; `Denote/Sanity.lean`'s `bootOkB` guard green with the two new clauses.

## Clink 51 (2026-09-02) — the frame lemma: `StateOk` describes the whole world, and nothing more. **178 rungs / 238, 28 of 83 rules**

No rung climbed. What landed is the thing three stalled rungs were all asking for, and
separating its two halves is the whole content: `Denote/Sem/Frame.lean`.

### The diagnosis

Every component of `StateOk` was a **lower** bound — each thing `κ` records is really there —
and none said *there is nothing else*. Three stalls were that one gap in three costumes: a
rule reasoning from **absence** (`bareName`, `lambdaLit`) had no hypothesis that could reach
its conclusion, and a rule that **redefines** something had components that were unsatisfiable
rather than false. "`StateOk` describes the whole state of the world, and nothing more" is the
frame lemma, and it is two claims.

### Half one: the frame rule for conformance — already proved, now named

Conformance reads the heap, the frames and the frame stack; it does not read `ctl` or `kont`.
Everything it does not read is *frame*. `frameOnly` + `StateOk_frame` give that its name and
its general statement; the proof is `StateOk_reCtl`'s, which since clink 45 is a corollary of
`StateOk_ext`. Recorded there rather than rediscovered: `ctl`/`kont` are the *only* frame, and
the run-quantifying components (`denM`'s arrow arms, `AsmsOk`) survive them for a sharper
reason than not looking — `applyIn`/`sendIn` **overwrite** both, so the run a call denotes is
literally the same run from both machines.

### Half two: "and nothing more" — three components, not one

**`MethodsExact κ m`** is the general form: every method installed anywhere in the heap is an
axiomatized builtin (`MethodDef.builtin`), Ruby's core library written in RubyCore
(`MethodDef.fromPrelude`), or a name `κ` records (`declaresName`). The model's own two
discriminators do all the work, so this needed nothing new in `RubyCore`.

**Measured before it was stated.** At the real prelude-booted heap the number of installed
methods that are none of the three is **zero**. So this is a fact about the machine the ladder
starts from, not a hopeful invariant, and `declaresName` is exactly the room a program grows
into it.

*Not forced:* `declaresName` is **name-global** — it forgets which class a name was declared
on. The per-owner alternative is expressible (relate the owner id to a `Cls` through
`classNamed?`) and was rejected as unmotivated: the rules that consume exactness ask "did the
program define this name *at all*?", which is what a premise like `defDeclared? κ.defs m =
none` is trying to say. The cost is recorded — `bareName`'s premise constrains only `κ.defs`,
so a name declared on a *class* still satisfies `declaresName`, and that rule will want either
the owner-aware refinement or a sharper premise.

**`NameFreeOk κ m`** exists because `MethodsExact` is not enough, and this is the part worth
reading. It allows a *prelude* method, while `Judge.bareName` needs `x` to resolve to
**nothing**: "not the user's" is not "not there". So the prelude escape is dropped —
`builtin.isSome ∨ undefined`, which is exactly `finishSend`'s own `md.builtin.isNone &&
!md.undefined` shadowing test — on the fixed list `shadowableNames`
(`BareNameError`'s one row plus `nameFree`'s two), and the claim is localised to the
receiver's own ancestor chain.

**Chain-local rather than heap-global, and that is a finding rather than a technicality.** The
heap-global form is **false**: the prelude really does define a method named `proc` — `T.proc`,
the sorbet shim's type constructor — installed as a **singleton** method on the `T` module,
i.e. on `#<Class:T>`. That is off every ordinary receiver's chain (`include`/`extend` move a
module's *instance* methods, never its singleton ones), so the model's shadowing test is right
about it and the component has to be stated at the same walk in order to say so. Measured for
the record: the toplevel chain carries ~40 prelude-written methods (`tap`, `format`,
`Integer`, `!=`, and the `__`-prefixed helpers) and **none** of the three names.

*Not forced:* the `declaresName` escape is kept in `NameFreeOk` too. Dropping it would be
simpler and is wrong — a program that really does `def lambda` would then make `StateOk`
**unsatisfiable** rather than making the rule inapplicable, i.e. vacuity in place of falsity,
which is the failure mode `Denote/Sanity.lean` exists to police. With the escape, such a
program is perfectly conformant and it is `nameFree`'s premise that fails.

**`SelfLive m`** was forced by `NameFreeOk`'s transport and closes a gap nothing had named:
`StateOk` never said `self` is a real object. `classOf` reads `Heap.get`, `Heap.get` is
**total** (past the end it answers `default`, whose class is `BasicObject` — clink 45's "one
genuinely surprising cost"), so at a machine whose `self` is a *dangling* reference an
allocation changes what `self` is an instance of and a claim about the methods reachable from
`self` does not survive the push. Stated as an implication (`∀ o, self = .ref o → o < size`)
so an **immediate** `self` is admitted rather than excluded: `classOf` answers a boot id for
`.int`/`.sym`/`.nil`/booleans without reading the heap, and `1.instance_eval { … }` is a
machine the model can be in even though no rule types it.

### Half three: the interpreter's frame rule — stated, not proved

The continuation tail is frame too, by the same argument: `StateOk` does not describe it, so a
run must not depend on it. `KontFrame` states that and `EvalsDecompose` states the consequence
the compound rungs consume. This is the right factoring of the fifth stall point — **one**
named target for ~40 rules instead of forty arguments — and both are stated with the side
condition that is their content: `applyKont`/`unwind` at `kont = []` are the two pass-through
points, which are exactly the states at which a sub-run *ends*.

**Nothing takes either as a hypothesis and no rung is counted on them.** They are written down
so the target has a name; the measured cost and the one `partial def` blocking it are in
`Denote/Sem/notes.md`, and the proof belongs in `RubyCore/Proof/`.

### What this does and does not buy — stated, because two of three stalls are untouched

* **Ninth stall point: resolved on the conformance side.** What remains per rule is the
  forward walk (`startArgs`/`finishSend`/dispatch to the `NameError`, or to `reifyBlock`'s
  Proc) — and neither rule has argument expressions, so neither needs `KontFrame`.
* **Sixth stall point item (1): resolved.** Under exactness a stale declaration table makes
  `StateOk` **false** at the post-machine rather than unsatisfiable at the pre-machine. That is
  the honest failure and the one `Denote/Sanity.lean` can see.
* **Sixth stall point item (2): untouched.** `Judge.defStmt` concludes at the *incoming* `κ`
  and no component can make that true; the fix is `κ` threaded through `Judge`'s signature.
* **Fifth stall point: untouched.** Stating it as a frame rule does not reduce its proof.

### State

**178 rungs of 238**, **28 of 83 `Judge` rules** (unchanged — no rung climbed). Corpus
agreement unchanged at **238/238** (nothing under `Ratchet/` or `corpus/` touched), hand
derivations **177/177**, negative controls **144/144**, mismatches **35**, permanent negatives
**23**. `StateOk` grew from fourteen components to **seventeen** (`exact`, `nameFree`,
`selfLive`), and `Denote/Sanity.lean` still exhibits a model of all seventeen at the real
booted machine — an upper bound that did not cost vacuity, which was the risk. Modified:
`Denote/Sem/Frame.lean` (new), `Denote/Sem/State.lean` (`declaresName`, `MethodsExact`,
`shadowableNames`, `NameFreeOk`, `SelfLive`, `classOf_self_ext`, three `StateOk` fields and
both transports), `Denote/Sanity.lean` (`methodsExactB`, `nameFreeB`, `selfLiveB`,
`classPayload?_oob` and their soundness lemmas, `bootOkB`'s three new conjuncts),
`Denote/Rules.lean`, `Denote/Sem/notes.md`, `AGENTS.md`. Axiom-clean; no `sorry`;
`Denote/Examples.lean`'s 31 `#guard`s green; `bootOkB` green with seven clauses.

## Clink 52 (2026-09-02) — the two rules that reason from absence, and the spine that is a lookup. **178 rungs / 239, 30 of 83 rules**

Two rungs climbed — `Judge.bareName` and `Judge.lambdaLit`, which are the ninth stall point's
own two rules — one soundness bug found and fixed on the way (`found-issues.md` §F4), and one
definitional correction to the denotation that was a live **vacuity** rather than a hard rung
(the tenth stall point). Nothing under `Ratchet/` was touched except for the §F4 fix.

### What made these two reachable at all

Both are rules with **no argument expressions**, so no sub-run is ever evaluated under a
pushed continuation and the fifth stall point (`KontFrame`) is not on the path — which is why
the ninth stall point named exactly these two as "what remains is the forward walk". Their
proofs are the ladder's first *forward* walks: `evalExpr` → `startArgs` → `finishSend` →
`invoke` → `invokeDispatch` → `dispatchMiss`, rather than an inversion of a two-step run. That
made `Denote/Rules/Bare.lean` the first rung file to touch `Interp/Send.lean` and
`Interp/Reflect.lean`.

### `Judge.bareName`: the content is that the run does not return

The rule types a bare `x` as `.any` and threads `Γ` and `I` out **unchanged**, on the strength
of `NameError` being outside the type-stuck family. All three claims are vacuous *provided the
call really raises*, so the obligation is that its own hypothesis — `Evals m (.vcall "x") v m'`
— is unsatisfiable. Two pieces:

* **`Doomed` + `evals_doomed`** (`Denote/Rules/Bare.lean`): the inversion a non-returning rung
  uses in place of `evals_pure`. A `match` on `StepResult` rather than four lemmas, because the
  caller always arrives with a result in hand from a `split`. `Doomed_raiseErr` is the one arm
  with content: `raiseErr` leaves `kont` alone and `unwind` at `kont = []` is `.uncaught`.
* **The three fragment gates cost nothing**, and it is worth seeing why rather than
  discovering it: `crubySingletonShadow`/`crubyShadow`/`mixinShadow` each answer
  `.unsupported`, which is not a `.value` either, so they close by the same argument as the
  `NameError` branch.

Two `StateOk` components, and the decision in both is *where the escape goes*:

* **`BareNameFree`** — at top level, a name `κ.defs` does not record resolves nowhere on
  `self`'s chain. `NameFreeOk` (clink 51) is **not** enough, and the reason is its disjunction
  rather than its name list: it admits `md.builtin.isSome`, and a *builtin* named `x` would
  send `invokeDispatch` into `Builtins.run` — a call that returns a value and moves the heap.
* **`MissFree`** — no *user* `method_missing` is reachable from `self`.

Both are stated at **exactly the rule's own premises** (`defDeclared? κ.defs n = none`,
`κ.selfTy = none`, `nameFree κ "method_missing" = true`) rather than at `NameFreeOk`'s wider
`declaresName` escape. That was not forced and the alternative was tried first: `declaresName`
also reads `κ.classes`, about which `bareName` has no premise, so the wider escape hands the
rung nothing at a context where some class happens to declare an `x`. The cost is honest and
recorded: a top-level machine whose `self` can dispatch an unrecorded `x` is **not**
conformant, and that is precisely the machine at which the rule is wrong.

`MissFree` has **no `undefined` escape**, unlike `NameFreeOk`, and that is the sharpest
decision in the clink. `dispatchMiss` tests `mm.builtin.isNone` and nothing else, so an
`undef method_missing` tombstone with no builtin behind it really would be *entered* by this
interpreter. Stating the component at the interpreter's own test rather than at the sharper
test it could have made is the point: a component is a claim about what *this* machine does,
and inventing a check the machine does not perform would make the rung a proof about a
different interpreter.

### The bug the rung found: `found-issues.md` §F4

Asking "which other name has to be absent for the walk to reach the `NameError`?" is one line
of `dispatchMiss`, and the answer is `method_missing`. A user `Object#method_missing` makes the
miss **return** — and its body can rebind an ivar the rule threads out unchanged:

```ruby
@a = "s"
def method_missing(*n); @a = 1; 2; end
x
@a + "b"        # validate: String. CRuby and the model: TypeError, same message.
```

Fixed in the rule, the §F2 way: an `autoParam` premise `nameFree κ "method_missing" = true`, so
no derivation term moved; `Validate.lean` gains the conjunct and `Proof/ChkSound.lean` splits
the guard, so the checker is still *proved* to accept only what `Judge` derives. Pinned twice
(`corpus/239-method-missing-bare-name-unsafe` and a `CheckRungs` negative control, which
reports it as a **sound** rejection). The minimal form is a wrong *type* with no raise at all:
`def method_missing(n); @a = 1; 2; end; x; @a` is `NilClass` to the checker and `1` to both
executors.

### `Judge.lambdaLit`: the first higher-order conclusion

The value is a Proc and the type records what it captured. Three parts, one per conjunct of
`denM`'s `.clos` arm:

* `procClosure?` at the pushed object — `ext_push` again, at a `.proc` payload, so this is the
  third allocating rule and `CoreOk` grew `procBasic` exactly as that structure's docstring
  keeps predicting. No `procNamed`/`procSelf` twin: the conclusion is `.clos`, not
  `.cls "Proc"`.
* the captured spine — see below.
* `self` — and this is where `FrameInRange` had to grow a conjunct. `closSelf` reads the
  captured frame **by id** (`reifyBlock` captures `m.stack.headD 0`) while `SelfTyOk` reads
  `Machine.currentFrame`, which answers `default` at an empty stack while the captured id is
  `0` — a frame that may well exist. So the two readings agree exactly when the stack is
  non-empty. Clink 47's docstring already said "there *is* a current frame"; the inequality
  alone did not say it, and now the component does (`currentFrame_headD` is the bridge).

`nameFree` is spent against `NameFreeOk` here, which is the pairing clink 49 hoped for without
being able to state: the checker's premise and `finishSend`'s own `md.builtin.isNone &&
!md.undefined` test are the same question about two different things, and the component is what
identifies them. `nameFree_declaresName` is the one-line bridge (`find?`-shaped and
`any`-shaped negations of each other).

### The tenth stall point: `denSpine` walked entries, every consumer reads the first match

`denM`'s `.clos` arm asks for `denSpine (envToSpine Γ) m' (closLocal m' cl)`, and that is what
found it. `EnvOk` is stated at `envGet?` — **first** match — while `envToSpine` copies every
entry, and the two differ exactly at a duplicate key. The checker builds one **by design**:

```ruby
x = 1
f = lambda { |x| lambda { x } }
g = f.call("s")
g          # validate: <closure#1>{x: String, x: Integer} -- and it is right
```

`Judge.closCall` types a body in `paramEnv c.params argTys ++ spineToEnv cap`, parameters
first "so they shadow a captured name of the same spelling". So the old reading made
`Obl.Judge.lambdaLit` **false**, and — worse — made `EnvOk` false at any environment binding
such a `g`, i.e. `StateOk` *unsatisfiable* there. That is vacuity rather than falsity, the
failure mode `Denote/Sanity.lean` exists to police, and the third time (after the sixth and
eighth) that a component keyed differently from its lookup has produced it.

**The fix is `denSpineFrom seen`**: the accumulator carries the keys already bound and skips an
entry whose key is among them; `denSpine τ = denSpineFrom [] τ`. Two other shapes were
considered and dropped, both for the same reason, and the reason is proof shape rather than
taste:

* **`denSpine (dedup τ)` at the two call sites.** `dedup τ` is not a subterm of `τ`, so all
  four transports (`denM_heap_only_aux`, `denM_ctl`, `denM_ext`, `denM_setLocal`) would have
  become well-founded inductions on `sizeOf`.
* **the fully lookup-shaped `∀ x σ, ivarGet? τ x = some σ → denM σ m (g x)`.** Cleanest to
  read, and it makes the projection an identity — but the recursive call sits at a `σ` that
  comes from a *hypothesis* rather than a pattern, which breaks the mutual block's structural
  recursion, and every transport then needs an extra induction to recover "σ is a component of
  τ".

With the accumulator the recursion stays structural and each transport carries one extra
`∀ seen`. `denSpineFrom_get` gained an `x ∉ seen` side condition, which is exactly the
invariant the walk maintains (descending past an entry keyed `n` is `ivarGet?`'s `n ≠ x` case).
`denSpineB` got the same treatment (`denSpineBFrom`), because `closB_sound` and
`Examples.lean`'s guards have to keep lining up — and two new guards pin the new behaviour
against the real semantics: a shadowed entry is skipped, and a *wrong first* entry is not
rescued by a right second one.

### Definitions changed, and why each is a correction rather than a convenience

* **`denSpine` → `denSpineFrom seen`** (+ `denSpineB` → `denSpineBFrom`): the new reading is
  what the checker's own consumers mean; the old one was a strictly stronger demand no rule and
  no `Judge` premise ever made, and the machines that separated them were real programs.
* **`FrameInRange` gains `m.stack ≠ []`**: its docstring claimed it since clink 47.
* **`CoreOk.procBasic`**: one more boot fact, spent by `ext_push`.
* **`StateOk` gains `bareFree`/`missFree`**: seventeen components → **twenty**, and
  `Denote/Sanity.lean` still exhibits a model of all twenty at the real booted machine, so
  neither upper bound cost vacuity. `missFreeB` is checked in the component's own form
  (`none`, or a builtin behind it) rather than in the stronger "absent" form, because here the
  two are *not* interchangeable: `BasicObject#method_missing` is a real builtin, and demanding
  absence would have failed the guard.
* **`Judge.bareName` gains an `autoParam`** — the §F4 fix, the only change under `Ratchet/`.

### State

**178 rungs of 239** (one corpus rung added: the §F4 regression), **30 of 83 `Judge` rules**.
Corpus agreement **239/239, 0 disagreements** (the new rung included, CRuby vs the Lean
semantics), hand derivations **177/177**, negative controls **145/145** (one added),
mismatches **35**, permanent negatives **23**. `Denote/Examples.lean` is at **33** `#guard`s
and `bootOkB` at eight clauses, both green. Modified: `Denote/Rules/Bare.lean` (new),
`Denote/Rules/Lambda.lean` (new), `Denote/Den.lean`, `Denote/DenB.lean`, `Denote/Grow.lean`,
`Denote/Local.lean`, `Denote/Sem/State.lean`, `Denote/Rules/Core.lean`,
`Denote/Rules/Read.lean`, `Denote/Sanity.lean`, `Denote/Examples.lean`, `Denote/Rules.lean`,
`Ratchet/Judge.lean`, `Ratchet/Validate.lean`, `Ratchet/Proof/ChkSound.lean`,
`CheckRungs.lean`, `scripts/generate_corpus.py`, `corpus/239-*`, `found-issues.md`,
`Denote/Sem/notes.md`, `AGENTS.md`, and `../lean/RubyCore/Proof/KontFrame.lean` (new — the
first file this investigation adds *outside* `ratchet/`, because a theorem about `stepFn`
belongs next to `stepFn`). Axiom-clean; no `sorry`.

### The fifth stall point's named target is **false**, and here is the machine

Also this clink, and it changes the next attempt's plan rather than this one's number.
`KontFrame` (clink 51) says `stepFn` does not read below the head of `kont`. The measurement
behind it checked the **writers** — "grep `kont :=` finds thirteen sites, all `k :: m.kont`" —
which is the wrong half. There is one **reader**, and one is enough:

```
-- RubyCore/Interp/Reflect.lean, the "throw" arm
let matched := fun (tag : Value) =>
  m.kont.any fun k => match k with | .catchK t => t.identEq tag | _ => false
```

`not_KontFrame` (`Denote/Sem/Frame.lean`) exhibits it at the smallest machine that reaches the
dispatch: a value in flight, one `argsK` delivering it to an implicit-self `throw`, and an
**empty heap** so `lookup` misses and `dispatchMiss` reaches `tryReflect`. Under the empty tail
the step raises `UncaughtThrowError` *at the throw site* (deliberate — an enclosing `rescue`
must see it); under one `catchK` with the matching tag it jumps. Conditional on two `#guard`ed
`Bool`s rather than `decide`d, because `Interp.invoke` is well-founded-recursive and therefore
not `rfl`-reducible, and `native_decide` costs an axiom this package does not spend — the same
trade `Denote/Sanity.lean`'s `bootOkB` makes, for the same reason.

**`EvalsDecompose` is false too, and that half is sharper**, because it is *not* rescued by
"the sub-run must return": a sub-run can return under the empty continuation and not under `K`.

```ruby
catch(:t) do
  x = begin
        throw :t
      rescue UncaughtThrowError
        1
      end
  x + 1
end
```

**The repair costs the rungs nothing**: `CatchFree K` — the appended tail carries no `catchK` —
which is true by inspection at every kont a `Judge` rule pushes (they are literals), while a
`catch` *inside* the sub-expression pushes its marker **above** `K` where both sides see it
alike. `KontFrameCatchFree` is the corrected target and is what the compound rungs should be
written against.

Worth keeping as a working lesson: the target was written down as a named `Prop`-shaped `def`
rather than as a comment, which is the only reason it could be *attacked* instead of assumed.
A clink that had proved 40 rungs against it would have proved them against a falsehood.

### The eleventh stall point, and the map of what is left

Two more things were derived rather than met, and both are recorded in `Denote/Sem/notes.md`
because they are the next attempt's starting point:

* **A `def` is not an allocation.** Asking whether the sixth stall point's item (2) could be
  worked around inside `Denote/Sem/Judge.lean` (hand-editable) instead of in `Judge`'s
  signature (not, this clink) gets halfway: `SemJudge` *can* conclude at `κ.afterStmt e τ`, and
  `afterStmt` is definitionally the identity on every non-declaration expression, so no climbed
  rung would move. What stops `defStmt` anyway is a *transport*: installing a method changes a
  `classPayload?`, and both `Ext` and `Later` have a clause forbidding exactly that. Most
  components survive by inspection; the two that do not are the two that quantify over **runs**
  (`denM`'s arrow arms, `AsmsOk`) — and they honestly should not, since installing a method can
  change what calling a value returns. So the fix is §F1's shape (a declaration invalidates
  recorded claims about calls), not a coarser quantifier.
* **The wall map.** All 53 remaining rules, sorted by what actually blocks each one (5th: a
  sub-expression under a pushed continuation; 6th(2): a run that declares — which turns out to
  be *only* the five statement rules, since clink 49's `declFree` filter makes a declaring body
  uncallable and so every call rule's premise already implies its body declares nothing; 7th:
  `SemJudgeAll`'s snapshot; and a **call lemma** nobody has attempted, relating a premise about
  the body's run to the call's run and paying the frame-balance conjunct). The ninth was the last wall a clink could take down by *adding
  components*, which is what these two did. What is left needs a metatheorem about `stepFn` in
  `RubyCore/Proof/`, or a change to `Judge`'s signature and all 177 derivations, or a
  `SemJudgeAll` decision that wants the first call rung's requirements — which are behind the
  6th.

### The fifth wall, attacked: the `Builtins` layer is proved (and it was the cheap one)

`ratchet` cannot climb another rung without the fifth stall point, and the fifth stall point's
own notes said the **builtins** were the part nobody could size ("whether `invoke`'s descent
into `Builtins/` is `rfl`-transparent in `kont` *at kernel speed* is untested, and that is
where the 24k lines actually are"). So it was attacked rather than argued about:
`../lean/RubyCore/Proof/KontFrame.lean`, 51 theorems, axiom-clean, ~430 lines, ~3 s to build.

**The layer is framing-transparent by construction**: `grep -rn '\.kont\|kont :='` over the
whole `RubyCore/Builtins/` directory finds **zero** occurrences. What is proved: the fourteen
leaves (every one `rfl`), the two fuel walks (`putsGo`, `flattenAll`), the five `…Impl`
helpers, the `$~` layer (`matchFrameId`/`setLastMatchValue`/`setMatchGlobals`/`setLastMatch` —
the one write in the layer that is *not* to the heap, and the one that needed an induction
because the walk carries the machine as a captured argument), `runRegex`'s two match helpers,
and the allocating-fold family (`allocFold_frame` polymorphically, plus four concrete
instances because `simp` matches syntactically).

**The five dispatchers are stated, not proved, with the residual counted**: `runModules`
leaves 1 goal, `runStrings` 5, `runRegex` 17 — and every residual is either a machine-taking
`where` helper (`scanAll`, `splitBy`, `splitOn`, `subst`) or one more bespoke allocating fold.
Not a 24k-line risk; a few hundred more lines of the same shape.

Three tooling facts, each of which cost real time and none of which is in any manual:

* **`rw [f.eq_def]`, never `simp only [f]`** — the equation compiler refuses per-arm equations
  at interpreter scale ("failed to generate equational theorem for `runModules`").
* **`split` does not scale to deeply nested arms** — on `newImpl` (five nested `if`s over
  `ancestors` tests) `split`'s own `simp` reports "maximum number of steps exceeded", and
  neither `maxSteps` nor `simp.maxSteps` is a settable option. Hand case-splitting is ~15 lines
  per such function.
* **A general lemma is not enough where `simp` has to match syntactically** — `allocFold_frame`
  covers only the folds whose step really is a function of `(machine, element)`.

What this does *not* buy: a rung. `KontFrameCatchFree` needs the `Interp` layer too, and that
is the harder half — the statements there are **conditional** (`applyKont`/`unwind` at
`kont = []` are the two pass-through points), `CatchFree` has to be threaded through the
`throw` arm the refutation above found, and one `partial def` (`destructureBind`) has to be
given a structural recursion in `RubyCore` before anything about it is provable at all.

### What is still in the way, and why the number stops here

Of the 53 rules remaining, the attempted-and-reachable set is now **empty**: every one sits
behind the fifth, the sixth's item (2), or the seventh, and each of those is a clink-sized (or
larger) design decision rather than a proof a rung can carry. The sixth's fix in particular is
a change to `Ratchet/Judge.lean`'s *signature* — out of bounds under this clink's "do not
modify `Ratchet/`" constraint, and a rewrite of every derivation on file even without it.
