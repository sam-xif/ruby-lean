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
