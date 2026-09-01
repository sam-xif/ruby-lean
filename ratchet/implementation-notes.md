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
