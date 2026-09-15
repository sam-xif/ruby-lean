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

**The five dispatchers are stated, not proved, with the residual counted**: `runNumerics`
closes; `runModules` leaves 1 goal (its delegation to `runRegex`), `runCollections` 1,
`runStrings` 5, `runObjects` 12, `runRegex` 17 — and every residual is either a machine-taking
`where` helper (`runRegex.scanAll`/`splitBy`/`splitOn`/`subst`) or one more bespoke allocating
fold. Not a 24k-line risk; a few hundred more lines of the same shape.

Three tooling facts, each of which cost real time and none of which is in any manual:

* **`rw [f.eq_def]`, never `simp only [f]`** — the equation compiler refuses per-arm equations
  at interpreter scale ("failed to generate equational theorem for `runModules`").
* **`split` does not scale to deeply nested arms** — on `newImpl` (five nested `if`s over
  `ancestors` tests) `split`'s own `simp` reports "maximum number of steps exceeded", and
  neither `maxSteps` nor `simp.maxSteps` is a settable option. Hand case-splitting is ~15 lines
  per such function.
* **A general lemma is not enough where `simp` has to match syntactically** — `allocFold_frame`
  covers only the folds whose step really is a function of `(machine, element)`.
* **And the biggest multiplier: a fold lemma keyed on a lambda is invisible to `simp`.**
  `List.foldlM f (pushK K m) l` with `f` a lambda is rewritten by `rw` and not by
  `simp`/`simp_all` — the discrimination tree does not index under the lambda — so the
  contradictory cross-cases a `split` leaves behind do not close automatically even with the
  right lemma in the set. That is a `simp` fact, not an interpreter fact, and it is what makes
  the remaining Builtins work per-arm rather than per-file.

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

## Clink 53 (2026-09-02) — the seventh stall point, and three rungs that were never behind the wall. **178 rungs / 239, 33 of 83 rules**

Three rungs climbed — `JudgeAll.cons`, `JudgeKw.pair`, `JudgePairs.cons` — which completes
**six of the eight families** (`JudgeAll`, `JudgeKw`, `JudgePairs`, `JudgeRescues`,
`JudgeConsts`, `JudgeNested`). Nothing under `Ratchet/` touched.

### The finding, and it is a lesson about the ladder's own bookkeeping

All three were filed behind the **fifth** stall point — the continuation wall — and none of
them was ever behind it. `EvalsAll`'s `cons` arm reads

```
EvalsAll m (e :: es) (v :: vs) m' = ∃ m₁, Evals m e v m₁ ∧ EvalsAll m₁ es vs m'
```

so each element's run is an `Evals`: under an **empty** continuation, at successive machines.
A hypothesis of that shape *is* the two premises' hypotheses, and nothing has to relate a run
under a pushed `argsK` to a run under `[]`. **The companion families are compositional by
definition, so no companion rule ever needed the decomposition**; the wall belongs to their
*consumers* (`Judge.arrayLit`'s own run pushes `arrK` per element, `Judge.prim`'s pushes
`argsK`).

That is the same mistake, in the same direction, that clink 48 corrected for `JudgeSeq.last`,
and it has now cost rungs twice. The rule to carry forward: **before filing a rule behind the
wall, check whether its hypothesis is a compound run or a composition of `Evals`.** A `Judge.*`
rule's hypothesis is one run of one expression, so it is the compound case; a companion
family's is not.

### The seventh stall point, resolved — and which of its two candidates, and why

The real blocker was the seventh: `SemJudgeAll` concluded `DenAll τs m' vs`, every argument's
type at the machine the **whole list** left behind. That made this rung demand a transport of
`denM τ m₁ v` across the evaluation of every later argument, and no such transport exists —
`denM_ext`'s `Ext` wants a heap that only grew, and evaluating an arbitrary Ruby expression can
mutate an object in place.

The stall point recorded two candidate fixes. **The first was taken**: `DenAllAt` states each
element's type at *its own* post-machine, stepwise, which is what an argument list's evaluation
actually establishes. The second (a non-interference component on `StateOk`) was rejected, and
the reason is where the missing fact ends up: under `DenAllAt` a call rule that needs its
arguments' types at the *call* machine has to say so, so `PrimSig`'s no-mutator property — the
thing that makes the old form true today — becomes an explicit obligation at the consumer
instead of an invisible dependency at the producer. A non-interference component would have
buried it in `StateOk` for every rule to carry.

The intermediate machines are existential in `DenAllAt` rather than shared with `EvalsAll`'s,
and that costs nothing: `Interp.run` is a function, so the machine a returning run ends at is
determined by where it started.

### The second defect in the same family, also fixed

`SemJudgePairs` read a hash literal's pairs as `ps.map (·.1) ++ ps.map (·.2)` — **all keys,
then all values** — while `JudgePairs.cons` threads key, value, then the rest, which is Ruby's
order and the order `evalExpr`'s `.hash` arm performs. The two coincide at one pair and diverge
at two, so the obligation was stated over an evaluation the machine never performs. It is a
*hypothesis*, so the effect was vacuity rather than falsity — the rung looked unprovable and
`Judge.hashLit` would have had nothing usable to consume. `pairExprs` interleaves, matching
`kwExprs`' existing shape for keywords, and `DenPairsAt` is the stepwise per-element claim.

### What the rungs cost, once the definitions were right

Four lines each: destructure the value list (a length mismatch makes `EvalsAll` `False`), spend
the head premise at `m`, spend the tail premise at `m₁`, compose. `JudgePairs.cons` adds the
join's upper-bound property twice (`denM_joinT_left` for the head, `denPairsAt_mono` — one
induction over `denM_joinT_right` — for the tail, whose types are the join's right branch).
These are also the first rungs where the `m'.stack = m.stack` conjunct is **composed** rather
than read off a single step.

`Denote/Rules/Nil.lean`'s three base cases moved with the definitions and are stronger for it:
`DenAllAt m [] [] [] m'` is `m' = m` where the old conjunct was `True`, and `JudgePairs.nil` is
now `JudgeAll.nil`'s shape exactly instead of a `ks ++ vs = []` split.

### State

**178 rungs of 239**, **33 of 83 `Judge` rules**. Corpus agreement **239/239** (nothing under
`Ratchet/` or `corpus/` touched), hand derivations **177/177**, negative controls **145/145**,
mismatches **35**, permanent negatives **23**. `Denote/Examples.lean`'s 33 `#guard`s green,
`bootOkB` green. Modified: `Denote/Rules/Args.lean` (new), `Denote/Sem/Judge.lean`
(`DenAllAt`, `pairExprs`, `DenPairsAt`, and the three restated companions),
`Denote/Rules/Nil.lean`, `Denote/Rules.lean`, `Denote/Sem/notes.md`, `AGENTS.md`. Axiom-clean;
no `sorry`.

### And the fifth wall, further: `Interp/Support.lean` too

`../lean/RubyCore/Proof/KontFrame.lean` is at **105 theorems**, axiom-clean. Since clink 52 it
gained: the four continuation-taking `Builtins` helpers (`binArg`, `numBin`, `numCmp`,
`withIndex`) stated with the continuation's framing as a *hypothesis* rather than unfolded —
unfolding them across `runNumerics`' ~90 arms diverges at any recursion limit; `runRegex`'s six
`where` helpers; **five of the six dispatchers** (all but `runObjects`, which is at 13 goals,
eight of them the `Kernel#print` fold's contradictory cross-cases); and **all of
`Interp/Support.lean`**, `callClosure` — the first helper that pushes a *frame* — included.

Two of the five tooling facts recorded in `Denote/Sem/notes.md` are worth repeating here
because they are what actually moved the needle:

* **`simp_all` must be a per-goal last resort, not a stage in the `<;>` chain.** Run eagerly it
  re-folds goals that `rfl` would have closed. Demoting it closed `callClosure` and four
  dispatchers that had looked blocked — one lesson, four dispatchers.
* **A fold-framing lemma keyed on a lambda is invisible to `simp` and visible to `rw`**, and
  `rw`'s *conditional* form is the trick: it unifies the step out of the goal and leaves the
  framing hypothesis as a side goal, so a step and its per-declaration matcher constant never
  have to be written out. That is what closed `scanAll`/`splitBy`/`subst`, whose folds nest.

Also: a `macro_rules` tactic that mentions itself does not expand. The first higher-order
closer was recursive and silently failed on every nested case.

### The `partial def` on the wall's path, removed

`Interp/Support.lean`'s `destructureBind` was a **`partial def`**, which is worse than
expensive: a `partial def` compiles to an opaque constant with no equation lemmas, so *nothing*
about it is provable and the continuation-framing metatheorem was blocked **in principle**
(`Denote/Sem/notes.md` §The fifth stall point, item 3 — the trap `../AGENTS.md` L73 warns
about, arriving from the other side).

It now has a fuel-bounded recursion, which is the fix `ancestors` already took for the same
reason (`RubyCore/Heap.lean` L73 is `partial`-free on purpose). The fuel is `destrDepth subs +
1` — the nesting depth of `.destr` sub-params plus the level being bound — passed by both call
sites, so the `0` arm is unreachable and the behaviour is unchanged.

Two things worth recording about doing it:

* **`sizeOf` is not usable in executable code**: `destructureBind m subs dv (sizeOf subs)`
  fails to compile ("Failed to find LCNF signature for `List._sizeOf_inst`"), hence the
  hand-written `destrDepth`.
* **The off-by-one was caught by running it, not by reading it.** `destrDepth subs` alone gives
  fuel `0` at a one-level `def f((a, b), c)`, and the symptom is not an error but a **silent
  `nil` binding** — the model answered `NoMethodError: undefined method '+' for nil` where
  CRuby answers `6`. Verified after the fix against CRuby on `def f((a, b), c)` and
  `def g((a, (b, c)), *rest)`, plus the corpus agreement at 239/239 and `checkrungs` at
  177/177.

Its framing lemma is not written yet, and the honest status is that it is now *ordinary work*
— `KontFrame.lean` records the recipe that gets it to **three remaining goals**: zeta-only
reduction, the conditional `rw [foldPair_frame K]` at each of its three folds with the `.destr`
arm discharged by the fuel induction hypothesis, `Prod.ext` for the pair-valued arms, and
`congrArg Prod.fst/snd` where the pair has already been split. What is left is one fold whose
initial machine is a compound term and two `False` goals `simp_all` produces from arms it
over-reduces — the "`simp_all` must be a last resort" lesson again, one level in.

**And the model change is verified against the project's main gate**: the difftest suite at
tier 0 ran all **1304 bootstraptest cases with 0 disagreements** (992 agree, 306
`sut_unsupported`, 5 `control_invalid`, 1 harness error — the same shape as before the change),
on top of the corpus agreement at 239/239 and the two hand-checked destructuring programs.

### The fifth wall, third pass: `Interp/Dispatch` and the shape problem, named

`../lean/RubyCore/Proof/KontFrame.lean` is at **119 theorems**; the frame-pushing entries moved
to a second module (`KontFrameDispatch.lean`) so that iterating on them does not recompile the
first — `enterUserMethod` alone is `split`-bound on a 135-line body with ten branch points.

Proved this pass: **`destructureBind_frame`** (the item that was blocked *in principle*),
`eigenclassOf` and its fuel walk, `symOrStr`, `mixinShadow`, `moduleHook`, `missNoMethod`,
`visError?`, `cpathContainer`, `defineAttr`, `enterClassBody`, `enterScopedClassBody`.

**`destructureBind_frame` is the one worth reading**, because three plausible tactics failed
before the six-line proof:

* **`cases v`, not `split`, for the outer match.** Its catch-all *overlaps* the `.ref` arm, and
  `split` loses the negative hypothesis — leaving unprovable `⊢ False` side goals that look
  exactly like a false statement. Twenty minutes went into wondering whether the framing claim
  was wrong.
* **Deterministic, not a loop.** A `repeat' first | … | rw [foldPair_frame]` **spins**: the
  conditional rewrite keeps finding new occurrences in the side goals it just created. Two
  goals became 64, then 112. Two rewrites and their two named side goals close it.
* **`simp only []` for zeta *only*.** The body is a chain of `let`s, `rw` cannot reach under a
  binder, and the framing simp set goes too far: it turns `pushK K m` into a flat record
  literal, and then nothing whose left-hand side is `pushK K ?m` unifies.

That last one is **the shape problem**, and it now has a name and a diagnosis. The interpreter
builds machines by nested record update; Lean collapses those into one flat literal; so a
machine that *is* `pushK K m'` is spelled with `kont := k ++ K` inline, and the unifier will
not invent the structure field-wise to match it. Two things do not work: making `pushK`
`@[reducible]` (simp's discrimination tree still keys on the literal) and adding a `@[simp]`
lemma for the missing direction (simp then uses **structure eta** to expand every machine into
nine field projections, and a two-arm goal becomes ninety). What works is a *keyed* variant per
callee — `eigenclassOf_frame_mk`, whose left-hand side is `eigenclassOf` applied to a literal
— or a hand-written `show`, as `enterHandler_frame` uses.

And one more ordering lesson, in its sharpest form yet: **`frame_simp` has to run *before* the
`split`**, because otherwise `split` peels the pushed and unpushed matches *independently* and
pairs arm `i` of one with arm `j` of the other. The symptom is a goal comparing a `raiseErr`
against a `withKont` — which reads as a false statement and is nothing of the kind.

### What is left, corrected again

Fifty rules: `Judge`'s 47 and `JudgeSeq`'s 3. Every one of them has a **compound** hypothesis —
one run of one expression whose sub-expressions run under pushed continuations — so every one
is behind the fifth stall point, and the call rules are additionally behind the call lemma
nobody has written. The seventh is resolved; the sixth's item (2) reaches only the five
statement rules. So the wall map is now: **one wall**, and it is the one whose `Builtins` half
clink 52 proved.

## Clink 54 (2026-09-02) — the fifth wall, taken, and the call family opened. **178 rungs / 241, 38 of 83 rules**

The continuation wall — `Denote/Sem/notes.md` §The fifth stall point, the thing that has
gated "most compound rungs" since clink 48 and was refuted-then-repaired in clink 52 — is
**proved**, in `RubyCore/Proof/`, where that section said it belonged. Two theorems:

* **`RubyCore.Proof.stepFn_frame`** — the interpreter's frame rule, `KontFrameCatchFree`'s
  statement, over the *whole* of `stepFn`. Axiom-clean, and so is every lemma under it.
* **`Ratchet.Denote.run_split`** (`Denote/Sem/Decompose.lean`) — the run-level decomposition
  `EvalsDecompose` was stating: a run under an appended continuation `K` splits at the state
  that delivers the inner run's value to `K`.

`Denote/Sem/Frame.lean` keeps both `def`s as the statements of record, now pointing at the
proofs; nothing there was deleted, because what it records is *what the wall was*.

### The chain, and its real shape

The estimate in clink 50 was that the job is "a dependency chain of one-line lemmas over a
bounded helper set" rather than a line count proportional to the interpreter. That was right
about the shape and wrong about the price. What it took, file by file:

| file | what it needed |
|------|----------------|
| `Builtins` (24k lines) | done in clink 53 — 121 theorems, mostly `frame_simp`/`frame_arms` |
| `Interp/Support.lean` | done in clink 53 |
| `Interp/Dispatch.lean` | `enterUserMethod` (135 lines, the largest function in the model), the iterators, `include`/`prepend` |
| `Interp/Reflect.lean` | **`tryReflect` split into 16 named arms in the source** |
| `Interp/Send.lean` | `invoke` by induction on `args` (its own `termination_by`), plus twelve more |
| `Interp/Kont.lean` | `applyKont`/`unwind`, `cases k` over thirty continuation frames |
| `Interp.lean` | `evalExpr` (43 arms) and `stepFn` |
| `Proof/NotDone.lean` | the run **inversion**, which the estimate did not see at all |

### Six things that generalised, and are worth reusing

1. **`withCtl_mk`/`withKont_mk`/`mk_push`** — the shape problem's answer. A machine literal
   whose `kont` field is syntactically `k ++ K` *is* `pushK K` of the same literal, and saying
   so with the other eight fields as metavariables gives a **pattern** where `pushK K ?m` is
   not. `mk_push` is safe as a named `rw` and a **timeout** as a `simp` lemma (it ping-pongs
   against the framing set).
2. **The `_mk_cons` idiom** — one derived lemma per callee reached under a freshly consed
   continuation, each `rw [← List.cons_append]` from the general lemma.
3. **Generalise the machine-free scrutinees first.** On `enterUserMethod` this is the
   difference between a 40M-heartbeat timeout and forty seconds.
4. **A machine-carrying scrutinee must become a machine-free decision plus a machine.** This
   is the one lesson that changed the *source*, five times: `dmTarget?`/`dmTargetM`,
   `removeOk`/`removeRun`, `visOk`/`visRun`, `withSpread` (a combinator with the
   continuation's framing as a pointwise hypothesis), `classNewBlock`. `split` on a scrutinee
   that carries a machine pairs an `.ok`/`some` arm of one side with the `.error`/`none` arm of
   the other, and the resulting goals are contradictory only up to a conjunction it cannot use.
5. **The reverse-rewrite closer.** The goals `split` leaves are `withCtl m' c = pushK K
   (withCtl m c)` with `pushK K m = m'` in the context — which `simp_all` can only use left to
   right. Rewriting the *goal* backwards with the wrapper's own framing lemma puts the
   hypothesis's left-hand side into it. This is what took `invokeDispatch` from a wall of
   residual goals to none.
6. **Walk, close, and repeat.** `simp_all`+`subst_vars` *exposes* applications that were hidden
   behind an equation, and only the walker can rewrite those. Three rounds.

### The two facts the wall's own statement did not predict

**`unwind`'s `retJ` arm steps at an empty continuation.** The first version of `stepFn_frame`
assumed `stepFn m = .next m₂` was enough, on the reasoning that the excluded results are
exactly the ones that read an empty continuation as "the program is over". That is false: a
non-lambda block `return` whose home method has exited answers
`.next (raiseErr … "unexpected return")` at `kont = []`, where under a pushed `K` it unwinds
into `K`. So the side condition `Denote/Sem/notes.md` wrote down for `KontFrame` is needed
after all — for the `jump` arm, and only there.

**`.done` is constructed at one site, and that is a theorem.** `Proof/NotDone.lean`:
`StepResult.done` appears once in the interpreter (`applyKont`'s empty-continuation arm) and
`applyKont` is called from once place (`stepFn`), so

    stepFn m = .done v m' → m.ctl = .value v ∧ m.kont = [] ∧ m' = m

Without it the decomposition cannot be *stated* usefully — "the inner run stopped here" says
nothing about where *here* is, and the outer run cannot be continued from the corresponding
state. Forty-odd one-sided lemmas, and three tactic lessons: never put `isDone` in a simp set
(it unfolds into its matcher and destroys the head every callee's lemma is keyed on), never
`rfl` in the walker (it unfolds a WF-compiled function and burns the budget), and
`isDone_of_optNotDone (by assumption) (by simp)` for the `try*` family's callers.

### `JumpOpaque`, the third hypothesis

`run_split` needs one thing neither `Frame.lean` statement mentions: `K` cannot turn an
escaping jump into a returned value. `CatchFree` handles the `throw` counterexample
`Frame.lean` records; `JumpOpaque` handles the rest of the family (a `rescue` in `K` catching
what the sub-run raised, a `whileBodyK` swallowing a `break`). It holds by computation for the
literals a `Judge` rule pushes, on top of one general fact — **a jump at an empty continuation
never returns a value** — which is an induction rather than a computation, because `retJ` and
`throwJ` both step to a `raiseErr` that is itself a jump at the same empty continuation.

### The evalExpr measurement, because the strategy is the result

Running the full walker over `evalExpr`'s 43 arms costs **20 minutes and still times out** at
40M heartbeats. A **stage per named callee** — thirteen of them, no `split`, no `simp_all` —
closes it in 1m46s, and the theorem **depends on no axioms at all**. That is
`notes.md`'s own measurement holding up: the arms that do not delegate close on
`frame_simp; rfl`, and the residue is one goal per helper function. The 40M budget that
remains on it is for the **kernel**, not the tactic.

### Decisions that were not forced

* **The proofs live in `RubyCore/Proof/`, not `Denote/`.** `notes.md` argued for this and the
  alternative it named — a *typed-stack invariant* (`KontOk`) that avoids needing the frame
  rule at all — was reconsidered and rejected: the invariant technique proves preservation for
  a fixed program, while the ladder's obligations quantify over *arbitrary* sub-runs, which is
  what a frame rule is for. The two copies of `pushK`/`CatchFree` cost two `rfl`s
  (`Decompose.lean`'s bridge) and are worth it — `Frame.lean`'s statements are dated evidence.
* **`isDone` as a `Bool`, not a `Prop`.** The `∀ sr, o = some sr → …` form made every walker
  goal need an `at h` variant of `split`; a decidable predicate on the goal side needed none.
* **`destructureBind` de-`partial`ized rather than axiomatised.** (Clink 53's decision, priced
  here: it broke one existing proof, `T5.dispatch_progress`, which needed a heartbeat raise
  because unfolding `enterUserMethod` now walks fuel arithmetic.)

### The soundness finding

`found-issues.md` **§F5**: `Judge.vasgn` records the right-hand side's type verbatim, and if
that type is an alias (`Ty.sameAs y σ`) the rule claims `x` and `y` now hold the same value —
a claim about `y` that the premise does not carry, because `denM` gives `sameAs` no meaning as
an *expression* type. Unreachable through `chk` (whose `var` arm strips aliases and says so in
a comment), so there is no corpus counterexample to add; the fix is the invariant stated where
it is used, as `Judge.vasgn`'s `halias` premise plus the matching conjunct in both of
`Validate.lean`'s `vasgn .lvar` arms. Gate numbers unchanged.

### Definitions changed, and why

* `RubyCore/Interp/Reflect.lean` — `tryReflect`'s 390-line `match` became 16 named `def`s
  (right for the source independently of the proof: each family is now separately readable and
  separately provable, in seconds rather than a wall of 566 residual goals);
  `hasCatcher`, `blockClosure?`, `dmTarget?`/`dmTargetM`, `removeOk`/`removeRun`,
  `visOk`/`visRun` named for reason 4 above.
* `RubyCore/Interp/Kont.lean` — `withSpread` (the four `*splat` arms) and `isPrivateConst`.
* `RubyCore/Interp/Send.lean` — `classNewBlock`.
* All verified behaviour-preserving: **tier-0 difftest 1304 ran, 992 agree, 0 disagree** and
  **corpus agreement 239/239**, after each change.

### State

* `./scripts/run_ratchet.sh` — 178 rungs / 239, 35 `expect_validate` mismatches (unchanged),
  corpus agreement 239/239.
* `./scripts/run_check_rungs.sh` — 177/177 rungs confirmed, 145/145 negative controls.
* `lake exe semladder` — **38 of 83 rules**, all axiom-clean.
* `RubyCore/Proof/` — `lake build Metatheory` is clean but for the two pre-existing
  `Static/Iter.lean` errors (verified present with `Interp/{Support,Dispatch}.lean` reverted to
  before this clink's changes), and `T5.dispatch_progress` needed a heartbeat raise because
  unfolding `enterUserMethod` now walks `destrDepth`'s fuel arithmetic.

### After the wall: three more rungs, and the two definitional corrections they needed

**`Judge.vasgn`**, then **`Judge.callNever`** and **`Judge.primNever`** (the first two of the
call family), then **`Judge.constPath`**. Both conclude `Ty.never`, which is the empty type, so both are discharged by
contradicting the run: the argument walk finds the values the arguments delivered, the premise
says one of their types is `never`, and no value has that type. `primNever` is the first rung
to chain two `run_split`s (receiver, then one per argument) with a `.recvK` delivery stepped
through in between.

**`Denote/Sem/Send.lean`'s `run_args`** is the argument walk, and it is the call family's
backbone: `run_split` at each `.argsK`, with `catchFree_singleton`/`jumpOpaque_passthrough` as
the per-link ingredients (every one of these frames takes `unwind`'s default arm) and
`stepRunsTo_of_run` for "and the run continued" — which has to be phrased over
`Interp.run (f+1)` rather than over the `match` that unfolds to, because that matcher belongs
to `run`'s own declaration. Axiom-clean.

**`SemJudge` now carries `Plain`**, and that is a soundness correction rather than a
convenience. `Ratchet.Expr` has three shapes that are not expressions (`.splat`, `.kwargs`,
`.fwd` are argument-list syntax) and no `Judge` rule concludes about one — so a *syntactic*
`JudgeAll` derivation implies each argument is a real expression, structurally. `SemJudgeAll`
implied nothing of the kind: its `EvalsAll` hypothesis is unsatisfiable at a splat, so the
premise is **vacuous**, while `startArgs` routes the splat through `.argsSplatK` and the call's
run returns a value anyway. Every call rule's obligation was false for that reason.
Thirty-two of the 34 rungs discharge the new conjunct with `trivial`; `JudgeAll.cons` composes
its head's and its tail's, and `JudgeSeq.last` takes its statement's.

**`EnvOk` is complete** (a name the environment omits reads as `nil`) — `SelfSpineOk`'s second
conjunct one piece of state over, forced by `joinEnv`'s `.nilT` default. It strengthens
`StateOk`, which weakens all 83 obligations at once, and is taken for the reason
`SelfSpineOk`'s was: the completeness is the checker's own convention, and this is it stated
where the semantics can see it. `bootOkB` gains a `localsEmptyB` conjunct.

### One probe that came back negative, and is worth the line

`Judge.ivarAsgn` threads `Γ` out **unchanged** while writing an ivar, so a local holding `self`
(typed at `κ.selfTy`, an `.inst` with an ivar spine) would go stale exactly as §F1's `Ty.clos`
captures did — and `denM`'s `.inst` arm reads the object's ivars *at the current machine*, so
the obligation is false at such a `Γ`. Probed with a corpus element
(`corpus/240-ivar-asgn-stale-inst-unsafe`): the checker **rejects** the program, so it is
unreachable, and it joins §F5 and the eleventh stall point as a rule unsound in isolation whose
soundness in the checker rests on an unstated invariant. Left as a probe rather than fixed,
because the conservative premise it would need ("no `Γ` entry mentions the assigned ivar") has
real precision cost and the reachable set does not exercise it.

### And the rung it was for

**`Judge.vasgn`** (`Denote/Rules/Vasgn.lean`) — the first compound rung, and it reads like the
literals: peel the push (one `rfl`), `run_split`, apply the premise at the sub-run, invert the
two-step tail, and transport across the write with the machinery `vasgnAlias` already had.
That is the point of having paid for the wall.

One mundane lesson worth recording because it will recur at every compound rung: after
`run_two`'s `v = v₀` is substituted, **which of the two names survives is Lean's choice**, and
a proof that spells one of them out breaks when it picks the other. The ending is a separate
lemma (`vasgn_close`), parametric in the written value, and applies either way.

### And one component added on the way out

**`ConstPathsOk`** (`Denote/Sem/State.lean`): `ConstsOk` is about *lexical* resolution, which
is what the `Judge.const` family consumes; `Judge.constPath` asks about the **keyed** entry
`constKeyIn owner n` against what the interpreter finds inside the class named `owner`, and
nothing related the two. Its `setLocal` transport needs exactly `capStaleCtx`'s third
disjunct, which already covers `κ.consts` — so no `Ratchet/` change. `Denote/Rules/Path.lean`
**closes the rung**, and the technique that closed it is the one `Decompose.lean`'s `throwJ`
arm needed: `applyKont`'s arm builds its two conditions with `let`s and the resulting `if`s sit
inside the scrutinee of `run`'s five-arm match, so they have to be taken apart with
`cases … :` **in the hypothesis** — `split` in the goal picks the wrong match, and
`rw [if_pos …]` does not match the elaboration the source produced. Three outcomes, one fact
each: the hit is typed by `ConstPathsOk`, the `const_missing` gate is `.unsupported`, and the
miss-or-private path is a `raiseErr` — a jump at an empty continuation, which
`jump_empty_never_value` handles. The private case needs no machine-side conformance at all:
`PrivConstsOk` claims nothing, and a machine that hides the constant *raises*.

Its sibling **`constPathCls`** (the nested-class form) is the same three outcomes with one more
component: **`NestedClassesOk`**. `ClassesOk` says a class in the table has a name the machine
resolves *through the toplevel lookup at the full path* `"A::B"`; the rung needs the other
direction of the same fact — that looking `B` up **inside** `A` finds that class. Stated with
both lookups on the left, so it is a claim about agreement rather than an existence claim.

### What is next, and what it costs

`Judge.if'`/`ifNoElse` are next in constructor order and they are **not** behind the wall any
more — they are behind something else: **narrowing soundness**. Their branch premises are at
`narrowEnvs κ.classes c Γc` and `narrowSpine κ.classes c Ic`, so using them needs `StateOk` at
the *narrowed* environment, which is a fact about `refineOne` and `narrowCond?` that nothing on
file establishes: *if the run of `c` returned truthy, the tested local's value is in the
refined type*. `Denote/Sem/State.lean` L52 predicted this ("what a proof of `Judge.narrowEnvs`'
soundness will have to consume") and `EnvOk`'s identity conjunct was put there for it. It needs
the run of a concrete builtin dispatch (`x.is_a?(C)`) inverted, which is the same thing the
`callAsm` family will need, so it is not a detour.

## Clink 55 (2026-09-02) — three dispatch rungs, one new conjunct in the judgment, and §F7. **177 rungs / 243, 41 of 83 rules**

Three rungs, all in the same family: `Judge.isAQuery` (`recv.is_a?(C)`), `Judge.caseEqQuery`
(`C === v`, what `case v when C` desugars to) and `Judge.clsToS` (`C.to_s`). Each one is a
`Judge` rule whose run goes all the way through a **dispatch** — receiver, arguments, method
lookup, builtin — which is what clink 54's wall was blocking. All three are axiom-clean.

The interesting part is not the rungs. It is that the second one could not be proved from the
definitions on file, and what it needed was a **new conjunct in `SemJudge` itself**.

### The transport a send needs, and why no component could supply it

A send evaluates its receiver first, then its arguments, then dispatches. So a rule whose
receiver premise is `.clsOf cn` establishes "the receiver is *that* class object" at machine
`m₀`, and the dispatch **reads** the heap at `m₁` — with an arbitrary expression's evaluation
in between. `StateOk` cannot bridge that: it is a predicate on *one* machine, by design.

Three routes were considered and two rejected:

1. **A monotonicity theorem over `stepFn`** ("evaluation never unmakes a class"), in the shape
   of clink 54's frame lemma. Rejected on price: the property has to hold for every arm of
   `Builtins.run` — 24k lines, including hundreds of bids no rung will ever dispatch to — and
   it is not even unconditionally true as the model stands (`Modules.lean`'s four core
   `initialize` bids overwrite an existing object's payload without asking what it was, which
   is unreachable but not excluded).
2. **Restating the component to avoid the fact.** Measured and refuted: `===` resolves to
   `Module#===` at all 87 class objects but at only 44 of 87 arbitrary class ids — the other
   43 answer `Regexp#===`, a *prelude Ruby* `===`, or nothing at all. So the component cannot
   be indexed by the receiver's class the way `QueryOk` is; it has to be conditioned on the
   receiver *being a class object*, which is precisely the fact that needs transporting.
3. **A conjunct in the judgment.** Taken.

`SemJudge`'s first conjunct was `m'.stack = m.stack`. It is now `Framed m m'`, a two-field
structure: the same frame balance, plus **`cls` — once a class, always a class**. The trade is
the same one the `stack` conjunct already makes: the obligation is discharged *per rule*, so a
rule pays only for the bids it actually dispatches to, and a rule with sub-judgments composes
its premises' fields by `Framed.trans`. That composition **is** the transport — the argument
premise's own `Framed m₀ m₁` is what `caseEqQuery` applies to the receiver's class-ness — and
it arrives for free at every rule that does not allocate.

Retrofitting it cost less than the count suggested (65 sites named the old conjunct). Bundling
into a *structure* rather than adding a fourth conjunct kept the arity at three, so every
`obtain ⟨hst, hden, hok⟩` still typechecks and only the *uses* of `hst` as an equation had to
move. Four lemmas cover almost all of them: `Framed_reCtl`, `Framed_withCtl`,
`Framed_setLocal` and `Framed.of_ext` — the last because every allocating leaf rung already
builds an `Ext` for `StateOk_ext`, and an `Ext` pins `classPayload?` outright.

### The component, and the measurement that shaped it

**`ClsQueryOk`** (`Denote/Sem/State.lean`) is `QueryOk` at a **class-object** receiver: the same
five facts (the resolved method is the expected builtin, not undefined, public, not a prelude
twin, unshadowed) plus the same `method_missing` clause, but indexed by the object rather than
by its class, because `classOf` of a class object is its eigenclass. Two rows, both measured at
the booted machine before being written down: `("===", "Module#===")` and
`("to_s", "Module#to_s")`, each clean at all 87 class objects. Checked by one `Bool`
(`clsQueryOkB`) inside `bootOkB`, so the satisfiability witness still holds.

Conditioning it on the payload has a second benefit: a class payload pins its reference
**live** (`lt_size_of_classPayload` — past the end of the heap `Heap.get` answers `default`,
whose payload is `.none`), which is what `Ext` needs to transport the row.

### The soundness finding — §F7

Writing the component down forced the question `Judge.caseEqQuery`'s guard was ducking, and the
answer is a real hole. The guard is `smroGet? κ.classes cn "===" = none` — no singleton `===`
**on `cn` itself** — and the docstring defended dropping §F6's `isADispatchOk` on the grounds
that `Module#===` does not go through `obj.is_a?`. True, and beside the point: the dispatch
starts at `cn`'s *eigenclass* and walks its ancestors, so a `def self.===` on a **superclass**
is inherited, and a `class Module; def ===` replaces the builtin for every class in the
program. Both get past the guard, and both make the rule certify `bool` for a run that produces
a String. `Judge.clsToS` had the identical hole with `to_s`.

Fixed the §F6 way — `nameFree κ "===" `/`nameFree κ "to_s"` plus §F4's
`nameFree κ "method_missing"`, with the matching conjuncts in `Validate.lean` and the splits in
`ChkSound.lean`. Corpus 243 (`inherited-singleton-case-eq-unsafe`) pins the reachable shape and
validate now rejects it. The `class Module` shape is recorded in `found-issues.md` only: it
breaks the difftest **harness's own** JSON wrapper (`case` in `json/common.rb`), so it produces
no observation to compare — the one corpus candidate this ratchet has had to decline for that
reason, and worth remembering as a limit on what a corpus element can be.

### `Judge.classOf` (§F8), filed rather than climbed

Found while sizing the next rung. `Judge.classOf` types `x.class` as `.clsOf n` from a receiver
premise `.inst n I`. But `denM (.inst n I)` is an **is-a** test, which a `D < C` instance
passes at `n = "C"`, while `denM (.clsOf "C")` is `isClassRefNamed`, the *exact* class object.
So the rule is false of the denotation read on its own. Whether it is false of any *derivable*
judgment is a different question and probably no — `Judge` has no subsumption rule — which
makes it the same family as §F5 and probes 240–242. Recorded, not fixed.

### Tactic notes, both about large matches

* `Builtins.run`'s prologue asks **three** questions before any bid is looked at (the
  byte-string safety net, a zero-argument arity gate, the class-generic `dup`/`clone` rule). A
  `run_*` lemma has to answer all three; `run_isA` got away with folding the last two into a
  `simp only [zeroArgBids, dupBids, cloneBids]`, but at `Module#to_s` that `simp only` times out
  at `isDefEq` on the five-file bid chain.
* The fix generalises and is worth reusing: **state the descent as its own `rfl` lemma**.
  `runObjects_toS : runObjects "Module#to_s" … = runModules "Module#to_s" …` is `rfl`, because
  at a *literal* bid all five fallthrough matches reduce definitionally — the kernel does in one
  step what `simp only` was searching for. Same for the arm itself
  (`runModules_toS`). `run_clsToS` is then three `split`s and a payload case.

### State

`lake build` clean; no `sorry`, no new axioms. Corpus 243/243 agreement, 0 disagreements;
`expect_validate` mismatches 35 (unchanged — both new probes are rejected as intended);
`checkrungs` 177/177 + 145/145; the denotation gate's `#guard`s green; ladder **41/83**. No
change under `lean/` this clink, so the tier-0 difftest from clink 54 still stands.

### What is next

`Judge.if'`/`ifNoElse` remain where clink 54 left them: behind **narrowing soundness**, which
needs the run of `x.is_a?(C)` *inverted* rather than replayed — and that is now a smaller step
than it was, because `Denote/Sem/Query.lean`'s chain is exactly the forward direction of the
inversion. The other open front is unchanged and is model coverage, not proof: `Judge.prim` and
`Judge.callAsm` need `PrimSig`'s 222 rows to agree with `Builtins.run`, and each row needs both
a dispatch fact (which class binds the name to which bid — receiver-dependent, so not a single
`nameFree` row) and a result fact.

## Clink 56 (2026-09-02) — three reachable soundness bugs, and the denotation's nominal arms split. **177 rungs / 247, 42 of 83 rules**

One rung (`Judge.classOf`), four findings, and the findings are the content. Three of them are
programs `validate` **accepted** and CRuby raises `TypeError` on — the first time this ladder
has produced that, and all three came out of the same activity: writing down what an obligation
would have to assume, then writing the program that breaks the assumption.

### The route, because it is repeatable

`Denote/Sem/notes.md`'s twelfth stall point lists six type-level lemmas as narrowing's cheap
end: "the refined type still denotes the value". Four went through in an afternoon
(`Denote/Sem/Narrow.lean` — `truthyTy`, `falsyTy`, `isNilTy`, `nonNilTy`, axiom-clean). The
other two are `isATy`/`notATy`, and they cannot be stated without saying what makes
`isAAnswer`'s answers *true of the heap*. Every finding below is a step in writing that
sentence:

* "the static chain is the machine's chain" → **§F9**: it is not, if a program `include`s a
  module into a core class.
* "…at the class the name resolves to" → **§F10**: the name need not resolve to that class;
  `Foo = Integer` is a constant alias and narrowing read the *name*.
* "…and the value's class is the one the type names" → **§F11** (`rescue` binds a subclass, and
  `PrimSig` dispatches on the supertype) and **§F12** (the `.inst` arm should never have been
  is-a at all).

Two of the four lemmas also needed `Ratchet/Ty.lean` fixed before they were true, and both
fixes are in the same direction: **a `.never` catch-all is a claim, not a default.**
`falsyTy`/`isNilTy` answered `.never` — "this branch cannot run" — for the alias arm (an alias
denotes its payload, so `.sameAs y .nilT` has a falsy value) and for the nominal arms (`nil` and
`false` descend from `Object`, `Kernel`, `BasicObject`, so `falsyTy (.cls "Object") = .never`
claims a branch unreachable that a `nil` reaches). They now refine under the alias and decline
to refine nominally.

### §F9 and §F10 — a wrong `some false`, and why it certifies *anything*

`isATy` turns `isAAnswer`'s `some false` into `Ty.never`. `never` makes everything downstream
vacuous, so a wrong negative answer does not mistype the branch — it certifies whatever is in
it. That is what makes these two worse than an ordinary imprecision, and it is why both
programs are three lines:

```ruby
module M; end
class Integer; include M; end      # §F9: 5.is_a?(M) is now true
Foo = Integer                      # §F10: 5.is_a?(Foo) is true, and "Foo" is in no chain
```

Fixes: `mixinFreeChain C ch` (a negative answer requires that the context reopens no class
*named in the chain* with an `include`/`prepend`; the positive answer is unchanged, since a
mixin only adds ancestors) and `narrowNameOk κ` (the `.isA` shapes require
`constGet? κ cn = none`, the same condition `Judge.constCls` carries for constant *reads*).
`narrowEnvs`/`narrowSpine` now take the whole `Ctx`, because the constant table is not in the
class table.

`Judge.lean`'s own comment above `rootAncestors` predicted §F9 exactly — "whichever tier gives
`include` a rule must revisit `isAAnswer`" — and the revisit had covered the declared chain and
not the builtin one. Worth remembering as a pattern: a comment that names a future obligation
is a to-do the ratchet will eventually collect on.

### §F11 — `rescue` is the one place the judgment uses subsumption

```ruby
class E < StandardError; def message; 5; end; end
begin; raise E; rescue StandardError => e; e.message + "s"; end
```

`Ty.cls n` denotes is-a *by design*, and `rescueBind?` is why: Ruby binds whatever was raised.
But every rule that **dispatches** on a nominal type looks the method up in `n`'s own table, and
`PrimSig`'s `excMessage` row is where the target's own code makes the call. `Judge.prim` gained
`primDispatchOk κ.classes σ m` — at a `.cls n` receiver, no declared class may descend from `n`
and redefine `m`.

The interesting part is the **exemption**. `valueClsNames` (`String`, `Hash`, `Regexp`,
`MatchData` — the only four `.cls` names the judgment mentions) is unguarded, because
`constLibTy?_sound`-style unconditionality has to be preserved: `constLitTy?_sound` types
`"s".freeze` in *any* context, so a premise it cannot discharge would land on callers
(`Ctx.afterStmt`'s class-body constants, `paramEnv`'s optional defaults) that have no class
table to check. `constLitTy?_primDispatchOk` is the companion lemma that makes the exemption a
proof rather than an assertion.

### §F12 — and the definitional fix, which is the session's real result

`denM (.inst n I)` was `isAName` — is-a. But every rule with an `.inst n` receiver premise types
the callee's body out of **`n`'s own table**, and `Judge.classOf` concludes the *exact* class
object, so under an is-a reading all of those obligations are false with one counterexample (a
`D < C` that redefines the method). §F8 filed that as a curiosity about one rule; it is the
central obstacle to the whole dispatch family.

Is-a is not what the judgment means by `.inst`. `Judge` produces one only by allocating exactly
`n` or from a `self` whose class is `κ.frame.recvClass` — which `superCall`/`zsuperCall` thread
*exactly*, `defClass` being the field they change — and `joinT` of two `.inst`s is a union, not
an upcast. So `isExactInst` is the reading, `Ty.cls` keeps is-a for `rescue`, and the asymmetry
between the two nominal arms is now deliberate and documented.

Two details in `isExactInst` are load-bearing and both were found by a failing proof:
`realClassOf` rather than `classOf` (the latter answers the *eigenclass*, so any object with a
`def obj.foo` would stop having its type), and a **liveness** test (`Heap.get` is total, so a
dangling reference reads as class `0` — which the is-a reading survives, `0` being an ancestor
of everything, and the exact reading would not; `Ext.isExactInst_mono` is false without it).

It cost four sites — `denM`, `denB`'s mirror, `Grow.lean`'s monotonicity, one `Ext` lemma — and
**nothing else moved**: 41 rungs, 33 `Examples.lean` `#guard`s, 177 hand derivations, 145
negative controls all unaffected. The guards are the interesting witness there: they check real
programs, where instances are exact.

### The rung

`Judge.classOf` (`Denote/Rules/ClassOf.lean`), 42/83. Short, because `Object#class` answers
`realClassOf` and `isExactInst` *is* `realClassOf` composed with `classNamed?` — the two ends
meet definitionally. Its two new `nameFree` premises are a different species from §F6's and
worth the line: `class` is a Ruby keyword, so no *program* can override it, which is what the
rule's docstring relied on — but `κ` is a data structure and the judgment quantifies over all
of them, so the rule was asking the grammar to imply something about `Judge` that `Judge` does
not enforce. Both discharge by `rfl` at every real context.

`ClsQueryOk`/`QueryOk` grew two rows (`class`, and `to_s`/`===` in clink 55), each measured at
the booted machine first. The measurement is now a habit worth naming: *ask both indexings*.
`is_a?` and `class` are clean at all 105 class ids, so they belong in `QueryOk`; `===` and
`to_s` fail at 43 and 63 of them but are clean at all 87 *class objects*, so they belong in
`ClsQueryOk`.

### State

`lake build` clean; no `sorry`, no new axioms. Corpus **247/247** agreement, 0 disagreements;
`expect_validate` mismatches **35** (unchanged through all four fixes — every one of them was
precision-preserving on the corpus); `checkrungs` 177/177 + 145/145; denotation guards green;
ladder **42/83**. No change under `lean/` in clinks 55–56, so the tier-0 difftest from clink 54
still stands.

### What is next, and one more finding to spend first

Narrowing's remaining piece is `denM_isATy`/`denM_notATy`, and after §F12 the `.inst` case is
fine — the `.cls n` case is what is left, needing §F9's guard extended from "the chain's own
classes" to "the declared classes below `n`". That is a checker change of the same shape and
the natural next step.

The call family is unblocked at the `.inst` level and blocked at another: **`SemJudge` is too
weak to be an interface for a rule whose premise is a *body*.** `Judge.callMethod`'s obligation
takes `SemJudge κ' Γb d.body ρ …`, and for `d.body = return "s"` that holds **vacuously** — the
run jumps, so `Evals` is never satisfied — while the machine really runs the body and the call
really returns a String. The syntactic judgment is safe because `.ret`/`.brk`/`.nxt` have no
rules at all (`bodyResult` handles the one lambda shape outside the judgment), so the fix is
the `Plain` precedent one more time: a **jump-freeness** conjunct, which `Judge` implies
structurally and `SemJudge` does not. Same species of finding as clink 54's `Plain`, and it has
to land before any call rung.

## Clink 57 (2026-09-02) — narrowing's six lemmas, two more rungs, and the wall the ladder actually has. **177 rungs / 248, 43 of 83 rules**

Two rungs (`Judge.clsToS` was clink 56's; this clink's are `Judge.newInstNoInit` and the
completion of narrowing's type-level half), one more soundness finding, and — the reason to
read this entry — the **remaining ladder now has a single named wall** instead of a list of
stall points.

### `Judge.newInstNoInit`: the allocator, and a fifth missing premise

`C.new` for a class with no `initialize`. The first rung that allocates through a class the
*program* declared rather than through a literal, and three things it needed are each worth a
line:

* **The dispatch cannot be a `ClsQueryOk` row.** `===`/`to_s` are clean at all 87 boot class
  objects; `new` is not — 16 of them do not resolve it to `Class#new` (14 modules, plus `Range`
  and `Struct`, whose `new` is prelude Ruby). So the fact is keyed on the *context's* table:
  **`DeclClassOk`**, quantified over `κ.classes` and therefore vacuous at `ctx0`, exactly as
  `ClassesOk`/`DefsOk` are. Five clauses, one per thing `Class#new` reads on the way to an
  object, and the two that are easy to miss are "the chain reaches `BasicObject`" (`ext_push`
  asks for it and nothing else said it) and "the class object is not `Class`, not `Module`, not
  a module" — those being the `newImpl` arms that answer with a **class**, and an allocation
  that adds a class is not an `Ext`.
* **The rule was missing the allocator's own premise.** A declared `def self.new` **wins** over
  `Class#new` in CRuby, and `invoke`'s `userNew` check honours that, so
  `smroGet? κ.classes n "new" = none` has to be *stated*. `validate` consulted `smroGet?`
  before the allocator anyway, so no derivation on file changed — the fourth time this clink
  pair has found a premise the checker supplied by accident of control flow (§F6, §F7, §F11,
  and `classOf`'s `nameFree`).
* **`newImpl` has eleven arms and five allocate**, stated as one disjunction: either a fresh
  object with `k` as its class, no ivars, no eigenclass and a non-class payload — exactly
  `ext_push`'s hypotheses — or a gate. The uniformity is real: Exception/String/Array/Hash
  subclasses each start with *that* class's empty payload so a later `super` can fill it, and
  all four keep `k` as `klass`, which is all the conclusion reads.

### Narrowing's type-level half, complete — and what finishing it cost

All six lemmas the twelfth stall point named (`truthyTy`, `falsyTy`, `isNilTy`, `nonNilTy`,
`isATy`, `notATy`), axiom-clean, in `Denote/Sem/Narrow.lean`. The first four are facts about
`Ty` alone. The last two answer from `isAAnswer`, a **static table**, while the branch's
justification is the machine's own ancestor walk — and every guard below was forced by trying
to write that sentence down:

* **`coreConstFree κ`** (§F10, chain-side). The per-name guard covers the name being *tested*;
  it does not cover the names the chain is *written in*. `Comparable = Integer` makes `String`'s
  own chain mean something else.
* **`isAAnswer`'s positive answer is gated too.** It would survive on its own — a mixin only
  adds ancestors, a subclass keeps them — and an earlier version of the guard kept it. It is
  gated because proving that half without the no-subclasses clause needs **transitivity of the
  ancestor walk**, a general fact about `ancestors` that nothing on file proves and that a
  `StateOk` component has no business assuming. Worth recording as a *choice*: the alternative
  is a real theorem, and if a later rung wants the precision back that theorem is the price.
* **`BaseChainsOk`'s clauses are split by which guard they need** — the clauses about a chain's
  own names need only `coreConstFree`; the clauses about what is **not** an ancestor need
  `isANoOk` and, for the tested name, `constGet? = none`. That split *is* the finding.
* **`isExactInst` gained a third conjunct, no eigenclass.** With a singleton class `isA` walks
  the eigenclass chain, so `obj.extend M` makes `obj.is_a?(M)` true while `M` is in no declared
  chain, and the `.inst` lemma needs "the value's ancestors are its class's ancestors"
  exactly. A rule concluding `.inst` allocates a fresh object, which has none.

`Ratchet/Ty.lean`'s `builtinAncestors` also **lost its `.arrayOf`/`.hashOf` rows**, and the
reason is a denotation fact rather than a table gap: those arms read the *payload*
(`arrElems?`/`hshEntries?`) and say nothing about the object's class, so a negative `is_a?`
answer about them is a claim the judgment cannot make. Dropping them costs precision in one
direction only, because a positive answer keeps the type just as `none` does.

### §F13, and the wall

`Judge.if'`/`ifNoElse` are **still not climbed**, and the reason is now precise. `narrowCond?`'s
`&&` arm licenses a then-branch refinement when the right-hand side passes `noLocalAsgn` — a
*syntactic* "assigns no local". What the refinement needs is that evaluating the right-hand
side cannot **rebind** the local, and `f.call` on a closure that assigns is the gap
(`found-issues.md` §F13, corpus 248 as a control — `validate` rejects it today for an
unrelated reason). Even the strongest sound guard, `κ.closures = []`, only makes the claim
*true*; discharging it needs "a run of a `noLocalAsgn` expression at a closure-free machine
leaves the frame's locals alone" — a property of the **run** derived from a property of the
**syntax**.

Which is the same shape as the fourteenth stall point (a `Judge`-derivable expression contains
no `.ret`, therefore its run emits no return jump — needed by every call rule). So they are one
thing, and `Denote/Sem/notes.md` now records it as the **fifteenth stall point: syntax-directed
run invariants** — one induction over `stepFn` carrying a syntactic predicate through the
machine, of the same *kind* and size as the frame layer, and cheaper in two ways (these are
invariants rather than equations, so `simp` closes more arms; and `Builtins` is transparent to
both, needing one lemma rather than 121).

**That is the honest shape of the remaining ladder**: 43 of 83 discharged, ~17 behind this one
wall, and the declaration family behind the judgment redesign its own stall point describes.
The list of four walls clink 54 left has become two.

### State

`lake build` clean; no `sorry`, no new axioms. Corpus **248/248** agreement, 0 disagreements;
`expect_validate` mismatches **35**, unchanged through every guard in this clink and the last —
worth noting explicitly, because five of the eight changes tightened the checker and none of
them cost a rung. `checkrungs` 177/177 + 145/145; denotation guards green; ladder **43/83**.
No change under `lean/` in clinks 55–57, so the tier-0 difftest from clink 54 still stands.

## Clink 58 (2026-09-02) — the narrowing layer, two guard rungs, and three more findings. **177 rungs / 249, 46 of 83 rules**

Four rungs (`Judge.raiseCls`, `JudgeSeq.nextGuard`, `JudgeSeq.guard`, and clink 57's
`newInstNoInit`), the whole of narrowing soundness built out, and three findings — one of them
a program `validate` accepted. The headline number moved 43 → 46; the more useful output is
that the *remaining* ladder is now one interconnected layer plus one judgment redesign, and
both are sized.

### `Judge.raiseCls`, and a rung I had mis-filed

`raise C` / `raise C, "msg"` concludes `Ty.never`, so it belongs to the family `callNever`
opened — discharge by *contradicting the run*. I had filed it behind the frame-push wall
because of the `raiseNewK` interception, and that was wrong.

`raise C` where `C` has a user `initialize` cannot be finished by a builtin (CRuby builds the
exception with `C.new(…)`, so the initializer must run), so `Interp/Send.lean` allocates the
instance, pushes `.raiseNewK inst` and enters the method — and a value **does** come back, from
an arbitrary user body. It still cannot escape: `applyKont` at `.raiseNewK` turns any arriving
value into `.jump (.raiseJ inst)`. So the kont is *value-opaque*, and with `run_split` that
covers the whole activation **without looking at the body**.

Two techniques from it are reusable:

* **`pushK_of_kont_append`** — a machine whose continuation *ends* with `Kout` is a `pushK` of
  one that does not. The `raiseNewK` machine comes out of `enterUserMethod` (frame pushed,
  parameters folded in, `ctl` set); writing it down to feed `pushK` would transcribe the
  definition, so read it off the continuation instead.
* **`RubyCore.Proof.enterUserMethod_frame` is an equation**, not an implication, so the
  activation needs no shape lemma at all: entering a method under an appended continuation *is*
  entering it and appending. Clink 54's frame layer paying off in a rung that is not about
  frames.

The lesson worth generalising: **re-audit the filing.** A rule whose conclusion makes the run's
value irrelevant (`.never`, or a path that jumps) may be reachable even when its *machinery*
looks like it belongs to a blocked family.

### Narrowing, built out — and it is the guards that land, not `if'`

All six type-level lemmas were clink 57's. This clink adds the run half and the state half:

* three **inversions** (`nilq_inv`, `isaq_inv`, `caseeq_inv`) over two shared skeletons
  (`send_zeroarg_inv`, `send_const_arg_inv`, `send_const_recv_inv`), parameterised over the
  variable kind since `.lvar` and `.ivar` differ only in which step lemma fires;
* two **transports** (`EnvOk_refineOne_else`, `SelfSpineOk_ivarSet`), the first stated
  *pointwise* — which is what makes `refineOne`'s alias arm free, since `EnvOk`'s own conjunct
  says an alias and its target hold the same value;
* `narrow_else_fact`, the branch's fact for **every** shape in one conclusion, with the shape
  analysis done once by `split` on the recogniser's own match;
* `stateOk_narrow_else`, the assembly.

And then the two rungs it buys are `JudgeSeq.guard` and `JudgeSeq.nextGuard` — **not**
`Judge.if'`/`ifNoElse`. The reason is worth stating because it is a design fact about guard
clauses: a guard's then-branch is `next` or `return e`, both of which **escape** (`.nxt` emits
a `nxtJ` that neither `ifK` nor `seqK` consumes; `doReturn` answers a jump whatever happens).
So the run never returns a value on that path, the then-premise is never spent, and only
`narrowEnvs`'s *else* component is read — where the `&&` shape refines nothing and
`found-issues.md` §F13's wall does not bite.

### Three findings

* **§F14** (reachable, `validate` accepted it): `class NilClass; def nil?; false; end; end`
  sends a `nil` down the **else** branch of `if x.nil?`, where `nonNilTy .nilT` is `.never` —
  so everything in that branch is certified, and it runs `nil + 1`. `Judge.nilQuery` guards its
  own *typing* of `x.nil?` with `NilQSafe`, which is about the receiver's **shape**; the
  narrowing needs the **name**, and `nameFree κ "nil?"` is that.
* **§F15** (found by a lemma that turned out false): `falsyTy (union (sameAs y ρ) int)` *is* the
  `sameAs`, because `joinT` returns its non-`never` argument. So refining a binding the
  environment describes as a **union** records an alias claim — "these two locals hold the same
  object" — that the union never made. `refineOne` now declines to refine when the result would
  be an alias, in both arms.
* **§F16**: `narrowCond?` recognises `C === x` and refines by `.isA cn`, which is only the right
  reading if `C` **is** a class — `Module#===` is the ancestor test, `String#===` is equality.
  `validate` cannot build such a derivation today, and the protection is three separate
  accidents; none of them is a premise, and the *semantic* premise for a condition carries no
  typing at all.

The three together, with §F10 and §F14, are one pattern stated five ways: **a narrowing reads
syntax, so every fact it relies on about what that syntax means has to be a premise** — the
tested name must be unclaimed (§F14), must not be rebound (§F10), must name a class (§F16), and
the types involved must not be manufactured into claims the environment never made (§F15).
`narrowNameOk` is now six conjuncts, and each one is a program that used to be certified.

### Decisions not forced, and the alternatives rejected

* **`nil?` got its own component** (`NilQueryOk`) rather than a row in `queryBuiltins`, because
  it is the one query name resolving to **two** bids (`NilClass#nil?` at `NilClass`,
  `Object#nil?` elsewhere) and `QueryOk` pairs a name with one bid — two rows would claim each
  of every class, which is a contradiction rather than a weakening. The alternative, making
  `queryBuiltins` a name→*list* table, would have touched the three working query rungs; a
  local component touched nothing.
* **`isAAnswer`'s positive answer is now gated too.** It would survive ungated — a mixin only
  adds ancestors and a subclass keeps them — but proving that half needs **transitivity of the
  ancestor walk**, which nothing on file proves and which a `StateOk` component has no business
  assuming. Gating buys exactness instead. If a rung ever wants the precision back, that
  theorem is the price, and it is written down here so the trade is visible.
* **Removing the `&&` narrowing was tried and rejected**, twice over: `validate`'s verdicts do
  not move, but rung 132's hand derivation stops type-checking (its `x + 1` needs the narrowed
  `Integer`), so `checkrungs` would read 176/177. The feature is load-bearing; §F13's fix has
  to be the guard *plus* the invariant.

### What is left, and why it is one piece

Measured while looking for a cheaper route to `if'`: the fifteenth stall point's two halves are
**entangled with the call decomposition**, so they cannot be sequenced. The locals claim wants
to be an induction on the expression — `noLocalAsgn`'s grammar is small — but its `.send` arm
(which the feature requires) may dispatch a *user method*, whose run pushes a frame and runs an
arbitrary body. So it needs "a callee's run leaves the caller's frame's locals alone", which is
a statement about the activation between a `frameK` push and its pop: the same decomposition
the call family needs, and the one that needs jump-freeness to even state.

So the honest shape of the remainder is **two** items, not five:

1. **One layer**: `frameK`-decomposition + jump-freeness + the two syntactic invariants, built
   together. It gates `if'`/`ifNoElse` (2), the call family (~21), `while'`, `begin'`, and —
   through the argument transport those need — `arrayLit`/`hashLit`. There is no useful smaller
   first step, which is worth knowing before starting.
2. **One judgment redesign**: the declaration family (`defStmt`, `classStmt`, `moduleStmt`,
   `casgn`, `cpathAsgn`, `JudgeSeq.cons`). `StateOk` is **anti-monotone in `κ`** — `MethodsExact`
   and `NameFreeOk` are upper bounds — so a rule that *grows* the context cannot have its
   obligation stated at the old `κ`, and `Judge`'s conclusion has no outgoing context. This one
   really is a change to the judgment's shape rather than an additive layer.

`Judge.prim`'s ~200 `PrimSig` rows and `AsmsOk`'s frame-shape mismatch are the two remaining
items outside both.

### State

`lake build` clean; no `sorry`, no new axioms. Corpus **249/249** agreement, 0 disagreements;
`expect_validate` mismatches **35**, unchanged across all nine checker changes in clinks 55–58 —
every one of them tightened a guard and none cost a rung. `checkrungs` 177/177 + 145/145; the
denotation gate's `#guard`s green; ladder **46/83**. No change under `lean/` since clink 54, so
that clink's tier-0 difftest (1304 cases, 0 disagreements) still stands.

## Clink 59 (2026-09-02) — mutation enters the ladder, two reachable soundness bugs, and the layer's plan corrected. **177 rungs / 250, 47 of 83 rules**

One rung, and it is the one that pays for a whole class of the remaining ones:
`Judge.ivarAsgn`. Every transport the ladder had before this was `Ext` (allocation: the heap
grows, old ids read back identically) or `setLocal` (a rebinding: the heap is untouched).
`@x = e` is neither, and `Ext` is *false* of it — `Ext.get` promises every old id reads back
identically, which is exactly what the write breaks.

### `Mut`, and why it is a third relation and not a widening

`Denote/Sem/Mut.lean` is the relation for a step that mutates an object already in the heap:
frames, stack, globals and heap **size** are pinned, and so is every heap field the *shape*
reads — `klass`, `eigen`, `payload`, `frozen`. What is not pinned is `ivars`, and that is the
whole of it.

Three relations rather than two, and the split is forced the same way `Ext`/`Later`'s was:
`Ext` **grows** the heap and `Mut` does not, so neither implies the other and their common
part is a shape interface that `Ext` satisfies only *in range*. Factoring that interface out
of both would have obliged every existing `Ext` caller to supply the out-of-range clauses. The
nine `StateOk` components that read only the heap's shape therefore have a `.mut` twin next to
their `.ext` one, each the same proof with `Mut`'s reads substituted — which is *also* the
measurement that `ivarAsgnOk`'s docstring is asserting when it says those components read only
the shape.

### The circularity, and where the induction breaks it

`denM_ivarWrite` — "a `denM` claim survives the write, at a type that agrees about `@x`" —
needs, at the one spine entry that moved, that the **new** value is in the type the spine
claims of it: `denM τ m₂ v`. Taking that as a hypothesis is circular, because it is precisely
what the rung has no other way to know: the premise gives `denM τ m₀ v` at the machine
*before* the write.

The fix is to state the hypothesis at the pre-write machine and let the induction close the
gap. In the moved-entry arm the type owed is `ρ`, and `ivarAgree` says `ρ = τ` — but `ρ` is a
**strict subterm** of the `σ` being inducted on, so the induction hypothesis at `ρ` transports
`denM τ m v` to `denM τ m₂ v` without any circularity. The same fact read the other way is why
the guard `ivarAgree x τ τ` is not vacuous: a `Ty` cannot contain itself, so "τ's spine
mentions `@x` only at `τ`" means it does not mention it.

Two more structural notes:

* the theorem is a **conjunction** — the value reading and the spine walk — because `.inst`'s
  second half and `.clos`'s captured scope are spine walks whose entries are types, and a
  spine entry's type may itself be an `.inst`. One induction over `Ty` carries both, the shape
  `Denote/Den.lean`'s own `FirstOrder` proof uses;
* the spine half is parameterised over **two readers** related by "same, or this is the name
  that moved", which covers `.inst` (two heaps, differing at `@x` and only for `self`) and
  `.clos` (`closLocal`, a `frames` reader, differing nowhere) in one arm each.

### The three arms of the step, and the two that need no premise

`applyKont`'s `.asgnK .ivar` arm is three cases, and `Judge.ivarAsgn` has premises for none:
`self` a live unfrozen reference (the write), `self` a frozen reference (`FrozenError`), and
`self` an immediate (also `FrozenError` — immediates are frozen). The last two produce **no
value**, so the obligation is discharged there by having no case, exactly as `Judge.constExc`'s
is at `"IOError"`. `SelfLive` supplies the liveness the write needs, which is the component
clink 51 added for `NameFreeOk`'s sake and which now has a second consumer.

### §F17, and why the guard checks agreement

The rung's stall was a soundness bug (`found-issues.md` §F17, **reachable** — `validate`
accepted it): the rule moved the `@x` entry of the `self` spine and said nothing about the
*other* places a type can mention `@x`. `κ.selfTy` mentions every ivar the class has, so
`@o : C[@x : Integer]` with `@o` holding `self` is falsified by `@x = "s"`.

The fix, `ivarAsgnOk`, checks **agreement** at six places — `Γ'`, `τ` itself, `κ.selfTy`,
`κ.blockTy`, `κ.consts`, and now `I'`. Both weaker readings were tried and both are wrong:
*absence* rejects every in-method assignment, and agreement at `I'`'s **own** `@x` entry
rejects type-changing reassignment (`if flag then @v = 1 else @v = "s" end`, the program that
put `joinIvars` in `Ratchet/Ty.lean`). `ivarAgreeIvars` exempts that one entry, soundly,
because `ivarSet` replaces it.

Arrows are waved through unexamined, and that is `Later`'s doing: an arrow's denotation is
quantified over `Later`-futures and an ivar write is one (`IvarWrite.later`). `Ty.clos` is not
exempt — it reads the captured scope and creation `self` at *this* machine — which is §F1's
split, one component over. The `Later` widening this needed (drop `get`/`freshIvars`/
`freshBasic`, add `klass`/`eigen`/`payloadObj`/`frozen`) is the one that structure's own
docstring anticipated.


### §F18, and the rule that had no premise

Found while sizing `Judge.casgn` for the *next* rung, and it is **reachable**:
`X = 1; y = (X = "s"); X + 1` was certified `Integer`; CRuby raises `TypeError`. Corpus rung
250 is the witness, and it read `validate=true (MISMATCH)` before the fix.

`Ctx.afterStmt` records a constant's type through `extendConsts`, which matches a **top-level
`casgn` statement**. An assignment anywhere else is not that shape, so `κ.consts` keeps the old
type — and `Judge.casgn`'s own docstring called that invisibility "conservative, in the
direction that costs a rung rather than soundness", which is backwards: invisibility is
conservative only for a name the tables say *nothing* about. For a name they already describe,
the write makes the description wrong.

**Two doors.** `constEnv` reads the stale entry; and `constBuiltin`/`constCls`/`constExc`'s
premise is `constGet? κ n = none`, which a buried write *satisfies* — so
`y = (String = 5); String.new` types `String` as the class object while the machine holds `5`.

`constAsgnOk` is the fix, and it is §F17's shape arriving twice in one clink: **agreement, not
absence.** The first assignment of a name resolves nowhere yet (so absence is the common case),
a re-assignment at the recorded type changes nothing anyone read, and what is refused is a
rebinding the tables would then be wrong about — a different type, a declared class, a builtin
class, an exception class. `Judge.cpathAsgn` carries it at `constKeyIn owner n`, the key
`extendConsts` uses, so the guard and the table agree about which name moved.

The generalisation, now three instances deep (§F17, §F18, and §F10 read this way): **every
table the context carries is a claim about the machine, so every rule that writes what a table
describes owes that table a premise.**

### The layer's plan named a theorem that is false

The fifteenth stall point sized the remaining ladder around

> a callee's run leaves the caller's frame's locals alone

and that is **not true of the semantics**. `Machine.setLocal` walks the *capture chain*, not
the frame stack, so `x = 1; f = lambda { x = 2 }; def g(p); p.call; end; g(f)` leaves `x` as
`2` — confirmed under CRuby. A callee only has to reach a closure that captured its caller, and
an argument will do.

Two further measurements, both negative and both cheap to redo:

* **No tightening of `noLocalAsgn`'s grammar fixes §F13.** Every tightening still admits
  `.send`, and `x && x > 1` (rung 132) is the program the feature exists for; making the send
  arm answer `false` stops three rung derivations compiling, which the 177/177 gate forbids.
* **Pinning the operator's dispatch to a builtin does not work either.** A `QueryOk`-family
  component — "at every non-module class this name resolves to a builtin" — is *false at the
  booted heap* for every name the rungs need except `nil?` and `length`: `>`/`<`/`>=`/`<=`
  resolve to a **prelude** `Comparable` method at `Symbol`, `Numeric` and `Pathname`, `==` at
  `Numeric`/`Pathname`/`Encoding`, `!=` at every class, `empty?` at `Pathname`, `size` at
  `Range`. A prelude body is arbitrary Ruby and dispatches `<=>` onward, so the builtin route
  collapses into the general case.

So the honest premise bounds the program's **closures**, not its expressions: a `ClosuresOk`
exactness component in `MethodsExact`'s mould ("every closure in the heap is one `κ` records,
or the prelude's") plus a syntactic check over `κ.closures`. Rungs 132/192/194 have no closures
at all, so it should be corpus-neutral, and §F13's own witness (corpus 248) is refused for the
right reason under it. The cost not yet paid anywhere: unlike `MethodsExact`, whose upper bound
is measured once at the booted heap, closures are created **at run time**, so the component has
to be preserved by `lambdaLit`/`iterBlock` — and `Judge.lambdaLit` is already discharged, so it
gets re-proved.

### Four bricks of the corrected layer, and the narrowing's other half

`Denote/Sem/Locals.lean` is the part that can be built without any of the closure apparatus,
and every later piece calls it:

* **`ReachesB`** — the capture chain as a fuel-bounded `Bool`, mirroring
  `Machine.setLocal.owner`/`getLocal.go`'s own shape so the eventual `StateOk` component can be
  *computed* at the booted machine;
* **`setLocal`'s target is on the chain it starts from** — one lemma, a disjunction because the
  walk has two ways to end (a frame that owns the name, or the `start` fallback), which
  coincide at the call site. This is the reason an activation is safe: not that it is a callee,
  but that `b` is off its chain;
* **`CaptureDown` and fuel-irrelevance** — `getLocal` walks with `m.frames.size + 1` fuel and
  an activation grows the array, so comparing two walks needs the fuel to stop mattering, which
  needs the chain to be finite. That is *not* a fact about the types (`Frame.captured` is an
  arbitrary `Option FrameId`); `CaptureDown` — a frame captures a frame that already existed,
  so a smaller id — is what makes it so, and it is destined to be a `StateOk` component;
* **`Sealed`** — the invariant, with two conjuncts, the second being the falsifier above stated
  as a clause. Nothing about `m.kont`: restoring a frame id only pops back to a frame already
  on the stack.

And narrowing's **then** side, which clink 58 left out because the guards read only the else
side: `EnvOk_refineOne_then`, `narrow_then_fact`, `stateOk_narrow_then`. Two notes. The `then`
transport is a *copy* of the `else` one rather than one lemma parameterised over `refineOne`'s
`thenSide` — that was tried first, and the function's own `let refine := fun τ => if thenSide
then …` leaves an `if` in every goal, so `split` picks it instead of the `isAliasTy` guard the
proof is analysing. And `stateOk_narrow_then` needs a hypothesis its twin did not, because the
then side of `narrowEnvs` refines for **both** `NarrowSides`: the `&&` sandwich, the only
`thenOnly` producer, has to be excluded by the caller. That exclusion is §F13, and it sizes
what is left of `Judge.if'` exactly — with the sandwich admitted, this lemma plus the run
inversion *is* the rung.

### And the seventeenth stall point: `casgn` is not free after all

`Judge.casgn` has no premise and no context growth, so it looked like the one remaining rule
outside both walls. `applyKont`'s `.casgnK` writes into `currentFrame.defmod`'s own constant
table; `ConstScopeOk` compares resolution against `Object`'s table alone. A machine inside
`class A … end` is conformant until the body's first constant and not after it — so `StateOk`
holds before the step and fails after, and the conclusion asks for it after. The component is a
conjunct of **both** sides of the implication, so the fix is a weakening, and every obvious
weakening breaks the three `.const` rungs that consume it. That is the eighth stall point from
a new direction, and it moves `casgn`/`cpathAsgn` into the declaration-family redesign.

### Gates

Corpus **250/250** agreement, 0 disagreements (the corpus grew by §F18's witness);
expect_validate mismatches **35**, unchanged through both guards; 177/177 hand derivations;
145/145 negative controls; `Denote/Examples.lean` green; no `sorry`, no new axioms. Nothing
under `ruby/lean/` changed.


## Clink 60 (2026-09-07) — the seal is not inductive, §F19's four doors, and a census. **178 rungs / 254, 47 of 83 rules**

**No rung**, and that was reached by attempting the layer's own next step and by auditing all 36
remaining rules rather than by running out of time on one of them. Three things landed: a
refutation, **four reachable soundness bugs**, and a census.

### The refutation — `not_BuiltinsSeal`

`Denote/Sem/StepLocal.lean`'s plan (clinks 57–59) reads: `Sealed`/`FramesWF`/`StepInv` are
built, `Denote/Sem/FrameLocal.lean` has the `Builtins` layer uniform for `LocalsSame`, so
carrying the **seal** across `Builtins.run` is the free half before the interpreter walk starts.
It is not free. It is false, and there is exactly one falsifier in the table.

`Symbol#to_proc` (`RubyCore/Builtins/Strings.lean` L441) allocates a `Closure` with
`captured := 0` — the toplevel frame — because `Closure.captured` is a `FrameId` and not an
`Option FrameId`, so there is no way to spell "captures nothing". `Sealed.clos` reads exactly
that field. So a builtin call drops a closure over frame `0` into the heap and the seal at
`b = 0` is gone, and `b = 0` is the frame every toplevel narrowing rung is about.

`not_BuiltinsSeal` is the proof, at the smallest machine where the seal says anything (two
frames, neither capturing, the caller `0` sealed off behind the frame that is running, an empty
heap), conditional on one `#guard`ed `Bool` — `Denote/Sanity.lean`'s trade, for its reason.
Axiom-clean.

**Decisions that were not forced, and what was rejected.**

* **Stated and refuted rather than patched.** The alternative was to add a hypothesis at
  `Sealed.alloc`'s call site and move on. Rejected for `Denote/Sem/Frame.lean`'s reason: the
  claim is false at a machine the seal really holds at, so no premise over `(b, m)` excludes it,
  and a hypothesis would have hidden that.
* **The model was not changed.** `captured := 0` is inert — the closure's body is
  `__recv.s(*__rest)`, assignment-free — so retyping the field or picking a different id would
  be a semantics change made to suit a proof, and the field has no "none" to pick. Rejected on
  `AGENTS.md` §Justification grounds: the denotation should not edit the machine to make itself
  provable.
* **`ClosInert` was not added yet.** Admitting an escape (`… ∨ this closure cannot write`) in
  `Sealed.clos` is easy and *insufficient*: `callClosure` then pushes a block frame whose
  `captured` is the inert closure's, and `Sealed.stack` — unconditional — breaks. Weakening that
  clause the same way needs "the code running in this frame cannot write", which is a property
  of `ctl`/`kont`. Writing the easy half alone would have looked like progress and been a dead
  end, so it is recorded as the eighteenth stall point instead.

The design consequence is the fifteenth stall point's own prediction with a number on it: **the
invariant has to be joint over the frame graph and the control state.** `Sealed` is the
frame-graph half and it is built; the half that says what the machine is about to do is not.
One thing the plan did not predict: `ClosuresOk`'s exactness needs a **third** escape beyond
"the program's or the prelude's" — a closure a *builtin* created, from source that is in
neither. Grep says `Symbol#to_proc` is the only one, so it is a fixed shape rather than an open
set.

And a working lesson, the second time it has paid: **write the layer's target down as a named
`Prop` before proving the layer under it.** The `Builtins` layer was proved uniform for
`LocalsSame` (532 lines) before anything asked whether the seal travelled across it; stating
`BuiltinsSeal` first would have cost an hour and found this. Same lesson as `KontFrame`.

### §F19 — `bodyResult` is right for a lambda and wrong for a proc, and there were four doors

Found by the *census*, not by search: sizing the jump-freeness conjunct (the fourteenth stall
point) means asking which `Judge` rules would have to discharge "this expression's run emits no
return jump", and `Judge.lambdaLit` is the rule that cannot — it has no premise about the block
body at all. Asking why that was safe produced a program that is not:

```ruby
def f;  p = proc { return "s" };  p.call;  1;  end;  f + 1   # certified Integer; TypeError
```

and then three more, one per site `bodyResult` had spread to (`iterBlock`, `yieldExpr`,
`iterClosPass`). All four are certified `Integer` and raise `TypeError` under CRuby *and* the
model. Written up as `found-issues.md` **§F19**; corpus rungs **251–254**.

`bodyResult` rewrites a body that is exactly `return e` to `e`. `return` in a **lambda** returns
from the lambda, so that is exactly right and `lambda-explicit-return` (rung 105) is the rung
that needs it. `return` in a **proc** or a **block** returns from the *enclosing method*, so the
call never comes back and the method's value becomes `e`'s — the call has no type, and the
method's recorded return type is a lie. Its own docstring said the rewriting was "applied only
at `closCall`, because only a lambda rung asks"; by the time it was read, `bodyResult` sat at
four rules and `closCall` could not tell a lambda from a proc.

**Decisions that were not forced, and the alternatives rejected.**

* **A refusal at `lambdaLit`, not a field on `Clos`.** The precise fix is to record `lam` on
  `Clos` and make `bodyResult` conditional at all four sites. Rejected on blast radius: `Clos`
  is what `closIdx?` matches on (by syntax, so the field would have to join the key), what
  `Denote/Sem/State.lean`'s `closTblOk` compares, and what `collectBlocks` builds — and the
  precision it buys is `proc { return e }`, which is a program nobody should write. `procRetOk`
  is one `Bool` on the one rule that can see `m`, and a `proc` whose body is exactly `return e`
  now gets **no type**.
* **`iterClosPass` was left alone**, and that is a consequence rather than an omission. With
  `procRetOk` in place the only `Ty.clos` with a `.ret` body comes from a `lambda`, and
  `[1].map(&->(y){ return e })` is *sound* — there the `return` really is the block's value. So
  the rule keeps its precision and the fourth witness is refused because its `&p` premise can no
  longer be met.
* **`iterBlock` and `yieldExpr` lose the rewriting outright.** Both take a block **literal**
  (`yieldExpr` reads `κ.blockTy`, which `callDefBlk` fills from a literal), never a lambda, so
  there is nothing to condition on. A whole-body `return` in a block now has no rule, which is
  the right answer.
* **The guard matches `bodyResult`'s pattern rather than mentioning `.ret` generally.** A
  `return` anywhere other than as the whole body already had no rule, so the narrow guard
  refuses nothing that was previously derivable — checked by the mismatch count staying at 35.

`Ratchet/Proof/ChkSound.lean` needed one line (the guard is a fourth `&&` conjunct, so
`lambdaLit`'s destructuring nests one deeper) and `Denote/Rules/Lambda.lean` one (`intro` gains
the new hypothesis) — the semantic rung survives the premise, since an extra hypothesis makes an
obligation easier.

**And it is a different pattern from §F17/§F18.** Those were "a rule that writes what a table
describes owes that table a premise". This one is: **a syntactic shortcut is scoped to the rule
that justified it, and copying it to a second rule re-opens the justification.** `bodyResult`'s
argument was correct for lambdas at `closCall` and was never re-run at the three sites it was
later reused at.

### The census — why no rung was available

`Denote/Sem/notes.md` §Where the remaining 36 rules sit is the audit, rule by rule. The result
is that **none of the 36 is one rung's work**: each is behind one of four unbuilt layers (the
locals/control invariant; the call lemma plus jump-freeness; `κ` threaded through `Judge`'s
signature; `PrimSig` row by row), or behind a stated falsity (`arrayLit`/`hashLit`, the seventh
stall point's remnant).

Two findings from the audit worth carrying:

* **`JudgeSeq.cons` belongs to the declaration family**, which the old table did not say. Its
  second premise is at `κ.afterStmt e σ` while its own hypothesis is at `κ`, so it is the sixth
  stall point read from the consumer's end rather than a sequencing lemma.
* **`Judge.if'` is not the cheapest remaining rung, and there is no cheapest remaining rung.**
  `semladder` prints the inductive's constructor order, which puts `if'` first, and `if'` looks
  one lemma away — all six narrowing type-lemmas are proved (clink 57) and
  `stateOk_narrow_then`/`stateOk_narrow_else` are the assembled transports. It is blocked
  *twice*: by the `&&` sandwich's `thenOnly` refinement (the locals layer) **and** by the
  eleventh stall point, where `joinEnv` synthesizes an alias nobody promised and the obligation
  is false as written. Both of the eleventh's recorded repairs cost something this clink's
  constraints forbid — one re-opens `Judge.vasgn`'s already-discharged premise, the other moves
  `joinT`'s output types and therefore the syntactic ratchet.

### Probed against CRuby afterwards (2026-09-08) — and it downgrades the exit

The exit below was written from the refutation alone. Probing the arm it exploits against the
reference semantics — 20 programs replayed under `--sut lean` (17 agree, 2 disagree, 1 gate),
plus CRuby-only probes — says the blocker is **in the model, not in the invariant**, and is
bounded. `found-issues.md` §A6 is the entry; `Denote/Sem/notes.md`'s eighteenth stall point
carries the detail.

`:upcase.to_proc.binding` raises `ArgumentError` and `source_location` is `nil`: **CRuby's
`Symbol#to_proc` proc has no binding at all.** So `captured := 0` is a capture edge the
reference semantics does not have, forced by `Closure.captured : Nat` where `Frame.captured` is
already `Option FrameId`. The clink below rejected touching the model on "the denotation should
not edit the machine to make itself provable" grounds; that reasoning does not survive the
measurement, because giving the field its `Option` is a **fidelity fix justified independently
of the proof**. Blast radius: 2 construction sites, ~4 readers in `RubyCore/Interp/`, 14 files
in `RubyCore/Proof/`, 12 in `Denote/`.

Two corrections to the clink below, both measured: there are **two** spurious-edge sites, not
one (`coerceToProc` in `Interp/Support.lean:448` builds the same closure for `&:sym`, so the
fiction is not confined to the `Builtins` layer), and the `Sealed.stack` objection that made
this look like a redesign was a consequence of the inertness escape — which the fidelity fix
makes unnecessary.

`not_BuiltinsSeal` stands unchanged: it is a theorem about `Sealed` and `Builtins.run`, both
definitions in this repo, so fidelity does not bear on its truth. What moves is the prognosis —
**try the `Option` and re-attempt the `Builtins` layer before designing a joint
frame-graph/control-state invariant.**

Two unrelated fidelity gaps came out of the same probe run and are filed with it: the model's
`Symbol#to_proc` is **not identity-stable** (CRuby interns per symbol, `a.equal?(b)` is `true`
there and `false` here) and its zero-argument `ArgumentError` carries a different message
(`"wrong number of arguments (given 0, expected 1+)"` vs CRuby's `"no receiver given"`).

### EMERGENCY EXIT — the layer gating the largest block of rungs needs a redesign, not a continuation

Flagged here so the next session reads it before starting rather than rediscovering it.

**The deficiency.** `Denote/Sem/Locals.lean`'s `Sealed` — the frame-graph invariant the whole
locals layer is built on — **is not inductive over `stepFn`**. `not_BuiltinsSeal` is the proof.
The layer's plan (clinks 57–59) was: `Sealed`/`FramesWF`/`StepInv`, then the `Builtins` layer,
then the interpreter walk. The `Builtins` layer is where it stops: one builtin allocates a
closure over frame `0`, and no premise stated over `(b, m)` can exclude it, because the
allocation happens at a machine the seal really holds at. The escape that would admit it
(`… ∨ this closure cannot write`) fixes `Sealed.clos` and breaks `Sealed.stack`, whose repair is
a statement about `ctl`/`kont`.

**Why that is a rewrite and not a next step.** The invariant has to become **joint over the
frame graph and the control state**. `Sealed` survives as one half; the interpreter walk it was
being built for cannot start until the other half exists, and the 532 lines of `FrameLocal.lean`
were proved for a target that was never stated as a `Prop` first. That is the layer gating
`if'`, `ifNoElse`, `begin'`, and — through jump-freeness, which the call decomposition cannot be
*stated* without — the 22 call rules.

**What was verified before flagging**, so the next session does not re-derive it: all four
remaining layers were probed, and none has a rung available at its near edge. The call lemma
needs `JumpOpaque K` and `retK` is precisely a continuation that turns an escaping jump into a
value; a fully recursive jump-freeness conjunct un-discharges `Judge.lambdaLit`, which has no
premise about its block body; the declaration family needs `Judge`'s signature, i.e. all 177
derivations; `Judge.prim` is the ~200-row model-coverage job. `arrayLit`/`hashLit` and
`if'`/`ifNoElse` are each additionally behind a **stated falsity** (§the seventh stall point's
remnant, §the eleventh stall point).

**What was done after flagging, and why it does not change the flag.** The census that produced
this conclusion is also what produced §F19 — four *reachable* soundness bugs, found by asking
which rules could discharge a jump-freeness conjunct. Fixing them is `AGENTS.md`
§Justification's own instruction and moves the checker, not the ladder. The ladder is still 47.

**Where to start.** State the joint invariant as a named `Prop` — `Sealed b m` paired with a
predicate on `ctl`/`kont` — and *attack it* before proving anything under it. That is the lesson
`not_KontFrame` taught in clink 52 and this clink paid for a second time.

### State

Semantic ratchet **47 of 83** (unchanged; `Judge` 32/67, `JudgeSeq` 3/4, the six companion
families complete, denominator still 83). Syntactic ratchet **178 of 254** rungs certified
well-typed — the corpus grew by §F19's four witnesses, all four correctly refused — with
expect_validate mismatches at **35**, unchanged, and 254/254 CRuby agreement with 0
disagreements. 177/177 hand derivations and 145/145 negative controls (`checkrungs`);
`Denote/Examples.lean` green; no `sorry`, no new axioms. `Ratchet/Judge.lean`,
`Ratchet/Validate.lean` and `Ratchet/Proof/ChkSound.lean` changed for §F19 and for nothing
else; nothing under `slice/` or `ruby/lean/` was touched.

*(Note for the next session: the goal text quotes the syntactic ratchet as "177/232" and the
negative controls as "140/140". Both are stale — 177 is the count of hand-authored derivations,
which `checkrungs` still reads at 177/177; the ladder's denominator is the corpus, now 254, and
the controls are 145.)*

## Clink 61 (2026-09-08) — the seal's blocker was a model fiction; the seal is closed; two half-layers proved; the census re-verified rule by rule. **178 rungs / 254, 47 of 83 rules**

Clink 60 exited on an architectural flag: `Sealed` is not inductive over `stepFn`, so the
locals layer — which gates `if'`/`ifNoElse`/`begin'` directly and the 22 call rules through
jump-freeness — needed a joint frame-graph/control-state invariant before it could continue.
This session executed the decision recorded against that flag, and the flag comes down.

**The ladder does not move, and that is the honest reading.** 47 of 83, unchanged. What this
clink removes is a *refutation*, not an obligation: `not_BuiltinsSeal` is retired, so the
`Builtins` layer can be re-attempted at all. A session that discharges no rule and says so is
the point of counting rules rather than counting work.

### What was discharged

Nothing. See above. The deliverable is L266, below, plus one baseline finding.

### L266 — `Closure.captured : Option Nat`

`RubyCore/Heap.lean`'s `Closure.captured` was a bare `Nat`, so "captures nothing" was
unspellable and the two sites where the model *invents* a Proc for a Symbol
(`Interp/Support.lean`'s `coerceToProc` on `&:sym`, and `Builtins/Strings.lean`'s
`Symbol#to_proc`) wrote `0` — the toplevel frame. `Sealed.clos` reads that field, so the
allocation put a closure over frame `0` into the heap and the seal at `b = 0` was destroyed by
a capture edge **CRuby does not have**: `:upcase.to_proc.binding` raises `ArgumentError` and
`source_location` is `nil` (`found-issues.md` §A6a, probed 2026-09-08).

The field is now `Option Nat` — `Nat` and not `FrameId` for the import-cycle reason
`MethodDef.capturedFrame` already documents — and those two sites take `none`.

**Not forced, and recorded because it is the interesting half.** Three places had a real
choice, and `.getD 0` was the cheap answer at all three. It is right at two and wrong at one:

* `Interp/Support.lean`'s `callClosure` reads `m.frames.getD (cl.captured.getD 0) default` for
  `self`/`defmod`/`blk`/`cref`. **Kept `getD 0`** — it is byte-for-byte the frame this line
  read before, so the two `none` closures see exactly the `self` they saw, and the *only*
  behavioural change is that the pushed block frame's own `captured` is now `none` instead of
  `some 0`. Unobservable: the body's free names are its own parameters.
* `Denote/Apply.lean`'s `closSelf` mirrors that line, so it **keeps `getD 0` too** — a
  denotation that disagreed with `callClosure` here would be describing a different call.
* `Denote/Apply.lean`'s `closLocal` **does not**, and this is the one that would have been a
  silent bug. It is the closure's captured-*locals* reader, and the block frame `callClosure`
  pushes carries `captured := none`, so the body's walk stops at its own activation and every
  free name reads `nil`. `getD 0` would have had the denotation reading the toplevel's locals
  for a program that reads none of them. New `frameLocal?` answers `.nil` for `none`; four
  transport lemmas (`Ext`, `Mut`, `reCtl`, `setLocal`) grew a two-case split and nothing else.

**Two definitions changed shape rather than parenthesisation**, which is where the fidelity
actually moved. `Sealed.clos` and `FramesWF.clos` are now quantified —
`∀ p, cl.captured = some p → …` — matching the shape their `Frame`-side clauses
(`Sealed.push`, `FramesWF.push`) already had. A capture-free closure discharges them
**vacuously**. That is the whole repair; everything else is transport.

**Rejected, and it was decided before implementation** (full four reasons in
`Denote/Sem/notes.md` §The decision): keep `captured := 0` and discharge the allocation with a
lemma showing `Symbol#to_proc`'s body mutates nothing. It does not discharge `Sealed` as
stated — that clause is about the capture *graph* — so spending it means first weakening
`clos` to "…or this closure is inert", and that escape is exactly what drags the unconditional
`stack` clause into control-state territory. Its one merit was costing no difftest re-run.

**`not_BuiltinsSeal` retired.** It was a true theorem about two definitions in this repo and
L266 changed one of them. `toProcBreaksB` → `toProcSealsB`, still a `#guard` and still
non-vacuous: it checks the call **returns a Proc** *and* that the Proc captures nothing, so it
cannot pass by `Builtins.run` gating. `BuiltinsSeal` is left **stated and unproved** — one
builtin measured is not the layer walked, and pretending otherwise is how a `#guard` becomes a
theorem it never was.

**Smaller than advertised.** The hand-off priced eight model sites plus 14 `RubyCore/Proof/`
files and 12 `Denote/` files. Lean's `Option` coercion absorbed every *construction* site that
wrote a bare `FrameId` — `blockClosure`, `lamClos`, `dmPcl` all still elaborate untouched (they
are now written with an explicit `some`, for readers) — so what actually broke were the
*reads*. Six proof files and five `Denote/` files.

### The `MethodDef` arm is still a draft

L266 did not touch it. `Denote/Sem/notes.md` has the clause, its `FramesWF` twin, its consumer
(`Sealed.push` at `enterUserMethod`) and the writer-by-writer argument that it is closed; the
measurement behind it (`probes/measure_captures.lean`: 0 capturing methods and 0 Procs at the
booted machine, re-run and re-confirmed after L266) still stands. It is the next thing the
locals layer needs after the `Builtins` walk.

### Baseline finding: `lake build Metatheory` is red at HEAD — `found-issues.md` §A7

Found while establishing a baseline, on a clean tree, before any edit. Three breaks, none
caused by L266. The one worth reading is the first: `Proof/Static/Iter.lean`'s
`startArgs_lambda` is **a false statement**, not a broken script — commit `0657e1c` (the A5 fix,
"teach the model to shadow `Kernel#lambda`") put a `shadowed` test in front of the branch it
claims is `reifyBlock` by `rfl`, so a user `def lambda` refutes it. Its consumer in
`Preservation.lean` then needs a fragment invariant supplying `shadowed = false`, which the
fragment does not have; that missing clause is the real finding. The other two
(`Preservation.lean:1518`, `:2404`) are proof-script repairs.

Extent was measured rather than guessed: with exactly those three transiently `sorry`ed,
`Metatheory` + `Judgment` + `HJudge` build clean and the only remaining failures are the
`#guard_msgs` axiom bills correctly reporting `sorryAx`. The `sorry`s were then reverted — the
tree carries none. This is the rot mode `lean/lakefile.toml`'s own comment predicts for a
library outside `defaultTargets`, arriving on schedule.

**Not fixed, deliberately.** Repairing it is a separate job with a soundness-shaped question at
its centre, and it is not what the semantic ratchet is blocked on. Filed so the next session
starts from a known baseline instead of attributing it to whatever it changes next.

### L267 — the `MethodDef` arm, and the `Builtins` layer's frame half

L266 removes the refutation; these two are the first work it makes possible.

**`Sealed.meth` + `FramesWF.meth`.** The third clause the eighteenth stall point's enumeration
found missing: of the six `frames.push` sites, the two that set `captured` read
`Closure.captured` (which `clos` covers) and **`MethodDef.capturedFrame`, which nothing
mentioned**. `enterUserMethod` is the push, `define_method` the writer, and the hazard is real
on both executors (`x = 1; Object.send(:define_method, :setx) { x = 2 }; def g; setx; end; g; x`
is `2` under CRuby and under the model). Threaded through all eleven preservation lemmas.

**Two departures from the draft**, both found by the elaborator rather than by re-reading it:

* **`Sealed.alloc`/`FramesWF.alloc` needed a second premise.** The draft's writer-by-writer
  argument covers `defineMethod` writing into an *existing* payload. A fresh `Heap.alloc` of a
  **class** carries a method table too, so the `meth` clause owes there exactly what `clos`
  owes for a fresh Proc. Every caller in the model discharges it trivially — classes are
  allocated with `methods := []` — but the lemma is false without it.
* The lookup is a named `methodIn h k n` rather than the inline `bind`/`find?`/`map` chain
  written three times, because the clause, its twin and their consumers have to agree on it
  syntactically.

**Vacuity re-measured, not assumed** (`probes/measure_captures.lean`, `Sanity.lean`'s rule):
still 0 capturing methods and 0 Procs at the booted machine. Both clauses are satisfiable and
trivially satisfied where the ladder starts — which is the check worth doing, since an
unsatisfiable component makes every obligation true for the wrong reason.

**`Sealed` is now the closed three-clause invariant** the enumeration predicted: stack,
closures, methods, with no writer left over and the control state not in it.

**And the `Builtins` layer's frame half fell out nearly free.** `Sealed`/`FramesWF` read exactly
two things — the frames' `captured` links (plus the frame count, for the congruence) and the
heap's closures and methods. The frame side was *already* being proved by this layer's existing
600-arm walk (`FrameLocal.lean`'s `builtins_run_locals`); its claim `LocalsSame` was simply too
weak to say so, projecting only `locals`. Adding two conjuncts — every frame's `captured`, and
`frames.size` — cost **three lemmas and one `rfl`**: `setCurrentFrame` (the only arm in the
layer that writes `frames` at all, and it copies the frame to flip a `Bool`),
`setLastMatchValue` (the same `set!` shape), and one extra argument in the `builtin_arms`
macro. Six hundred arms re-elaborated green with no other change.

**Not forced, and the alternative was the expensive one.** The obvious move was a *second*
predicate (`CapturedSame`) with its own traversal. Rejected: every one of the six hundred arms
would discharge it by the same `of_eq` the first traversal already uses, so it is the same walk
written twice. A conjunct is one walk.

What that buys, in `Denote/Sem/StepLocal.lean`: `Sealed.of_localsSame`/`FramesWF.of_localsSame`
(the frame-side congruence of each invariant *is* `LocalsSame`), and `builtins_run_seal`/
`builtins_run_framesWF` — the same at `Builtins.run`, so a caller owes **only the heap
clauses**. That turns "the layer is unproved" into a proposition with two named hypotheses,
and those hypotheses are the specification of what remains.

**What remains, and why it will not ride the first walk.** The two hypotheses say `Builtins.run`
installs no capturing closure and no capturing method. Both are true — the layer's only closure
allocation is `Symbol#to_proc`, which since L266 captures `none`. But a heap conjunct cannot be
added to `LocalsSame`: nearly every arm discharges it through `LocalsSame.of_eq rfl rfl`
(*frames* unchanged) while the heap is exactly what those arms change, by allocation, and
`of_eq` has no heap hypothesis to discharge it with. The second walk needs its own
allocation-monotone predicate and its own copy of the twenty machine-threading helper lemmas.
A clink, not a follow-on.

### L268 — `JudgeSeq.cons`'s run half, and the transport that is not merely unproved

The census (clink 60) says every remaining rule is behind one of four layers. Rather than
trust it, three rules were attacked directly. Each hit exactly the layer the census predicted,
and the third produced a proof and a measurement worth keeping.

* **`Judge.begin'`** — the one rule gated by the *locals* layer alone, so the obvious candidate
  after L266/L267. It needs `StateOk` at an **arbitrary intermediate point** of the body's run
  (a handler runs mid-body; that is what `noLocalAsgn body` is a premise about). That is the
  fifteenth stall point, not a lemma.
* **`Judge.vcallAsm`** — looked nearly free: `AsmsOk` is already the exact semantic content of
  `κ.asms`, so the value's type is immediate. It is not enough. The obligation also demands
  `Framed m m'` and `StateOk κ Γ I m'` **across an arbitrary user method call**, and `AsmsOk`
  says nothing about state preservation. That is the call layer.
* **`JudgeSeq.cons`** — the one that moved.

**The run half is proved** (`Denote/Rules/SeqCons.lean`, axiom-clean). `Judge.seq`'s docstring
said `cons` was blocked by the *fifth* stall point — the first statement runs under `.seqK
rest`, a non-empty continuation, while `Evals` is defined at an empty one — and that stall
point was cleared in clink 54. `evals_seq_cons` spends it: a run of `.seq (e :: e' :: es)` **is**
a run of `e` followed by a run of `.seq (e' :: es)`, both machines exhibited. Three obligations
to `run_split`, each one computation: `CatchFree [.seqK rest]`, `JumpOpaque [.seqK rest]`
(word for word `jumpOpaque_asgnK`, which its own docstring predicted would be the shape every
literal kont follows), and the two one-step equalities at either end.

**One asymmetry that is not bookkeeping**, and it cost the second half of the file:
`evalExpr`'s singleton arm (`.seq [e]`) pushes **no** continuation, while `applyKont`'s `.seqK`
arm pushes a trailing `.seqK []`. So delivering into a *one-statement* tail does not land on
the machine `evalFrom` reaches, and that case needs a second `run_split` at `[.seqK []]` whose
delivery is a value at an empty continuation. `evals_seqK_tail` is that case split.

**And the blocker that remains was measured, not assumed.** `Obl.JudgeSeq.cons`'s second
premise is at `κ.afterStmt e σ` and its conclusion at `κ`, so the rung needs `StateOk`
transported **both ways**. The finding is that the two directions fail on *different*
components, which is what rules out the obvious repair:

| a bigger table makes the claim… | components | transport it gives |
|---|---|---|
| **weaker** (antecedent fires on fewer names) | `NameFreeOk`, `BareNameFree`, `MissFree` | up only |
| **stronger** (`∀ c ∈ C` ranges over more) | `ClassesOk`, `DefsOk`, the `consts`/`privConsts` family | down only |

So there is no monotonicity lemma to prove in either direction, and strengthening `SemJudge`'s
conclusion to the grown context — the move the goal statement explicitly sanctions — buys *up*
at the cost of *down*, leaving `JudgeSeq.cons`'s own conclusion unstatable. The design that
would work is visible: `SemJudgeSeq` must conclude at the context after **all** of `es`, so
nothing ever transports downward — and that needs a "context after a statement list" function,
which `extendConsts` blocks by taking the statement's *type*, which the signature does not
carry. Hence the census's verdict, now with evidence rather than by inspection: a change to
`Judge`'s signature, i.e. to all 178 derivations.

### State

Semantic ratchet **47 of 83**, unchanged (`Judge` 32/67, `JudgeSeq` 3/4, the six companion
families complete, denominator still 83). **Three sessions' worth of layer work moved and the
number did not, which is the ladder working as designed**: L266/L267 remove a refutation, close
an invariant and prove half a layer, and none of that is a `Judge` rule. The census in
`Denote/Sem/notes.md` §Where the remaining 36 rules sit still holds — every one of the 36 is
behind one of four unbuilt layers, and no layer is smaller than a clink. Syntactic ratchet **178 of 254** rungs certified
well-typed, unchanged, expect_validate mismatches **35**, unchanged. Because L266 changes the
*machine*, everything downstream was re-verified rather than assumed: difftest tier 0 **1304
ran, 992 agree, 0 disagree**; corpus agreement **254/254**; `checkrungs` **177/177 hand
derivations + 145/145 negative controls**; `Denote/Examples.lean`'s `#guard`s green; `lake
build` clean in both packages; no `sorry`, and every `#print axioms` a subset of
`propext`/`Classical.choice`/`Quot.sound`. **Nothing under `Ratchet/` was touched.** Changed:
`ruby/lean/RubyCore/{Heap,Interp/Support,Interp/Reflect,Builtins/Strings}.lean` and six files
under `RubyCore/Proof/`; `ratchet/Denote/{Apply,Ext,Local,Rules/Core,Rules/Lambda,Sem/Mut,
Sem/Locals,Sem/StepLocal}.lean`; `probes/measure_captures.lean`.

---

## Clink 61 (2026-09-09/10) — `context-splitting.md` steps 1–5, built and measured

`context-splitting.md` was a design when this clink started. All five of its migration steps are
now on file, in the doc's own order, with the ladder measured after each. **No rung moved in
either direction at any point** — 178/254, `checkrungs` 177/177 hand derivations — the negative
controls went **145 → 148**, and the semantic ratchet went **47 → 48 of 83**.

### Step 2 — the split, made cheap by an accessor layer

`Ctx` became `Pos`/`Neg`/`Scope`. The thing that made this a one-sitting refactor rather than a
churn of 277 KB of rules is worth recording as a technique: **`@[reducible] def Ctx.classes
(κ) := κ.pos.classes`** and eight siblings. Dot notation resolves `κ.classes` to the def, and
reducibility keeps every `by rfl` premise and every `simp` in the proofs working unchanged. So
only the *writers* moved — sixteen `{ κ with … }` sites, replaced by four named updaters
(`pushAsm`, `withFrame`, `withBlockTy`, `withClosures`). Six `simp` calls in `Denote/Sanity.lean`
needed the accessor name added to their lemma list; that was the whole downstream cost.

### Step 1 — the `Neg` seed, and §F20 closed

`negEmit` walks **every expression position** carrying the lexical cref down, so
`class C; def a; def b; end; end; end` puts `b` on `C`'s chain and a top-level `def` anywhere
puts its name on `Object`'s. `negSeed` closes that over both chains of §4.6 and materialises the
port grid; `Ctx.withBlocks` runs it once, beside `collectBlocks`, for the same reason.

Three positive-table *misses* were deleted along with the encoding that made them wrong —
`bareName`'s `defDeclared? … = none`, and `clsToS`/`caseEqQuery`'s `smroGet? … = none`. Each was
a claim about a table's *completeness* wearing a lookup's clothes, which is §4.4's diagnosis and
§F20's mechanism.

**Two decisions inside the seed.**

* **`Neg` stores the *declared* names, not the free ones.** The free set would have to be
  enumerated against a name list, and a name missing from that list would read as "free" — the
  unsound direction. A name missing from `declared` is a name the program does not declare,
  which is the fact itself. The keyed `noMethod` grid still needs a name list (`negNames`), and
  there a missing name means "unseeded", so a rule asking about it declines: conservative.
* **The four query rules are *not* keyed yet**, though the seed materialises the keyed fact and
  `tyPorts?` computes the port. The blocker is semantic: `QueryOk`/`ClsQueryOk` are quantified
  over **class ids** with a name-global antecedent, so a keyed premise has nothing to discharge
  them with. Recorded at the end of §F20.

**§11's first open question, answered by measurement.** The keying pays for the seeding
*exactly*: the ladder held tier for tier on all 254 rungs, not just the six §10.1 priced.

### Step 3 — threading, and the elaboration tax §8.2 predicted

`Judge : Ctx → Env → Ty → Expr → Ty → Ctx → Env → Ty → Prop`. Three shapes were tried for the
outgoing index of a *premise*, and the third is the only one that works:

1. **Floating** (a fresh implicit per premise). Reads best and is what §2 describes. Fails on
   the semantic side: a rule that discards its sub-derivation's outgoing context cannot then
   republish conformance at its own, because the two are unrelated.
2. **Pinned to the incoming context.** Elaborates perfectly and refuses exactly the F20 shapes.
   Fails `chk_sound`: `chk` accepts a declaration in an expression position that `Judge` would
   then not derive, so the guard would have to be added at ~40 recursion sites.
3. **Determined — `κ.afterStmt e τ`, in premises *and* conclusions.** Derivable set identical to
   before (`Judge.out_afterStmt`, `cases h <;> rfl`), `chk_sound` needs no change to `chk`, and
   the semantic premise delivers exactly what the next statement wants. Uniformity is what makes
   the elaborator's unification of a derivation's two ends syntactic; mixing `κ` in conclusions
   with `afterStmt` in premises leaves it trying `κ =?= κ.afterStmt ?e ?τ` and stuck.

§8.2's warning cost exactly one rung: `narrow-union-ivar` defers its method body to a hole, and
`refine` will not finish with an index of the goal unassigned. A postponed nested `by` has the
same deferral and leaves the unification to the end, so the index solves itself.

### Step 4 — the conclusion does not *move* to `κ'`, it gains it

§8.1 step 4 says "`SemJudge`'s conclusion moves to `κ'`". Moving it **weakens the premise every
non-declaring rule lives on**, and the repair is not a lemma: see §F21 and `context-splitting.md`
§12. So `SemJudge` claims outgoing conformance at **both** contexts, which are for different
readers — `StateOk κ` is what a consumer republishes, `StateOk κ'` is what the next statement
needs. Written as two flat conjuncts rather than a bundled pair, so a consumer that wants the
first adds `-` to its pattern and a producer whose `κ'` is `κ` supplies the same term twice;
bundling would have made every existing `⟨_, _, hok⟩` silently bind `hok` to the pair.

### Step 5 — `JudgeSeq.cons`, and the correction to §3 that getting it required

`Obl.JudgeSeq.cons` needs `StateOk` transported **down** across `afterStmt`. The *up* direction,
which L268 recorded as the other half, is **gone**: step 1 put `NameFreeOk`/`BareNameFree`/
`MissFree`/`MethodsExact` onto `Neg` (invariant under `afterStmt`) and step 4 states the
grown-context conformance rather than transporting to it.

Down is not "antitone, one line" (§F21). It splits three ways, and the split is the finding:

* **Free** — `ClassesOk`/`DefsOk` and the membership halves of `NestedClassesOk`/`DeclClassOk`
  really are `∀ x ∈ table` over a table that grows, because **`mergeCls` prepends** the merged
  entry rather than replacing it in place. That is a fact about a function whose docstring
  already gave the reason, and it makes a third of the transport free.
* **Invariant** — most of `StateOk`, since `Ctx.afterStmt` rewrites only `pos`. Those components
  are the same proposition at both contexts and are *reused*, not transported.
* **Owed** — `ConstsOk`/`ConstPathsOk` (`extendConsts` is `envSet`, which overwrites) and
  `DeclClassOk`'s four guarded clauses.

**Three of the antitone guards were fixed rather than paid for**, by applying §2's own test:
`isANoOk`/`mixinFreeChain`/`coreConstFree` and `BaseChainsOk`'s `constGet? = none` clause are
*negative* facts about the context, so they belong in `Neg`, seeded whole-program the way
`noMethod` is. `Neg` gained `wholeCls` and `boundConsts`; the guards read those and are now
invariant. Every one of the three is **strictly more conservative** — a bigger class table can
only make `mixinFreeChain`/`noDeclaredBelow` answer `false`, and not-bound-*ever* implies
not-bound-*yet* — so none can admit what the per-point version refused. The *positive* half of
narrowing still reads `κ.classes`, and the split is deliberate: a chain is broken by a class
declared later just as much as by one declared earlier, while a constant not yet assigned
resolves nowhere and raises. Measured: the ladder did not move.

What is left is `Ratchet.ctxKept` — the constants clauses, and `DeclClassOk`'s antecedents
stated one-directionally — carried as `JudgeSeq.cons`'s third premise and as `chkSeq`'s guard so
`chk_sound` still holds. **All 178 hand derivations discharge it by `rfl`.**

An earlier shape of `ctxKept` demanded the `isANoOk` implication instead of making the guard
invariant, and that version cost exactly one rung (`class Uncomparable < StandardError`, because
`noDeclaredBelow` answers `false` when `ancestors?` cannot compute a chain). Recorded because it
is why the `Neg` move was worth making rather than paying the premise: a rung is not worth a
rung.

### State

Syntactic ratchet **178 of 254**, unchanged tier for tier; `expect_validate` mismatches **35**,
unchanged. Corpus agreement **254/254, 0 disagreements**. `checkrungs` **177/177 hand
derivations + 148/148 negative controls** (three new, one per §F20 shape, each confirmed
genuinely type-stuck by the real semantics). Semantic ratchet **48 of 83** (`JudgeSeq` 4/4).
`Denote/Examples.lean` green, `lake build` clean, no `sorry`, every `#print axioms` a subset of
`propext`/`Classical.choice`/`Quot.sound`. Changed: `Ratchet/{Judge,Validate,Rungs,
Proof/ChkSound}.lean`, `CheckRungs.lean`, `Denote/{Adequacy,Sanity,Rules}.lean`,
`Denote/Sem/{Judge,State,Frame,Narrow,NarrowState}.lean`, a new `Denote/Sem/Down.lean`, and
fourteen files under `Denote/Rules/`.

## Clink 62 (2026-09-10) — **`BuiltinsSeal` proved**, the eighteenth stall point closed, and §F22. **178 rungs / 254, 48 of 83 rules**

**The ladder did not move, and that was known before the session started.** All 35 remaining
rules were re-audited independently against `Denote/Sem/notes.md`'s census, and the census holds:
six candidates were checked by hand and every one is behind a named layer or a stated falsity
(`defStmt`'s `StateOk κ` conjunct asks `DefsOk` for the entry `defineMethod` just replaced;
`casgn`/`cpathAsgn` behind the seventeenth stall point *and* §F22 below; `if'`/`ifNoElse` behind
the locals layer *and* the eleventh; `while'` and the 22 call rules behind jump-freeness at the
**run** level, which no syntactic conjunct supplies; `callAsm` behind `AsmsOk`'s `DenAll` at the
call machine, which is the seventh stall point's remnant and false; `prim` behind ~200 rows).
So the session went at the layer `HANDOFF.md` names as the resume point.

### `found-issues.md` §F22 — a third reason `Judge.casgn`'s obligation is false

Found by measuring `constAsgnOk` rather than by reading it. Its guard refuses a rebinding only
for names the *tables* describe — a recorded constant at a different type, a declared class, one
of nine `builtinClsNames`, or an `excName?` — and **`Regexp` is in none of them** while
`Judge.regexpLit` concludes `.cls "Regexp"`. Since `denM (.cls n)` is `isAName`, which resolves
`n` through `constLookup`, `Γ = [("r", .cls "Regexp")]` plus `Regexp = "s"` falsifies `EnvOk` at
the post-machine. Not reachable — every other producer of a nominal `Ty` is inside the guard, and
rebinding the constant `Regexp` is behaviourally inert — so it is an obligation falsity, not a
wrong answer. **It is §F10's pattern read from the assignment side**, and the second of §F22's two
candidate repairs (identity-keyed nominal arms, which `Ty.inst`'s `isExactInst` already half-is)
would close both. Recorded, not fixed: `casgn` needs the cref *and* one of these, so it is two
fixes away rather than one.

### The layer: **`BuiltinsSeal` is proved**

`Denote/Sem/BuiltinsCap.lean` + one module per dispatcher. **`CapMono h h'`** — the heap's
capture edges did not grow — with `Sealed.of_capMono`/`FramesWF.of_capMono` discharging
`builtins_run_seal`'s two remaining hypotheses from it. **All six dispatchers are proved and
axiom-clean** (19/48/3/7/5/5 s), and `BuiltinsCapRun.lean`'s `builtinsSeal : BuiltinsSeal` plus
`builtinsFramesWF` join them to `FrameLocal.lean`'s frame half. **The eighteenth stall point is
closed: `Sealed` survives `Builtins.run`.**

**Two decisions that were not forced.**

* **`CapMono` is existential in the object id**, not keyed to it. The id-keyed version is
  *refuted* by `Object#dup`: `dupObj` pushes a fresh object carrying the source's payload, so
  `p.dup` on a Proc puts the same edge at a new id. `Sealed.clos` at the source discharges it, so
  the existential form is both true and exactly what `Sealed`'s clauses consume. Rejected
  alternative: keep the id-keyed form and special-case `dup` — which would have been a claim about
  one builtin standing in for a claim about the heap.
* **`CapAt`'s class arm is keyed on `methodOf`** — the *first* entry of a name, which is what
  `methodIn` reads — not on membership in `cp.methods`. The membership form is easier to establish
  and `Sealed.meth` **cannot consume it**, since that clause constrains only the first match. The
  sixth stall point's rule (*state the component over the lookup function*) one layer down.

**The cost was tactics, not lemmas, and that is the transferable part** (`Denote/Sem/notes.md`
§The second walk, seven measurements). `FrameLocal.lean` closes the same 600 arms in 89 s; the
first version of this walk had not finished in 35 minutes, and `sample` on the live process
diagnosed it — 60 % in `whnfImp`/`tryHeuristic`/`reduceMatcher?`/`getStuckMVar?`, i.e.
unification against stuck metavariables. The governing rule: **put the arm's shape in a
`rfl`-provable hypothesis and leave the conclusion first-order** (`MCap.push_eq rfl ?_`, not
`CapMono.push` concluding `CapMono ?h ⟨?h.objs.push ?obj⟩`), because that is what makes *failing*
cheap. 35 min → 25 s. Then `split at h` first, not last (two 12 s spikes on the undivided match
over `bid`); `cap_norm` before the closers, which is `KontFrame.lean`'s `frame_simp` technique;
and no `simp` anywhere in the walk — every side condition is a pure term
(`capAt_proc_none`/`capAt_emptyCore`/`capAt_cls_nil`, one per payload iota cannot reduce).

**Also recorded because it wasted a run:** a fold lemma applied through `MCap.trans` **fails
silently** — `foldPair_cap`'s conclusion is `MCap ?p.2 (?l.foldl ?f ?p).2` and `?p.2 ≟ m` is a
projection against a metavariable — so `Regexp#names`' arm looked like a missing case rather than
a mis-applied tactic. `MCap.fold_eq`, which reads the fold off the goal by `rfl`, is the version
that is correct *and* cheap.

**And one measurement error worth confessing**, since it briefly produced a false green: the
sequence script counted errors with `grep "BuiltinsCap$t.lean:[0-9]+:[0-9]+: error"`, and Lean's
format is `error: <file>:L:C: unsolved goals` — so it matched nothing and reported `errors=0` for
modules that had failed. Compounding it, a module that fails is never *imported*, so every
dispatcher after it in the chain also reports zero errors of its own while never being elaborated
at all. Both halves are why `runNumerics` looked like it built five times before anyone had
elaborated it once.

### `runNumerics`: 14 GB and non-terminating → 5 s, and the cause was one tactic

The last dispatcher to fall, and the most instructive. With `simp at h` reachable early it took
the elaborator past **14 GB of proof term without terminating** and `maxHeartbeats` never
tripped. The cause is exact rather than mysterious: on an arithmetic arm `simp` tries to
*evaluate* the `Int`/`Float` literals, while the one thing it was needed for is beta-reducing a
`(fun b => match …) b` arm so `split` can see the match — which **`dsimp only at h` does
definitionally and for free**. Demoting `simp at h` below the unfolds and putting `dsimp only`
in its place closed the file in 5 s, and re-verified the other five unchanged.

Two smaller ordering facts came out of the same measurement, both now in the shared tactic:
`Builtins.withIndex` must be unfolded **before** `split at h`, because it takes a continuation
and `split` otherwise peels the `if`s inside its lambda and strands the arm; and every dispatcher
needs **fall-through** closers for the ones below it in the chain — `runNumerics`' final open
goal was `runStrings bid recv args m = .ok v m'`, i.e. `runStrings_cap h`.

The diagnosis method is the reusable part, since Lean gives no in-file progress (verified: a 5 s
`IO.sleep` between two `#print axioms` markers emits both at the same timestamp under `--json`).
What works is **one module per dispatcher** (live progress from `lake`, plus caching, plus a
smaller closer list each), `set_option profiler true` with a threshold (which found the 12 s
spikes), and **`sample <pid>`** on the live worker, which is what identified the root cause as
unification against stuck metavariables rather than proof search.

### And the closer set for the *next* walk, complete

`Denote/Sem/StepLocal.lean` states the interpreter's per-step target as `Step b m m'` — the
locals claim paired with the invariant, so an arm closes with one `exact`. **Every machine change
`stepFn` performs now has one.** `Step.frameOnly`/`pop`/`setLocal` were already there;
`Step.builtins` (`BuiltinsCapRun.lean`) composes the two walks above with `inRange` riding
`LocalsSame`'s `frames.size` conjunct; and `Denote/Sem/StepInterp.lean` adds the two kinds a
builtin never makes:

* **`Step.alloc`**, stated over **`CapAt`** rather than over `Sealed.alloc`'s two `ReachesB`
  premises — a deliberate choice, so that the `cap_free` closers built for the `Builtins` walk
  discharge it *unchanged*. Restating it in `ReachesB` terms would have been the obvious reading
  and would have needed a second set of closers.
* **`Step.push_free`/`push_clos`/`push_meth`**, covering **all six** `frames.push` sites: the
  four that default `captured` to `none` close with no side condition (which is the L266 `Option`
  paying off), and the two that set it read a `Closure` or a `MethodDef` out of the heap — exactly
  what `Sealed`'s `clos` and L267's `meth` clauses exist for. Two comments in `StepLocal.lean` were
corrected in the same pass: it still named `Sealed.push_method`/`push_block`/`alloc_closure` as
the next step (they are built, under the names `Sealed.push`/`alloc`), and still said
`BuiltinsSeal` was "stated below and **not** proved".

### The layer's target, stated — and the walk's order, measured

`Denote/Sem/StepWalk.lean`: **`StepSound`**, the layer's per-step target, written down as a named
`Prop` *before* any walk under it — the working rule this layer has now paid for three times.
`stepSound_of` decomposes it into `EvalExprSound`/`ApplyKontSound`/`UnwindSound`, one per `ctl`
shape, and takes all three as hypotheses so the decomposition is checkable before a single arm is
closed.

**The first attempt at `EvalExprSound` did not terminate, and that is the finding.** A single
closer-list tactic over `evalExpr`'s 43 arms ran 20 000 000 heartbeats / 8½ minutes to a
`timeout at whnf`. Not the arm count and not the closers: `evalExpr`'s send arms *delegate* — to
`startArgs` (×3), `finishSend`, `enterUserMethod`, `startSuperArgs` (×2), `doSuper`, `startYield`,
`enterClassBody` (×2), `doReturn`, `evalDefined`, `continueArray`, `undefNames`/`undefAliasMiss`,
plus `lookup` and `defineMethod` (×3 each) — and with no `Step` lemma for any of them the tactic
falls through to `split at hstep` and unfolds the whole `Dispatch`/`Send`/`Reflect` layer inside
`isDefEq`. `RubyCore/Proof/KontFrame.lean` did not make this mistake; its order is helpers first,
then dispatchers, then `Builtins.run`, then above. So the companion working rule: **prove the
callees before the callers, because a missing helper lemma does not fail — it inlines.** Third
time measurement order has cost this layer a run, and the first time the failure was
non-termination rather than a false theorem.

`StepEval.lean` therefore holds the **specification** rather than a proof: the five-stage
bottom-up order (`Support`, `Dispatch`, `Send`, `Reflect`, then `evalExpr`, then
`applyKont`/`unwind`), `StepThrough` as the shape each helper lemma takes, and
`stepThrough_builtins` as the one entry already discharged — `Builtins.run` being the bottom of
the chain and done. No `sorry`; the file states what is owed instead of pretending to it.

One closer is recorded as poison for any list that does not need it: `Machine.setLocal` walks the
capture chain *by recursion*, so unifying against `setLocal ?m ?x ?w` unfolds a recursive
function. `evalExpr` never calls it (`.vasgn` pushes an `.asgnK`; the write is `applyKont`'s), so
`Step.setLocal`/`setLocal'` belong to `ApplyKontSound`'s list and nowhere else.

### The re-audit's real conclusion: the ceiling is 76, not 83

The session's last measurement, and the one that should change how the target is read. **Seven
of the 35 remaining obligations are false as stated**, not unproved, and every repair path for
them crosses into `Ratchet/`: `defStmt` (confirmed *by construction* this session — the
obligation is premise-free, `DefsOk κ.defs m'` demands the body `defineMethod` just replaced, so
instantiating `κ.defs = [⟨"foo", [], .int 1⟩]` and running `def foo; "s"; end` refutes it),
`arrayLit`/`hashLit` (seventh stall point's remnant, witness `corpus/242`), `casgn`/`cpathAsgn`
(seventeenth *and* §F22), `if'`/`ifNoElse` (eleventh, with an explicit two-environment witness).

**None of the seven is an unsoundness** — `validate` is right on every one of the reproducers,
which the sixth stall point checked for `defStmt` and §F22 checked for `casgn` — so the standing
"if a `Judge` rule looks genuinely unsound, fix it" exception does not license the edits. They
are false because `Judge` was designed to be *checked*, not *denoted*: four of its rules
re-assert an incoming context or a snapshot the semantics has already invalidated. That is the
sixth, seventh, eleventh and seventeenth stall points saying one thing from four directions.

So the honest form of the target is: **76 of 83 is the ceiling in `Denote/` alone.** The last
seven need the declaration redesign (`Judge` threading a cref, premises on `defStmt`/`casgn`) or
a decision to move `joinT`/`constAsgnOk` and re-run the syntactic ratchet — both `Ratchet/`
work, both already sized in `context-splitting.md` and the stall points, neither blocked on
anything in `Denote/`.

### The locals layer, stage 1–2: 46 theorems, and the four `split` failure modes

After the exit finding was recorded the brief was narrowed to *prove the true facts and ignore
the untrue obligations*, and the layer advanced accordingly. `Denote/Sem/Step{Interp,Walk,Eval,
Support,Dispatch}.lean` hold **76 theorems**, all axiom-clean:

* the full `Step` composite vocabulary with peels — `frameOnly`, `pop`, `setLocal`, `withCtl`,
  `withKont`, `raiseErr`, five allocators, `setGlobal`, `setLastMatchValue`, `heap` (the
  `MCap`-shaped one that subsumes every heap change), and `push_free`/`push_clos`/`push_meth`
  covering all six `frames.push` sites;
* the two heap transports the push premises need, `procClosure_alloc` and `methodIn_alloc`,
  whose in-range side conditions are **derivable** rather than assumed (`classPayload?`/
  `procClosure?` of an out-of-range read is `none`, because `default.payload` is `.none`);
* `Step.foldPair`/`foldPair'`, the layer's fold lemma and its peel;
* and the helpers: `bindIvar`, `reifyBlock`, `doReturn`, `finishRegion`, `appendKwHash`,
  `callClosure`, `enterHandler`, `eigenclassOf`/`_go`.

`Step.callClosure` is the load-bearing one — the first frame-pusher, and what the closure, block
and `yield` families all route through. `Step.reifyBlock` is the one that shows the seal paying
for its own closures: its `captured` is the current frame, which `FramesWF.nonEmpty` puts on the
stack, so `Sealed.stack` discharges `Sealed.alloc`'s premise.

**A wrong diagnosis, corrected.** Three lemmas were parked on "`split at h` cannot peel
`Interp/`'s chains". One line of `set_option trace.split.failure true` refutes it. The real cause
was a **postponement trap**: `exact absurd hstep (by simp)` looks like a closer but the `by simp`
is postponed, so the `exact` succeeds, that alternative wins the `first`, and the correct closers
never run — surfacing 70 stray `¬ …` goals at the *end*, which reads like an incomplete walk
rather than one bad alternative. Two of the three lemmas fell immediately once it was removed.

**The generalisation worth keeping**, since this layer met all four: `split` fails to *fire* (a
`have`-bound scrutinee — `doReturn`), fires on the *wrong* match (`destructureBind`'s
machine-irrelevant `vals`), is *unnecessary* because a lemma should exist instead (`constSet` →
`CapMono.of_constSet`), or fires correctly but is starved by closer ordering (`callClosure`).
**Only the last was ever an obstruction to the theorem**; the other three are addressing
conventions.

**`destructureBind` then fell**, and its two causes were both addressing rather than semantics:
`split` picks the *first* match it finds, and `vals` — machine-irrelevant, every branch yielding
the same machine — precedes the rest-parameter match the proof needs, so it is resolved by hand;
and the stubborn `∀ o, v = Value.ref o → False` goal was never `split`'s at all but a **side
condition of the conditional equation lemma** `rw [Interp.destructureBind]` picked.
`rw [f.eq_def]` has none. That is tooling lesson 1 biting from a direction it does not mention —
the bare *name* in a `rw` is as wrong as `simp only [f]`, and the symptom reads as an unsolved
case rather than a failed rewrite.

**The `_eq` forms are the other generalisation.** `Step.raiseErr_eq`/`allocArr_eq`/`allocHsh_eq`/
`withKont_eq` move each composite's shape out of its conclusion into a `rfl` hypothesis — the
same change that took the `Builtins` walk from "unfinished after 35 minutes" to 17 s per
dispatcher, which this layer had simply not applied to itself.

**Two helpers remain, both deliberate.** `enterUserMethod` is **one transcription away with no
unknowns**: everything it needs is proved, and three attempts (4M heartbeats, 60M, and every
closer in `_eq` form) establish that what is left is neither a proof nor a budget problem but
`split` on a 135-line body with ten branch points outrunning any closer list — the same
conclusion `KontFrame.lean` reached about the same function. The ~7 conditions want transcribing
as explicit peels. `enterClassBody` is deprioritised rather than blocked: it feeds
`classStmt`/`moduleStmt`, which are declaration-family rules and not among the reachable ones.

### EMERGENCY EXIT INVOKED — 83/83 is unreachable under the stated constraints

Recorded as the clink's conclusion rather than as a remark, because it is a **precondition on
the target** and the next session should not re-derive it.

**The deficiency.** Seven of the 83 obligations are *false as stated*, not unproved:

| rule | witness |
|---|---|
| `defStmt` | the obligation is **premise-free** (`#print` it), its conclusion carries `StateOk κ Γ I m'`, and `DefsOk κ.defs m'` demands the body `defineMethod` just **replaced**. Instantiate `κ.defs = [⟨"foo", [], .int 1⟩]` at a conformant machine, run `def foo; "s"; end` |
| `arrayLit`, `hashLit` | seventh stall point's remnant — a later element can mutate an earlier one; `corpus/242` |
| `casgn`, `cpathAsgn` | seventeenth stall point (`ConstScopeOk`, cref) **and** §F22, independently |
| `if'`, `ifNoElse` | eleventh stall point — `joinEnv` synthesises a `Ty.sameAs` neither branch promised |

**Why it is terminal rather than hard.** Every repair is a change to `Judge`: a premise on
`defStmt`, a cref recorded in `Ctx`, a purity premise on `arrayLit`, or a move to
`joinT`/`constAsgnOk`. That is the `context-splitting.md` step-3 class of change — the judgment's
signature, all 178 hand derivations, and the corpus gate — which this repo has done once and
recorded as a whole clink. The session's brief was **"do not modify `Ratchet/`"**, and the
standing exception ("if a `Judge` rule looks genuinely *unsound*, fix it") does **not** reach
these seven: `validate` answers correctly on every reproducer, which the sixth stall point
checked for `defStmt` and §F22 checked for `casgn`. So they are false for a reason that is not
unsoundness and cannot be repaired inside the permitted edit surface.

**The ceiling is 76 of 83 in `Denote/` alone.** Reaching 83 needs a decision that is not a
proof: either lift the constraint for those seven rules and accept the re-run, or re-target the
ladder at 76.

**What is *not* the reason.** The 26 rules behind the locals + call layer are ordinary work, and
this clink advanced that layer substantially (`BuiltinsSeal` proved, `StepSound` stated, the
closer vocabulary complete, stages 1–2 begun). The exit is not "this is hard"; it is "seven of
the obligations are false and the fix is outside the brief".

### State

Semantic ratchet **48 of 83**, unmoved — `BuiltinsSeal` is a layer, not a `Judge` rule, and
nothing here claims otherwise. What it unblocks is the *next* step of the locals layer
(`Sealed.push`/`pop`/`alloc_closure` at the interpreter's frame pushes, `ClosuresOk`'s exactness,
then the `stepFn` walk), which is still several clinks from any rung. Syntactic ratchet **178 of 254**, unmoved tier for tier;
`expect_validate` mismatches **35**, unchanged. `checkrungs` **177/177 hand derivations +
148/148 negative controls**. `lake build` clean, no `sorry`, every `#print axioms` a subset of
`propext`/`Classical.choice`/`Quot.sound`. **`Ratchet/` untouched.** Added:
`Denote/Sem/BuiltinsCap{,Regex,Modules,Collections,Strings,Numerics,Objects,Run}.lean` and
`Denote/Sem/{StepInterp,StepWalk,StepEval}.lean`. Changed:
`Denote/Sem/notes.md`, `Denote/Sem/StepLocal.lean` (its "stated and unproved" note and its
stale next-step list), `found-issues.md` (§F22), `AGENTS.md`, `HANDOFF.md`.

## Clink 63 (2026-09-10) — **`enterUserMethod` proved**, the nineteenth stall point, and stage 2's helpers. **178 rungs / 254, 48 of 83 rules**

**The ladder did not move, and it could not have.** All 35 remaining rules are behind the locals
+ call layer (26), `PrimSig` row by row (1), the declaration redesign (1) or a stated falsity (7,
clink 62's exit finding — unchanged and unrepairable inside the brief). So this session did the
layer's own work, at the resume point `HANDOFF.md` names, and the headline is that **the helper
three previous attempts parked is proved**.

### `Step.enterUserMethod`, and why the parked diagnosis was half wrong

`Denote/Sem/StepAct.lean`. The previous entry's prescription was *transcribe the ~7 conditions as
explicit `by_cases` peels*; that was measured this session and **does not work**, for a reason
that is now `Denote/Sem/notes.md`'s **nineteenth stall point**: `Interp.enterUserMethod` threads
the machine through nine `let`s, the activation push is a flat record literal whose **nine fields
are each a projection of the pre-push machine**, and so any tactic that touches the body produces
~1200 lines of hypothesis with every intermediate machine written out nine times. Both ways out
are then closed: a goal-side peel leaves `?mid` under a projection (clink 62's
`MCap.push_trans_eq` failure, arriving where the vocabulary was thought complete), and
`generalize … at h` **cannot name the machine either** — every machine-producing subterm is
guarded by a `match`, a hand-written `match` elaborates to a *fresh matcher constant*, and
`generalize` then abstracts nothing and **reports no error**. The silent no-op is the trap worth
recording: it reads as "the subterm is not in the hypothesis" rather than "your pattern is a
different constant".

**The fix is a mirror gated by `rfl`.** `enterUM` is the same function with its five
machine-touching stages given names (`Act.restBind`/`kwrestBind`/`destrBind`/`actPush`/
`actLocals`), and `enterUM_eq : Interp.enterUserMethod … = enterUM …` is `rfl` — fidelity is a
kernel check, so a transcription error is a build failure rather than a semantic gap. With the
stages named, every machine in the walk is an argument of a named callee, the goal determines it
first-order, and **the walk closes in 18 s** with a six-line closer list. `rfl` itself costs 12 s
(and needs 4M heartbeats; 200k is not enough).

**A decision that was not forced: mirror rather than refactor the model.** Factoring
`Interp/Dispatch.lean` itself is the same change one file lower and is arguably *more* correct —
that file's header claims each helper "performs one transition" — but it breaks
`RubyCore/Proof/KontFrameDispatch.lean`'s `enterUserMethod_frame`, which `stepFn_frame` and hence
the **climbed** `Judge.vasgn` rung sit on. A model edit whose blast radius is the ladder, against
a mirror that costs one `rfl` and no re-verification: the mirror wins. Rejected alternative also
recorded: proving the prefix's `frames`-equality and pushing at the *entry* machine's facts — it
turned out to be unnecessary, because every premise `Sealed.push` needs is read at the
intermediate machine, where `Step` already hands back `Sealed`/`FramesWF`.

### `PreAct` — the transport the activation actually needed

`Step` alone cannot carry an activation's push: the `MethodDef` is read out of the heap at the
*caller's* machine and pushed at a machine three allocations later. **`PreAct b m m'`** is `Step`
plus the two heap facts a push reads — every installed method is still installed
(`Sealed.meth`/`enterUserMethod`) and every Proc is still there (`Sealed.clos`/`callClosure`) —
with `refl`/`trans`, the two allocators, `appendKwHash`, both folds (`List` and `Array`) and
**`PreAct.destructureBind`**, which is `Step.destructureBind`'s structure verbatim one relation
up. Stated over `methodIn` (the lookup) and not over membership in `cp.methods`, the sixth stall
point's rule and clink 62's `CapAt` decision for the third time.

### The six `methodIn` bridges, and stage 2's remaining helpers

Every caller of `enterUserMethod` holds its `MethodDef` in a different currency, so each needs a
bridge to the heap fact: `lookup` (receiver-keyed), `methodOn` (class-keyed), `lookupAbove` (the
block fallback), `superFound` (`super`), `userInit?` (`Class#new`) and `moduleHook` (the mixin
hooks). All six are the same walk over one class's own table, so they cost one arm lemma
(`methodIn_of_arm`) and one `firstM` lemma; they are `[propext]`-only.

Then the helpers themselves: **`Step.missNoMethod`**, **`Step.visError`**, and the native
block-iterator trio **`Step.iterStep`/`startIter`/`tryIterator`** — the last of which is where
`PreAct`'s *closure* half pays for itself, because `Hash#each` allocates one `[k, v]` array per
entry **before** the loop starts and the block's Proc fact has to cross that fold.

**And a third costume for the ordering rule** (§The second walk item 3): a `callClosure`/
`iterStep` peel that takes the `Step` argument, or the closure fact, *before* the `.next m'`
hypothesis unifies `?mid` with the outer machine `m` and then rejects the real one. The peels
therefore take **the hypothesis first**. This is the third time in two clinks that the fix was
argument order rather than a lemma.

### `tryMixin` and `defineAttr` — done in the same session, and they cost *closer shape* again

Both landed after the above was written, so **stage 2 is complete except `enterClassBody`**
(deprioritised: declaration family). Neither needed a semantic idea; all three costs were the
shape of the hypotheses a closer can consume.

* **`CapMono.defineMethod`** — installing a method adds no capture edge when the installed
  method's captured frame is one the heap already reaches. Vacuous for every writer but
  `define_method`. The content is the *other* names: `defineMethod` prepends and filters the old
  entry out while `methodOf` reads the first match, so a name other than the one written has to
  be shown to resolve exactly as before (`find?_filter_ne`) — installing a method can only
  **hide** an edge. `CapMono.set_gen` (the existential form of `CapMono.set`) is what a
  `define_method` body needs, because its edge is carried by the *Proc*, not by the class.
* **The `E` forms, and this is the transferable half.** `refine`/`exact` **refuse to postpone an
  implicit argument** that a later `rfl` would determine — *don't know how to synthesize implicit
  argument `cp`* — so `CapMono.setClassPayload_methods` cannot be used inside a closer list,
  where the payload is available only as a `split`'s inaccessible hypothesis. Restating the pair
  as one existential and discharging it `⟨_, by assumption, by rfl⟩` fixes it, and the **`by`**
  on the `rfl` is load-bearing: a `rfl` *term* there is elaborated first and assigns the wrong
  payload. `methodIn_of_moduleHookE` is the same move for the hook lookup, whose machine is one
  `kont` push behind the activation's.
* **A fourth costume for the ordering rule.** A peel supplied as an *argument*
  (`Step.withCtl' (Step.heap' … rfl rfl ?_) _`) lets the `rfl`s unify the *target* machine with
  the intermediate one — it type-checks a different statement's shape and then fails; supplied as
  a **separate `refine`**, the goal fixes the target first. That is what closed `extend`.

`Step.defineAttr` also needed `Step.foldPairL`, the fold whose accumulator carries the machine
**first**. `Step.tryMixin` closes in 5 s, `Step.defineAttr` immediately.

Above them, `invokeDispatch`
now has everything it needs *except* `dispatchMiss`, which routes through `tryReflect` — the whole
stage-4 reflection dispatcher — so the dispatch spine cannot be closed before stage 4. That is
the honest next boundary, and it is not a new obstruction: it is the bottom-up order
`StepEval.lean` specified, with one more layer than the ladder's optimism assumed.

### Stage 4, most of it: thirteen `reflect*` helpers and two facts about the relations

`Denote/Sem/StepReflect.lean`. `dispatchMiss` routes through `tryReflect`, so this file is on the
reachable path and not a corner. **Thirteen of the fifteen helpers are proved**, axiom-clean:
`instance_variable_get`/`_set`/`instance_variables`, `const_get`/`const_set`,
`method_defined?`/`respond_to?`, `singleton_class`, `throw`, `attr_*`, `catch`, the `*_eval`
family, `define_method`/`define_singleton_method`, `alias_method` and
`remove_method`/`undef_method`. Most are queries and fall to one shared closer list; the four
that write the method graph or push a frame needed one heap lemma each
(`CapMono.defineMethod_clos`/`_copy`/`setClassPayload_filter`, `methodIn_defineMethod`).

**Two corrections to the layer's relations, both found by the type checker rather than by
thinking:**

* **`PreAct` is *false* across `defineMethod`.** Its method conjunct says every installed method
  is still installed, and `defineMethod` **replaces** — a redefinition drops the old entry. So the
  visibility and removal walks are `Step`, not `PreAct`, and what their second write needs is not
  the old fact transported but the **new** one established (`methodIn_defineMethod`: a method just
  installed is installed). The checker refused a `PayKeep` for a `defineMethod` and that is what
  surfaced it.
* **`PayKeep` is the right interface for `eigenclassOf`.** "The heap only grew" is false of it (it
  writes the attachee's `eigen` field, an object already there), but "every payload that was there
  is still there" is true — and payloads are all `methodIn`/`procClosure?` read. `PayKeep` is
  therefore what transports both across it, and `PreAct.eigenclassOf` is proved through it.

**The ordering rule got its fifth and sixth costume**, and by now it is the layer's dominant cost:
a composition whose *intermediate* carries an argument the goal does not mention
(`(eigenclassOf m ?o).2`) must be supplied as **one `exact` term**, since a `refine … ?_` never
determines `?o`; and a peel whose target is a record update (`m.setCurrentFrame ?fr`) must be
reached by a **separate `refine`**, or the `rfl` side conditions unify `?fr` with the *unmodified*
frame and the closer proves the wrong statement. Also worth recording: a hand-written `match` in a
lemma's **premise** is fine (`exact` checks up to defeq, and two matchers for the same match are
defeq) — it is only `rw`/`generalize`/`simp only`, which match *syntactically*, that the fresh
matcher constant defeats. That distinction is the nineteenth stall point's fine print.

**`reflectVisibility` then fell too, and its measurement is the clink's sharpest one.** It was
parked for one attempt on "its four leaves need hand peels" — right and insufficient: with the
leaves peeled the walk still **timed out at 1M heartbeats (28 s)**. The cause is clink 62's rule
for the fifth time: a closer whose *conclusion* carries the shape
(`Step b m (visRun (eigenclassOf m ?o).2 …)`) is expensive **to fail**, since unification unfolds
the callee against a machine-sized term at every goal it does not close. `Step.visRun_eq` moves
the shape into a `rfl` hypothesis: **28 s timeout → 2.3 s**. So **stage 4 is fifteen of fifteen**,
and with it **`Step.tryReflect` and `Step.dispatchMiss` are proved — the miss path is closed**,
which is what `invokeDispatch` was waiting on.

### …and `invokeDispatch` is *not* closed, for a reason worth a stall point: the twentieth

`Builtins.run` answers **four** ways, and three carry a machine (`.ok v m`, `.err cls msg m`,
`.throwV v m`). The layer's 600-arm walks — `builtins_run_locals`, `builtins_run_cap`,
`Step.builtins`, and therefore the eighteenth stall point's "`Sealed` survives `Builtins.run`" —
are all stated over **`.ok` alone**. So a builtin that *raises* leaves the locals layer with
nothing to say, and every dispatcher's error path is unreachable. Not a design problem: it is a
second pass of the same two walks, and `Denote/Sem/notes.md`'s twentieth stall point prices the
three ways to pay for it (generalise over the result and re-run the existing tactic; two more
instantiations; a `BRes`-level relation). **The finding is that it was invisible** — `Step.builtins`
reads like "the layer is done".

**And it was sized by measurement rather than by guess**, which changed the prognosis: the
existing `builtin_arms` tactic closes `runObjects`'s **`.err`** walk **unchanged, in 9 s**,
leaving **two** goals — both helper delegations. The tactic transfers because its closers act by
`cases h`, and an arm that answers `.ok` meets a `.err` hypothesis as a *constructor mismatch*
that `cases` closes by no-confusion. So the six dispatchers are refutations almost everywhere and
the real work is a dozen **helper** lemmas (`putsImpl_locals`, `regexApply_locals`,
`scanAll_locals`, `splitBy_locals`, `splitOn_locals`, `subst_locals`, `runRegex_locals`) getting
outcome-generic statements. A five-dispatcher batch left running to price the big two
(`runStrings`, `runNumerics` — the pair that cost 48 s and a 14 GB blow-up on the `.ok` side) had
**not finished at 20 minutes**, so the cost sits exactly where it sat before. Recorded in the
twentieth stall point; not attempted further this session.

**Superseded note, kept because the diagnosis was half right: `Step.reflectVisibility`.** Its walk (`Step.visRun`,
`Step.visStep`, `Step.foldOpt`) and every heap lemma under it **are** proved; what is left is the
caller's four leaf shapes, which a closer list cannot take — three arrive with the hypothesis
wrapped in an `And` (`simp` turns `if c then some x else none = some y` into `c ∧ x = y`) and one
of those does not `subst`, while the `*_class_method` leaves need the eigenclass composition as a
single `exact`. The remedy is `enterUserMethod`'s: peel `recv`, the `names.length` check,
`names.isEmpty`, `classMeth` and `visOk` by hand. **`tryReflect` waits on it**, and so does
`dispatchMiss`.

### State

Semantic ratchet **48 of 83**, unmoved — nothing here is a `Judge` rule, and the layer that gates
26 of them still needs stages 2–6 plus jump-freeness plus the `frameK` decomposition. Syntactic
ratchet **178 of 254**, tier for tier; corpus agreement **254/254**; `expect_validate` mismatches
**35**; `checkrungs` **177/177 + 148/148**. `lake build` clean, no `sorry`, every `#print axioms`
inside `propext`/`Classical.choice`/`Quot.sound`. **`Ratchet/` untouched.** Added:
`Denote/Sem/StepAct.lean`, `Denote/Sem/StepReflect.lean` (stage 4 whole, plus `tryReflect` and
`dispatchMiss`). Changed: `Denote/Sem/StepSupport.lean` (the two `Machine` folds,
`PreAct` and its lemmas), `Denote/Sem/StepDispatch.lean` (the bridges, the helpers, method
installation and the mixins; its
`enterUserMethod` prose was a status note and is now a pointer), `Denote/Sem/notes.md`
(nineteenth stall point), `AGENTS.md`, `HANDOFF.md`.


## Clink 64 (2026-09-10) — **§F23: a reachable soundness bug, found by reading an obligation**. **178 rungs / 256, 48 of 83 rules**

The session's last hour, and the only part of it that moved a number. Written as its own clink
because it is the semantic ratchet doing the job it exists for: **the bug was found by reading
`Obl.Judge.while'`, not by search.**

### The bug

`Judge.while'`'s premises are `Γc = Γ` and `Γb = Γ` — the condition's and the body's **outgoing**
environments — and a `next` leaves the iteration *in the middle*, at an environment neither
premise mentions:

```ruby
i = 0; x = 1
while i < 2
  i = i + 1; x = "s"
  next if i == 2      # leaves with x : String
  x = 2               # ...which is why Γb = Γ holds anyway
end
x + 1                 # CRuby: TypeError. `validate` said Integer.
```

**Reachable** — `validate` certified it — and the same hole sits one rule over in
`Judge.iterBlock`, whose `capIntact` is read at the block body's outgoing environment too
(`[1,2].each { |y| s = "a"; next if y == 2; s = 1 }; s + 1`). Both are corpus rungs now
(`while-next-escapes-unsafe`, `iter-block-next-escapes-unsafe`, tier 16), both `unsafe_program`,
and the Lean model agrees with CRuby on both (corpus agreement **256/256**).

### The fix, and three decisions that were not forced

A premise `nxtPrefixOk body = true` on both rules: **a `next` may only occur before anything has
assigned**, so the environment at the escape *is* the body's incoming one — which is exactly what
the outgoing premise already pins. Conservative, and it keeps every climbed rung.

* **`asgnFree`, not `noLocalAsgn`.** The first version reused the existing `noLocalAsgn`, which is
  a *whitelist of narrowing-condition shapes* and answers `false` for `next` itself — so it
  rejected `ctl-next`, a climbed rung, and the build said so. `asgnFree` asks the honest question
  (a `vasgn`, a `for` target, or a block body writing a captured local, anywhere) and keeps it.
  **Rejected alternative**: requiring the body to be `next`-free outright, which is simpler and
  costs `ctl-next`.
* **An `autoParam` (`:= by rfl`)** for the premise, so the **27** hand derivations that predate it
  discharge it the way they would have written it, with no re-editing — and a derivation whose
  body *does* `next` after an assignment fails to elaborate, which is the point. **Rejected
  alternative**: editing 27 sites by hand, which is the same change with a worse failure mode.
* **The precise fix was rejected on price**: the environment after the loop is really the *join*
  of the body's normal exit and every `next` exit, and computing it needs the judgment to thread
  an escape environment — a signature change of the `context-splitting.md` step-3 class. The
  conservative premise is sound and costs nothing measurable.

**The whole ripple of a `Judge` premise is two lines**, and that is worth knowing: `Ratchet/Proof/
ChkSound.lean`'s `while'` and `iterBlock` arms destructure one more conjunct out of `validate`'s
guard. Nothing else moved.

**Known limitation, inherited not introduced**: `asgnFree` is syntactic, so a `next` after a call
to a closure that assigns a captured local is still accepted — §F13's hole, the fifteenth stall
point's, unchanged.

### …and the same question at `break`, which is a negative result worth pinning

§F23's reasoning applies verbatim to `break` — it leaves the loop (or, in a block, the call) where
`next` leaves the iteration, and both rules read their premise at the body's end just the same.
Both witnesses were written and run against CRuby (both `TypeError`), and **`validate` rejects
them already**: it has no rule that types a `break` in either position. So `found-issues.md` §F24
is a *negative* finding, and the two programs are on file (`while-break-escapes-unsafe`,
`iter-block-break-escapes-unsafe`) as **the regression pin for the day a `break` rule is
written** — `nxtPrefixOk` says nothing about `.brk`, and those rungs will say so.

### The method note, which is the part that generalises

Three doors were asked about, and the *controls* are what separate the answers: §F23 (`next`) was
a real bug — witnesses certified, fix applied, both now rejected; §F24 (`break`) is a real
**negative** — the witnesses are rejected *and* their break-free controls validate `true`, so the
rejection is caused by the `break`; §F25 (`raise`) is an **absence** — the witness is rejected,
but so is the raise-free control, because `begin`/`rescue` is not typed at all yet. Running the
control costs one `#eval` and it is the whole difference between "checked" and "assumed". All
three are corpus rungs, because the two negatives are the regression pins for the day a `break`
rule or a `Judge.begin'` is written — `nxtPrefixOk` covers neither.

### State

Semantic ratchet **48 of 83**, unmoved, denominator still 83 (a premise is not a rule). Syntactic
ratchet **178 of 259** — the two new rungs are permanent negatives, so the climbed count is
unchanged and the denominator grew by the two witnesses; `expect_validate` mismatches **35**,
unchanged; corpus agreement **256/256**; `checkrungs` **177/177 + 148/148**. `lake build` clean,
no `sorry`, axiom-clean. Changed: `Ratchet/Judge.lean` (`nxtFree`/`asgnFree`/`nxtPrefixOk` and the
two premises), `Ratchet/Validate.lean` (the two guards), `Ratchet/Proof/ChkSound.lean` (two arms),
`scripts/generate_corpus.py` + `corpus/` (four witnesses: §F23's two, which the fix now rejects,
§F24's two and §F25's one, which were already rejected), `found-issues.md` (§F23, §F24, §F25),
`AGENTS.md`.
**This is the one edit to `Ratchet/` this session, and it is the standing exception: a genuinely
unsound rule, reported, witnessed in the corpus, then fixed.**

## EMERGENCY EXIT INVOKED (2026-09-10, clink 64) — **the ladder's unit of measurement and the work's unit of delivery do not match**

Recorded in the brief's own form, because three consecutive sessions have now ended at the same
number while doing substantial, verified work, and the reason is structural rather than a matter
of effort.

### The deficiency

`semladder` counts **one rule at a time**, and the brief says to discharge them *in the
inductives' own constructor order*. For the 35 that remain, that unit does not exist:

| kind | count | the unit the work actually has |
|---|---|---|
| false as stated, repair crosses into `Ratchet/` and is **not** an unsoundness | 7 | a `Judge` signature change (cref threading, purity premises, `joinT`) — clink 62's exit, unchanged |
| true, behind the locals + call layer | 26 | **the whole layer**. `AGENTS.md`'s own words: they "come out at the end of the whole layer, not in stages" |
| true, behind `PrimSig` row by row | 1 (`prim`) | ~200 conformance facts, two per row |
| true, behind the declaration redesign | 1 | `Ctx` recording the cref |

So a session that starts here reads 48/83 at the end **unless it finishes the entire layer**, and
the layer is not a session: it is six `Interp/` stages, a run-level induction, jump-freeness, and
the `frameK` decomposition. This session completed stages 2 and 4 of six, proved the helper three
previous attempts had parked, closed the lookup-miss path, and found that a *third* prerequisite
had been silently missing (the twentieth stall point). None of that is a rung, and none of it
could have been.

### The evidence that this is structural

| clink | work delivered | ladder |
|---|---|---|
| 62 | `BuiltinsSeal` proved (six 600-arm walks), `StepSound` stated, the closer vocabulary | 47 → 48 |
| 63 | `enterUserMethod` (the nineteenth stall point), stage 2 complete | 48 → 48 |
| 64 | stage 4 complete, `dispatchMiss`, the twentieth stall point, **§F23 fixed** | 48 → 48 |

Three sessions, three stall points found and two of them *closed*, and one number that cannot
move. A ratchet whose number is insensitive to three sessions of correct work is not measuring
the work.

### What would fix it — and the cheapest option is a *ladder* change, not a proof change

1. **Conditional rungs.** Let an obligation be discharged *modulo a named layer hypothesis* —
   `StepSound → Obl.Judge.if'` is a real, checkable theorem, and the layer hypothesis is already
   a named `Prop` (`Denote/Sem/StepWalk.lean`). The ladder then counts what is actually being
   built, the composition is one `exact` per rule once the layer lands, and nothing is claimed
   that is not proved. **Most of this session's work would have counted**, and no proof would
   have been weaker.
2. **Lift the no-`Ratchet/` constraint for the seven false obligations**, which is the
   `context-splitting.md` step-3 class of change and wants its own clink (all 178 derivations,
   the corpus gate).
3. **Re-target the ladder at 76** and measure layer progress on a second axis.

(1) is recommended: it is a change to `Denote/Ladder.lean`'s counting rule, it is honest, and it
is the only one that makes the next session's number move for the right reason.

### What is *not* the reason

Not difficulty, and not the model: §F23 this session is a **reachable soundness bug found by
reading an obligation and fixed** — the ladder's stated purpose, delivered. The exit is about the
measurement, not about the enterprise.

---

## Clink 65 (2026-09-11) — **the judgment is now generated from the proofs**: `Denote/Clink/`, and the EMERGENCY EXIT answered as a design change rather than a counting change

Clink 64 invoked the emergency exit on the grounds that *the ladder's unit of measurement and
the work's unit of delivery do not match*, and recommended a **ladder** change: count
conditional rungs. That recommendation is not what was done, and the reason is worth
recording, because the exit's diagnosis was right about the symptom and wrong about the cause.

### Why "count conditional rungs" was the wrong repair

The exit's premise was that 48/83 undercounts delivered work. True. But the deeper problem is
what the *denominator* was doing there at all: it was the list of rules **authored**, and the
gap between it and the numerator stood for rules that were already in the judgment, already
reachable by `validate`, and already certifiable — with no justification. Three consequences
that no counting change can touch:

1. `Judge.if'` types every conditional in the corpus and has no semantic proof. Under any
   counting scheme that is a *number*; what it needs to be is a *refusal*.
2. **Seven of the 35 remaining obligations are false as stated** (§F19/§F23/§F24 and clink
   62's exit). A rule list containing a false rule cannot have an adequacy theorem at all, so
   the terminal step (`AdequacyHyps → AdequacyTarget`) was not merely undone — it was
   unreachable in principle, and counting differently does not change that.
3. The only theorem tying the 48 proofs to anything was that same 83-case mutual induction.
   Partial credit is available for each *rung* and unavailable for the *theorem*, which is the
   old `Denote/Adequacy.lean`'s own observation — and it means the 48 proofs, for three
   sessions, implied nothing.

So the repair is to invert the dependency: **generate the judgment from the proofs.**

### The device, and why it is this one

A rule is authored once with the family abstracted (`form : Fam → Prop`), and the two readings
are that one `form` instantiated at two families — `synFam` (the `Judge` relations) and
`semFam` (the `SemJudge` ones). `Clink` bundles them with the semantic one **as a proof
field**, so the pairing is enforced by typing rather than by a report:

```lean
structure Clink (S T : Fam) where
  name : String
  form : RuleF
  syn : form S        -- the `Judge` constructor
  sem : form T        -- the proof; this field is the gate
```

This is `Denote/Sem/Obligations.lean`'s substitution reified. That command replaced one
*constant* with another inside the constructor's type; `register_clink` replaces it with a
**projection of a parameter**, which is the same operation made first-class, and is why one
authored rule yields both readings with no possibility of drift. Three choices inside it
that could have gone another way:

**`form` is derived, not accepted.** `register_clink` reads the constructor out of the
environment and computes `form`; it does not take a hand-written one. A hand-written `form`
would be a *third* transcription and could disagree with both readings — exactly the failure
`Obligations.lean` was written to prevent ("83 chances to weaken an obligation by a typo").
`Controls.lean` §4 exhibits a hand-written `form` once, only to check by `rfl` that it equals
the derived one.

**`withLocalDeclD`, not a de Bruijn index.** `Expr.replace` visits subterms under binders, so
substituting `bvar 0` for `Judge` would be correct at the outermost depth and wrong at every
other. An `fvar` is depth-independent and `mkLambdaFVars` puts the binder back. (This is the
same class of mistake as clink 63's `generalize`-abstracts-nothing, and the same fix: name the
thing rather than count to it.)

**`JudgeC` is impredicative, not inductive.** The judgment generated by a registry cannot be a
Lean `inductive`, because an inductive's constructor list is fixed at declaration and the
registry grows. So it is the Böhm–Berarducci encoding, available because `Prop` is
impredicative:

```lean
JudgeC R |>.judge … := ∀ F : Fam, Closed R F → F.judge …
```

Considered and rejected: **rules as first-order data** (`{premises : List Jdg, conclusion :
Jdg}` with `Derivable` an inductive over a `List Rule`). It works and is the textbook
encoding, but it requires every rule's premises and side conditions to be *re-encoded* as
data — 48 hand transcriptions, and the third-transcription problem again. The impredicative
encoding takes the constructor's own type as the rule, which is what makes the whole thing
cost one command instead of a file per rule.

### What it buys, each checkable

* **`registry_sound` is unconditional and one line** — instantiate `F := semFam`, discharge
  `Closed` from the clinks' `sem` fields. It holds at every registry size and **held at size
  1**. Axiom-clean. The three-session drought was a drought of *statements*, not of proofs:
  the same 48 proofs now imply something, today.
* **No denominator.** An unregistered rule is not an undischarged obligation; it is not a
  rule. `lake exe semladder`'s right-hand column is coverage — what `JudgeC` cannot type,
  which bounds what a certificate can be checked against soundly — and the exit code is
  non-zero only if the registry **shrank**. The old exit code was non-zero while rules
  remained, i.e. permanently, which is a light nobody reads.
* **The false-as-stated failure mode is structurally gone.** Seven rules have obligations
  known to be false; there is no step at which they could enter `JudgeC`, because the step is
  a proof.
* **Growth is gated by `lake build`.** `register_clink` refuses a rule with no proof
  (`Controls.lean` §2 captures the refusal with `#guard_msgs`, so the gate going *quiet* is
  itself a build failure), and the 35 legacy unclinked constructors are frozen by name in
  `legacyUnclinked` with a `#guard` that fails if anything not on that list is unregistered.
  Verified by removing `Judge.prim` from that list: the build goes red, naming it.
* **A derivation is a term, polymorphic in `F`** — `hF c hc` *is* the rule, so a derivation is
  a witness that only registered rules were used. No closure lemma, and there cannot be a
  generic one: a Horn rule mentions the judgment **contravariantly** in its premises, so
  `c.form` is not monotone in `F`. Recorded because it looks like an omission and is not.

### The parameterisation, and what it is for

`Clink (S T : Fam)` rather than a fixed pair, per Norm A. The semantic reading is *about to*
be restated — `answer-typed-schema.md` §3.1 replaces `SemJudge` with the answer-typed
`SemJudgeA`, because `SemJudge` has no progress content (`not_semJudgeImpliesStuckFree`) — and
under the parameterised structure that restatement is **a new registry at a new target
family**, not an edit to the mechanism. It also makes the cost of restating honest and
per-rule: a clink whose `sem` field does not carry over stops building, by name, rather than a
report continuing to say "48" about a superseded statement. That is the schema's §6 step 3
("the ladder number will drop, and reporting it honestly is part of the step") turned into a
property of the build.

### Deleted, and what replaced it

* `Denote/Ladder.lean` — the 48/83 report and its `isDefEq` check. The check survives as
  `Clink.sem`'s *type*: enforced at the point of declaration instead of counted in a report.
* `Denote/Adequacy.lean`'s `AdequacyHyps` and its derive command — the 83-conjunction. It is
  `Closed clinks semFam`, proved by `closed_target` in one line for any registry.
* `Denote/Adequacy.lean`'s `StuckFreeTarget` — on `answer-typed-schema.md` §5's delete list
  already; under an answer-typed target it is a consequence rather than a parallel statement.

`AdequacyTarget` stays, with its only consumer now written down
(`semJudge_of_judge_of_adequate`): it is exactly the assumption `Ratchet/Validate.lean` runs
on by targeting `Judge` rather than `JudgeC`, and naming the assumption is how the coverage
column acquired its meaning.

### What this does not do

It does not prove a single new rule, and the registry is the same 48. The reach of the
*checker* is unchanged and still bounded by `Judge`: `Ratchet/Validate.lean` and
`Ratchet/Deriv.lean` both target the authoring surface, so the next piece of work is to point
the certificate checker at `JudgeC clinks` — at which point the 35 uncovered rules become a
reach limit that is visible in the corpus number instead of an assumption in a docstring.

---

## Clink 66 (2026-09-11) — the typed ladder's checker: `check` **returns** the derivation, and the first 18 rungs climb

The goal was the first 18 rungs of the Sorbet-typed ladder with `validate` taking a `Deriv`,
and the constraint was explicit: **do not marry this to `chk`/`Judge`.** Both are met.
`lake exe ratchetd build` reports `LADDER REACH: 18 rungs`, frontier `019-to-s-call`.

### The one design decision that mattered

`check` could have been `Nat → Env → Expr → Deriv → Option (Ty × Env)` with a separate
`check_sound : check … = some … → DJudge …`. That was written first, and abandoned after the
proof skeleton made the cost visible: it is one `induction fuel` with a `split` over a
23-arm match, and **every arm is a place the proof can be weaker than the function.** An arm
whose `none` branch is discharged by `simp` proves nothing about what that arm actually does;
the theorem would be 200 lines of which the load-bearing part is invisible.

So `check` returns the derivation:

```lean
structure Certified (Γ : Env) (e : Expr) where
  ty : Ty
  out : Env
  judged : DJudge Γ e ty out

def check (fuel : Nat) (Γ : Env) (e : Expr) (d : Deriv) : Option (Certified Γ e)
```

Layer 3 of `answer-typed-schema.md` §3 is then not a theorem *about* layer 2 — it is layer
2's **type**, and the oracle is the Lean typechecker. `validateD_typed` is one `match`. This
is `Denote/Clink/`'s `Clink.sem` move one level down: put the obligation in a field and there
is no gap to be weaker across.

Cost of the choice, recorded: `check`'s arms carry witnesses, so they are noisier to read than
`chk`'s; and the return type is dependent (`Option (Certified Γ e)`), so every `match` on the
expression refines it. Lean handled both without help.

### Dispatch is on the expression, not the certificate

Both orders typecheck. Matching `e` first and *requiring* the certificate to be the rule that
concludes about it is the right one, because the alternative lets a certificate choose which
rule to try — the same class of mistake as letting it choose a type. Concretely: everything is
computed from the program and **compared** against the certificate's claim (`prim`'s `recvTy`
and `retTy`, `if`'s `join`, every literal). None is believed.

Worth being precise about why, since soundness does not require it: `DJudge Γ (.int 1) .int Γ`
holds whatever the certificate says, so accepting a certificate that claims `intLit 5` for the
program `1` would be *sound* and would mean the certificate was never read. A checker that
ignores its certificate makes the whole pipeline downstream of `scripts/emit_deriv.py`
unfalsifiable. `Ratchet/DerivControls.lean` has 16 `#guard`s for exactly this, in five shapes:
wrong program, wrong depth (both directions), wrong rule, wrong claimed result type, wrong
claimed receiver type.

### The control that flipped, as promised

The previous commit's `DerivControls.lean` §4 recorded, with a `#guard … = true`, that an
**ill-typed program with a well-shaped certificate was accepted** — `"a" + 1` with a
`String#+` derivation — and said the line would have to be edited the day the typing half
landed. It is now `= false`: `dprim?` has no row for `String#+` at an `Integer`. The positive
control next to it (`"a" + "b"`, accepted) is what makes that `false` about the types rather
than about the row being missing.

### Small, on purpose

`DJudge` has **13 rules** (seven literals, `var`, `vasgn`, `seq`, `prim`, `if'`, plus two list
companions) and `DPrim` has **7 rows** (`Integer#+ - * /`, `Integer#<`, `String#+`, `!` on a
boolean). Two size decisions, each with a reason:

**No `Ctx`, no ivar spine.** `DJudge` is `Env → Expr → Ty → Env → Prop`. The 18-rung fragment
declares nothing, has no `self` and opens no class, so a context would be a field nothing
reads. Copying `Judge`'s `Ctx` — with `afterStmt`, `ctxKept`, `narrowEnvs`, the assumption
table — ahead of a rule that needs it is how the old judgment acquired premises nobody could
justify. The declaration rules will need one; they can bring it.

**7 primitive rows, not 90.** `Sem.Judge.prim` — the obligation that every `PrimSig` row is
true of CRuby — is priced at "~200 conformance facts, two per row" and is one of the 35
unproved rules. A table that grows a row at a time has an obligation that grows a row at a
time, which is the whole argument for starting again rather than inheriting. The frontier rung
(`019-to-s-call`) is one row away, and that is the shape of every rung from here.

### Reach is a prefix

`MainTyped.lean` reports **ladder reach**: the length of the leading run of rungs whose
verdict equals the recorded `expect_validate`. 18 today. A prefix rather than a total because
that is what "we are at rung N" means, and because the total (75 rungs meet their target,
29 certify) is inflated by rungs that pass out of order — e.g. rungs whose target is `false`
and which the emitter happens to block. `ladderFloor := 18` ratchets it and the exit code is
non-zero if it drops.

### Deleted

`Ratchet/Deriv.lean`'s `derivShapeOk`/`paramNamesMatch`/`supMatch` — the shape-check stub.
Replaced by `check`, which subsumes it: dispatching on the expression *is* the
about-this-program property, and the controls that pinned it are unchanged.

### Not done

No semantic proof for any `DJudge` rule, so nothing here is a `Clink` and the reach number is
coverage of the checker rather than justification. `Ratchet/Check.lean` §5 is the owed list,
ordered by cost — literals/`var`/`vasgn`/`seq` are a reconciliation of index shapes with
`Obl.Judge.*` (already proved), `if'` needs join soundness under `denM`, `prim` needs one
conformance fact per row. §6 states the condition under which `Judge.lean`/`Validate.lean`
get deleted rather than assuming it.

---

## Clink 67 (2026-09-11) — **eight answer-typed clinks**, the first in the project whose hypothesis is an answer rather than a value

Asked, after clink 66, whether any clinks had actually been achieved. The honest answer was
**no** — the registry was still the same 48, every `sem` field predating the session, and
`DJudge`'s twelve rules had none. Two things were wrong and both are fixed here.

### The gate had a hole, and I had walked through it

`Denote/Clink/Registry.lean`'s growth gate ranges over `familyCtors` — `Ratchet.Judge`'s
eight-member mutual family. It has no opinion about any *other* judgment. So clink 66
authored twelve brand-new unproved rules in `Ratchet/Check.lean` and nothing went red, one
commit after building a gate whose entire purpose is "a rule enters only with its proof".
Not a violation of the letter; squarely one of the spirit, and the kind of hole that is
invisible until someone asks.

### Which shape the obligations should be in, and why the 48 were not reusable

The first instinct was to re-index `DJudge` to `SemJudge`'s shape, at which point ten of the
twelve rules would have inherited an existing proof verbatim — `Obl.Judge.intLit` is a
statement about `SemJudge` alone, and `Sem.Judge.intLit` discharges it. **That was the wrong
instinct**, and the correction is the substance of this clink: `SemJudge`'s hypothesis is a
*value*, so `Denote/Sem/NoProgress.lean`'s `not_semJudgeImpliesStuckFree` shows it says
nothing at all about a run that escapes. Inheriting those ten would have been inheriting ten
proofs of the weaker statement and calling the ladder justified.

So the obligations are `SemJudgeA`-shaped instead (`answer-typed-schema.md` §3.1, the
prototype's `PSemJudge` generalised):

* the hypothesis is `runA fuel (evalFrom m e) = .ans a m₀ rest` — an **answer**, not a value;
* the conclusion carries `AnsOk`, whose `esc (.raiseJ exc)` arm is
  `isTypeError m₀.heap exc = false`, i.e. **whether the run reached a type-stuck outcome**.

The two registries are kept separate rather than merged, and that is deliberate: they are
clinks against different statements, and one count would let the weaker launder as the
stronger. `lake exe semladder` prints both, with `dclinkFloor` ratcheting the new one.

### The structural fact that made rule-local proofs possible at all

`evalFrom m e = { m with ctl := .eval (toRuby e), kont := [] }` — it **empties the
continuation**. So every obligation is about a run from an empty continuation, and
`answer-typed-schema.md` §9.2's warning (that `safe_pushK` needs `CatchFree m.kont`, which a
reachable machine can violate, so the answer-typed decomposition is a per-rule tool and not a
whole-machine invariant) does not bite: at an empty base kont the frames a rule pushes are the
only ones there, and those are catch-free by inspection. Worth writing down because the
warning reads like a blocker and is not one at this layer.

### What that bought, and the one lemma that gates the rest

Eight rules proved and registered, axiom-clean: the seven literals and `var`. Each is one
`runA_pure` inversion plus packaging, and the packaging is **smaller** than the value-shaped
twin's — no `Plain` conjunct, one outgoing `StateOk` instead of two. `runA_pure` itself is
shorter than `evals_pure` for a pleasing reason: `evals_pure` needs two steps because
`Interp.run` has to *deliver* the value to the empty continuation before reporting `.value`,
while `runA` stops at the answer point, so one step is the whole run.

The other four — `vasgn`, `seq`, `prim`, `if'` — are behind **one** missing lemma, stated as a
named `Prop` before anything is proved under it (`HANDOFF.md`'s working rule, which
`FrameLocal.lean` paid for twice): `RunAPushK`, the answer-level counterpart of `run_pushK`.
All four evaluate a sub-expression under a pushed frame and the decomposition exists for
`Interp.run` and not for `runA`. One induction gating four rules is a good ratio, and
`Denote/Rules/VasgnAnswer.lean` already measured what it buys downstream: the `esc` clause was
**four lines** against the projection route's twenty-two.

### §F29, and it is the mechanism working

`DJudge.var`'s obligation **did not close**, and the reason was a premise I had dropped when
authoring the rule three hours earlier: `StateOk` supplies `denM (stripAlias τ)`, so at a
`Ty.sameAs` binding the conclusion claims more than conformance gives. That is §F5, on
`Judge.var`, found a second time by the same route. No corpus rung could have found it —
nothing in `DJudge` *produces* an alias, so no reachable environment has one — but
`SemJudgeA` quantifies over every conformant environment, so the hole was a failed proof
rather than a latent bug. Cost of the fix: one premise, one `if` in `check`, and **no ladder
movement** (reach 18 before and after).

### Mechanism changes

`Clink` is now generic in the family **record type** (`{F : Type} (S T : F)`), and
`register_clink`'s form derivation takes the family constant and field table as parameters.
So `Denote/Typed/Clink.lean` supplies a one-member `DFam` and reuses `Clink`, `Closed`,
`closed_target`/`closed_source` and `ruleForm` unchanged rather than copying them. `DFam` has
one member on purpose: `DJudgeAll`/`DJudgeSeq` join when a rule concluding about them acquires
a proof, which needs an answer-typed reading of a *list* evaluation that nothing yet consumes,
and inventing a statement nothing checks is how the old family got components no rung could
discharge.

### Where it leaves the ladder

Reach is still 18 rungs, and now says two different things over its length: rungs **001–008**
are derivable in the certified typed judgment (`DJudgeC dclinks`), so `dregistry_sound` makes
them an answer-typed safety claim; rungs **009–018** are checked by `Ratchet/Check.lean` and
are coverage of the checker only, because `prim`, `seq`, `vasgn` and `if'` are unregistered.
The two halves of the ladder now differ in kind, which is the first time that has been true
and is the right shape for it to have.

---

## Clink 68 (2026-09-11) — **the old ladder deleted**: 69 files, ~28k lines of Lean, and the 518-file untyped corpus

Asked to be radical: delete the proof cruft the new ladder does not need, keep the prose as a
legacy reference, and regress none of the measuring scripts. Done — 110 Lean files and ~42k
lines become **41 files and ~14k**, with reach 18, agreement 252/0 and 8 clinks unmoved at
every stage.

### The rule that decided each call

*Keep what the answer-typed ladder needs; delete what served the old judgment.* Stated that
way because "delete what is unreachable" would have been wrong in **both** directions, and
the two mistakes it would have made are the interesting part.

**It would have deleted things the next rung needs.** `Denote/Join.lean` and
`Denote/JoinState.lean` were unreachable — and they are `denM_joinT_left`/`_right` plus the
environment/spine join, i.e. *exactly* the join soundness `DJudge.if'`'s obligation needs.
`Ratchet/Check.lean` §5 had said that fact was "stated nowhere yet". It was proved, in a file
the sweep was about to remove. Finding it is what corrected the owed list, and it is the
strongest argument for reading a file before deleting it: `answer-typed-schema.md`'s own
advice, applied to a deletion rather than to a proof.

**It would have kept things that are traps.** `SemJudge` was reachable (through the step
lemmas the typed layer borrowed) and is the *value-shaped* judgment whose vacuity is the whole
reason for the restatement. Leaving it available would let a future rule acquire a proof of
the weaker statement and register, which is the one failure mode the clink discipline exists
to prevent. So it is deleted rather than deprecated, and `Denote/Sem/Judge.lean` is renamed
`Denote/Sem/Framed.lean` after the one thing in it the new judgment reuses.

### Four severings, in dependency order

Each was a one-identifier problem hiding behind a large file, which is worth recording because
the files looked entangled and were not:

1. **`ctx0`** was the only thing anything outside `Ratchet/Validate.lean` used from it — one
   line, moved next to `Ctx` in `Ratchet/Judge.lean`. 1,196 lines of `chk` then deleted
   outright.
2. **Three `stepFn` facts** (`stepFn_var`, `stepFn_str`, `strObj`) were the only reason
   `Denote/Typed/JudgeA.lean` imported `Denote/Rules/Lit.lean` and therefore the entire
   48-obligation tree. Moved into `JudgeA.lean` §1a; `Denote/Rules/` deleted whole.
   `Denote/Rules/{Core,Alloc}.lean` were not rules at all (transport lemmas and `ext_push`)
   and are now `Denote/Sem/{Transport,Alloc}.lean`.
3. **`ruleForm`** was the only thing `Denote/Typed/Clink.lean` used from
   `Denote/Clink/Derive.lean`, which pulled in `Obligations.lean` and the `Fam` registry. Moved
   to `Denote/Clink/Form.lean`; `Spec.lean` keeps the mechanism and loses `Fam`/`JudgeC`/16
   theorems.
4. **`InvInit`** was the one declaration in `Denote/Sem/Invariant.lean` §1 that named `Judge`.
   Generalising it to take *what "accepted" means* as a parameter (Norm A) cost no proof
   change and severed the file from any judgment — so the safety reduction, which is layer 7
   and proved for an abstract `Inv`, survives intact and is immediately usable against
   `DJudge`. §2/§3's `CtlOk`/`KontOk`/`Inv` skeleton was `Judge`-indexed and went.

### What the numbers cost

| deleted | lines | replaced by |
|---|---|---|
| `corpus-untyped/` + `slice/` | 518 files | `corpus/` (annotated), derived at build time |
| `Rungs.lean` + `ChkSound.lean` + `CheckRungs.lean` + `Main.lean` | ~7,500 | `Ratchet/Check.lean` (409), whose checker returns the derivation |
| `Validate.lean` (`chk`) | 1,196 | the same |
| `Judge`'s 83 rules and their threading lemma | ~1,750 | `DJudge`'s 12 |
| `Denote/Rules/` (48 obligations) + `Obligations.lean` | ~6,000 | `Denote/Typed/JudgeA.lean`'s 8, answer-typed |
| `Denote/Sem/{Step*,BuiltinsCap*,Locals,Mut,Narrow*,Query,Send,Down,FrameLocal}` | ~8,600 | nothing yet; this was the layer push the EMERGENCY EXIT was about |
| `Denote/Proto/` | 1,009 | `Denote/Typed/`, which is the real thing at 8 rules |
| `SemJudge` + companions | ~200 | `SemJudgeA` |

`Denote/Sem/FrameLocal.lean`'s 555 lines are the one deletion worth flagging separately:
`HANDOFF.md`'s working rule exists *because* of that file — it was proved against a target
that was never written down and the target turned out false. It is the cleanest possible
example of what the rule prevents, which is why the rule is quoted and the file is not.

### What survives unreachable, and why that is not a contradiction

Four files: `Join`, `JoinState`, `AnswerCatch`, `Invariant`. Nothing imports them; `lake build`
compiles them anyway (the `Denote` lib is a glob), so they stay verified. They are the next
rung's inputs — join soundness, `CatchFree`, the safety reduction — and a ladder that deletes
its own next step to make a dependency graph tidy has optimised the wrong thing.

---

## Clink 69 (2026-09-11) — **safety is a field of the clink**, and eight rungs have an end-to-end proof

Asked whether there is an end-to-end safety proof and where it can be watched growing. There
was not, and the chain stopped one link short in a way worth recording precisely, because the
obvious fix is the wrong one.

### Where it stopped

`dregistry_sound` gave `SemJudgeA`, whose hypothesis is `runA fuel (evalFrom m e) = .ans a m₀
rest`. That is a statement about runs which reach an **answer** — and the one type-stuck
outcome, `.uncaught`, is reported by `runA` as `.halt`, not `.ans`. So on exactly the runs
safety is about, the obligation was silent.

The tempting repair is to derive safety from `SemJudgeA`: `.uncaught` is constructed at one
site (`unwind`'s empty-continuation arm on a `raiseJ`), and `unwind` pops **one frame per
step**, so a machine that is about to produce `.uncaught` has `ctl = .jump (.raiseJ exc)` and
`kont = []` — which *is* an answer point, so `runA` stops and reports `.ans (.esc …)` first.
That argument is correct and it is the schema's §3.1 losslessness claim. It is also
**unproved**: it needs `UncaughtInv`, the converse of `done_inv`, which does not exist and
belongs in the other package next to it.

### The repair, and why it is better than the derivation

Make safety a **second obligation carried by the same clink**:

```lean
def SafeJudge (Γ : Env) (e : Ratchet.Expr) : Prop :=
  ∀ m, StateOk ctx0 Γ .ivar0 m → StuckFree m e

def SemSafeA (Γ : Env) (e : Ratchet.Expr) (τ : Ty) (Γ' : Env) : Prop :=
  SemJudgeA Γ e τ Γ' ∧ SafeJudge Γ e
```

and instantiate the target family at `SemSafeA`. Then `Clink.sem`'s type demands both halves,
`dregistry_safe` is **unconditional at every registry size**, and the property the question
was really about — *the safety proof stays green at every clink* — is not a discipline anyone
has to remember. It is what the structure's field means: a rule that cannot prove safety
cannot register, and a registered rule cannot lose the proof without `dclinks` failing to
build.

Two things this buys over waiting for `UncaughtInv`:

* **No critical path.** The general derivation is still worth having; when it lands,
  `SafeJudge` becomes a *projection* of `SemJudgeA` rather than an obligation, and every clink
  keeps its existing proof unchanged. Nothing has to be redone.
* **The registered fragment needs no such lemma at all.** Everything the eight rules derive
  evaluates in one `stepFn` step to a value at the empty continuation, so the run never
  reaches `unwind`. `safeJudge_of_step` is two fuel cases over `safeA_value_nil`, and each of
  the eight safety halves is then one line.

`SafeJudge` deliberately does not mention `τ` or `Γ'`: safety is a property of the program and
the incoming environment, and the type is what the other half is for.

### Where it can be watched

`Denote/Typed/Safety.lean`, one theorem per certified corpus rung, at the **real
prelude-booted machine** the difftest SUT runs:

```lean
theorem safe_004_str_lit (hb : bootOkB = true) : StuckFree bootMachine (.str "hello") :=
  dregistry_safe derivD_strLit (stateOk_boot hb)
```

Eight of them — rungs 001–008, the corpus's own programs — each axiom-clean, each with its
one remaining hypothesis discharged by `stateOk_boot`. That hypothesis is conditional on one
`Bool` (`bootOkB`) rather than `decide`d, because the booted heap is the output of
`Interp.run 200_000` over the whole prelude; the `Bool` is a build gate in
`Denote/Sanity.lean` and `native_decide` was rejected for the axiom it costs.

`lake exe semladder` prints the list and `safeRungFloor` ratchets the count. `004-str-lit` is
the interesting one of the eight: it is the only rung here whose evaluation **allocates**, so
its clink's answer-typed half goes through `ext_push` and `Ext` rather than being `rfl` at the
step — which is the shape every allocating rule will reuse.

### What is still coverage rather than safety

Rungs 009–018 are checked by `Ratchet/Check.lean` and have no safety theorem, because `prim`,
`seq`, `vasgn` and `if'` are unregistered. All four are behind `RunAPushK`, and `semladder`
now prints two numbers side by side so that gap is a line in the report rather than a
footnote in a file.

---

## Clink 70 (2026-09-11) — the safety proof is cross-checked against the corpus, and the coverage gate finds §F30 immediately

Asked to make `run_typed_ratchet.sh` check that the final safety proof involves each semantic
rung. Two checks were missing, they are different, and one of them failed on the first run.

### 1. The list was not the theorem's subject

`safeRungs` was a `List String` with `#guard safeRungs.length == 8`. That guard is satisfied
by eight names and **no theorems** — it counted a hand-maintained list against a
hand-maintained floor. Fixed by making the list carry the programs and proving the theorem
*over the list*:

```lean
def safeRungs : List (String × Ratchet.Expr) := [("001-int-lit", .int 1), …]

theorem safeRungs_safe (hb : bootOkB = true) : ∀ q ∈ safeRungs, StuckFree bootMachine q.2
```

Now adding a name without a theorem does not typecheck. Verified by tampering: changing one
entry's program made the build fail in three places.

### 2. …and the theorems' link to the corpus was prose

`safe_004_str_lit`'s docstring said *`corpus/004-str-lit.rb` — `"hello"`*. Nothing checked it.
A safety theorem can be perfectly true of `.str "hello"` and say nothing about rung 004 if the
rung's program is something else — honest per theorem, wrong per ladder.

`lake exe semladder build` now reads each rung the pipeline actually built and compares its
**sig-stripped program** against the `Expr` the theorem is about, using the same
`Decode.program` the checker uses. Eight matches. Verified in the direction that matters by
tampering with `build/004-str-lit.rung.json` rather than with the Lean: the theorem still
compiled, and the cross-check reported `MISMATCH` and exited 1.

Both directions therefore bite, and they bite in different places — the Lean build catches a
theorem drifting from the list, the script catches the corpus drifting from the theorem.

### 3. The coverage gate, and what it found

The question as asked — *does the safety proof involve each registered rule?* — is decidable:
each `Expr` head admits exactly one `DJudge` rule in this fragment, so `rulesUsed` says which
rules a derivation of a program must use, and the gate is one `#guard`.

**It failed on the first run**, and the finding is §F30: `var` is registered, proved on both
halves, in `DJudgeC` — and **no rung the safety proof covers reads a local**. It cannot: the
smallest witness is `x = 1; x`, which needs `vasgn` and `seq`, both unregistered and both
behind `RunAPushK`; and the single-expression alternative, a bare name, desugars to
`Expr.vcall`, which has no rule at all. So the gap is structural and self-healing — the first
`vasgn`/`seq` rung exercises `var` for free.

Recorded rather than papered over, in the shape `legacyUnclinked` established: a frozen
`unexercised := ["var"]` with a `#guard` that fails if anything *else* joins it. So a newly
registered rule must be exercised end to end or be added here with a reason, and the two
controls next to it (every listed name really is registered and really is unexercised; no rung
leans on an unregistered rule) are what keep the gate from being vacuous.

### What the numbers looked like before and after

Before: *8 rules registered, 8 rungs proved safe* — which reads as though the two cover each
other. After: *8 registered, 7 exercised, 1 named exception*, plus a per-rung cross-check
against the built corpus. Same proofs; the report stopped implying something it had not
checked.

---

## Clink 71 (2026-09-11) — the safety field is the **invariant**, not whole-program safety

Clink 69 made safety a field of the clink target as

```lean
def SafeJudge (Γ : Env) (e : Ratchet.Expr) : Prop :=
  ∀ m, StateOk ctx0 Γ .ivar0 m → StuckFree m e
```

and that is **too weak**, for a reason that is structural rather than a matter of degree.

### What was wrong with it

`StuckFree m e` is `SafeA (evalFrom m e)`, and `evalFrom` **empties the continuation**. So the
field said: *run this expression as a whole program and nothing gets stuck.* It said nothing
about a machine part-way through a larger program, which is the only situation a composite
rule's premise ever arrives in. `vasgn` evaluates its right-hand side under an `asgnK` frame;
what it would have had in hand is a fact about evaluating that right-hand side from an *empty*
continuation, and bridging the two is fuel arithmetic that every composite rule would redo.
Four rules owed, four bridges.

It was also not an invariant in any useful sense: nothing in it mentioned the continuation, so
there was nothing for a frame-pushing rule to discharge and nothing for a frame to accept.

### The replacement

```lean
inductive DKontOk (τa : Ty) : List Kont → Env → Ty → Prop
  | nil {Γ : Env} : DKontOk τa [] Γ τa

def SafeUnder (Γ : Env) (e : Ratchet.Expr) (τ : Ty) (Γ' : Env) : Prop :=
  ∀ (τa : Ty) (m : Machine), StateOk ctx0 Γ .ivar0 m →
    m.ctl = .eval (toRuby e) → DKontOk τa m.kont Γ' τ → SafeA m
```

Safety of the **machine**, under **any** continuation that accepts the expression's type. Two
indices carry the content:

* **the continuation typing `DKontOk`**, which is the invariant's hard half. One constructor
  today because no registered rule pushes a frame; `vasgn` will add `asgnK` with a value
  clause (write and pass on) and an escape clause (pop and pass on). The census that priced
  the full set at 36 of `Kont`'s 49 constructors is in `AGENTS.md`.
* **the answer type `τa`** — the type the *empty* continuation accepts, i.e.
  Wright–Felleisen's context typing `E : τ ⇒ τ_ans`. `nil` pins it to the program's own type,
  and that pin is load-bearing: the deleted prototype found that with `nil` accepting anything,
  the invariant proves safety while proving **nothing about types**, because the existential
  over the current type forgets what the certificate claimed. The pin is the only reason the
  value clause is recoverable.

`dregistry_safe` — safety of every program the fragment types — is now one line:
`dregistry_safeUnder` at `DKontOk.nil`. The invariant does the work; the whole-program theorem
instantiates it.

### The observation worth keeping: the Church encoding *is* the induction

`Denote/Proto/Safety.lean` proved `preserved` by `cases` on an inductive `PJudge`. That route
is **not available** here, and it is not an oversight: `DJudgeC` is Church-encoded
(`∀ F, Closed R F → F.judge …`), so a derivation cannot be inverted — there is no `cases` on
it at all.

What the encoding gives instead is elimination into *any family closed under the rules*. So
choosing the family to be "the invariant holds here" **is** the inductive proof of the
invariant, with one case per rule — and those cases are exactly the `Clink.sem` fields. The
registry design and the invariant design are the same design seen twice; realising that is
what made the field's shape obvious once the weak version was written down.

`Denote/Sem/Invariant.lean` §1 stays for the monolithic form (`SafetyObligations`,
`safety_of_invariant`, and `InvInit` parameterised by what "accepted" means), which is still
the right thing if a concrete `Inv` is ever wanted for a non-registry judgment.

### Cost

Eight proofs, unchanged in substance: `safeUnder_of_step` is the same two fuel cases over
`safeA_value_nil`, now with `DKontOk`'s inversion supplying `m.kont = []`. What changed is
that the step facts had to be restated in `m.ctl = .eval (toRuby e)` form with the
continuation left alone — §1a's `evalFrom` versions are the `kont = []` instances of the same
three facts. The string literal's is stated in terms of `Builtins.allocStr`'s own result
rather than `pushHeap`, because `safeUnder_of_step`'s existential only needs *some* machine to
land on; relating the fresh heap to `pushHeap` is work `SemJudgeA`'s half needs (for the `Ext`)
and this half does not.

Unmoved: reach 18, agreement 252/0, 8 clinks, 8 rungs proved safe, `var` still the named
unexercised rule (§F30).

**[✗→] Correction to the section above (2026-09-13).** "A derivation cannot be inverted — there
is no `cases` on it at all" overstates it. What is true: a `DJudgeC` derivation is a Π-type, so
there is no constructor to match on and `cases` does not apply; and induction with an
index-only motive is free, since that is what the definition *is*. But **inversion is
recoverable**, by the standard pairing trick — take the motive `DJudgeC R · ∧ Inv ·` so the
original derivation is available in the induction hypothesis — at the cost of also proving
`Closed R (DJudgeC R)`, which goes through rule by rule but has no proof uniform in `c` (a Horn
rule mentions the judgment contravariantly in its premises, so `c.form` is not monotone). No
one has needed it, and the invariant-as-motive route does not, which is why the gap went
unnoticed until the encoding was explained out loud.

---

## Clink 72 (2026-09-13) — `runA_pushK` proved, `vasgn` registered, and safety restated through `DInv`

Two asks: build the `vasgn` rule, then define the safety property in terms of `DInv`. Both
done; the second one has a caveat that is the interesting part.

### The lemma that was gating four rules

`runA_pushK : runA fuel (pushK K m) = resOutA K (runA fuel m)`, for `CatchFree K`. Proved, in
`Denote/Sem/Answer.lean` next to `run_pushK`, because it is the same induction one level up —
`Interp.run` becomes `runA`, `ARes.out` becomes `resOutA`, and the five outcomes are accounted
for the same way. It was stated as a named `Prop` (`RunAPushK`) in clink 70 and is now the
theorem; the `Prop` is deleted rather than kept beside it.

Two small things fell out of writing it that `run_pushK` had inline and now shares:
`pushK_eq_deliverA` (at an answer point, pushing the continuation **is** delivering to it —
the same three-case argument `run_pushK` had twice) and `answerPoint_pushK_none`.

### `vasgn`, and the two halves diverging for the first time

This is the first rule with a sub-expression, so the first where the halves are proved by
different machinery — and the asymmetry is the clearest evidence yet that clink 71's
restatement was right:

* the **invariant half is five lines and uses no fuel arithmetic at all**. Step to the pushed
  frame, hand the premise the machine that step created, and `DKontOk.asgnK` is exactly the
  continuation typing that machine has. The premise applies *where the rule uses it*. Under
  clink 69's whole-program `SafeJudge` this would have been a `safe_pushK` instance with its
  own fuel bookkeeping — which is what `VasgnAnswer.lean` was, at 12 lines plus a 22-line
  side-condition apparatus it replaced.
* the **answer-typed half is ~60 lines** and is the whole of `runA_pushK`'s customer: decompose
  the run, case on the inner answer, and deliver. The `val` arm writes the local and needs
  `denM_setLocal` and `StateOk_setLocal`; the `esc` arm pops the frame and is four lines,
  exactly as `VasgnAnswer.lean` measured on the stuck axis before it was deleted.

`DKontOk` gains its first frame: `asgnK`, carrying the rule's two side conditions, with a value
clause and an escape clause. The value clause of the invariant (`safeA_value_kontOk`) becomes a
real induction over the continuation — one case per frame, which is the shape the whole layer
has from here.

**§F29 happened again.** `DJudge.vasgn` was authored with outgoing environment `envSet Γ₁ x τ`
and no premises; the obligation is unprovable that way, because `StateOk_setLocal` needs
`capStale`/`isAliasTy` and produces `envAfter`. Same finding as `var`, one rule over, and for
the same reason: nothing the checker can *reach* has an alias or a closure, and the obligation
quantifies over every environment a conformant machine can have. Reach 18 before and after.

### Safety through `DInv`, and what `preserved` costs

`DInv τa m` is now defined as a predicate on machines — two arms, `eval` and `value`, no
`jump` arm because no registered rule produces one — with `dInv_safe` and `dInv_init` proved
and `StuckFree` derived as `dInv_safe (dInv_init hj hm)`. That is the factoring
`Denote/Sem/Invariant.lean` uses, so the object a reader looks for now exists.

**`preserved` is not proved, and cannot be by the route that file anticipates.** The eval arm
carries a `DJudgeC` derivation; `DJudgeC` is Church-encoded; showing the *successor* is judged
means taking that derivation apart, and there is no `cases` on a Π-type. `Denote/Proto/Safety.lean`
did exactly this by `cases` on an inductive `PJudge`, before both were deleted.

`dInv_safe` does not need it, and that is the design rather than luck: the eval arm's
obligation is `SafeUnder`, which already speaks about the machine's **whole future**. The
induction `preserved` + `safety_of_invariant` would perform over the run has already been
performed — once per rule, at registration, by choosing the family to be the invariant.
`preserved` would be a second pass over the same ground.

What is genuinely lost, recorded rather than papered over: `safety_of_invariant` is stated for
an abstract `Inv` and proved once, so a *different* judgment could reuse it. This one cannot.
That is the price of generating the judgment from the registry, and it is the first thing that
design has cost.

### Numbers

9 clinks (was 8), 3 rules owed (was 4). Ladder reach 18, agreement 252/0, 8 rungs proved safe
end to end — **unchanged**, and `unexercised` grows to `["var", "vasgn"]`: no corpus rung is a
bare assignment (`029-simple-assign` is `x = 5; x + 1`, a `seq`), so neither rule is reachable
by an end-to-end safety theorem until `seq` lands. The coverage gate said so without being
asked, which is what it is for. `seq` unlocks both, plus rungs 029–034.

The refusal control in `Denote/Typed/Controls.lean` moved from `vasgn` to `if'`, because
`vasgn` now has a proof and the control has to name a rule that does not. That is the control
doing its job.

---

## Clink 73 (2026-09-13) — a working rule, written down after paying for it twice

Not a proof. `found-issues.md` §F29 had recorded the same failure at two rules — `var` and
`vasgn` — and the project's own threshold for turning a finding into a norm is "paid for
twice" (`HANDOFF.md`'s other working rule cites `FrameLocal.lean` and `not_KontFrame`). So it
is stated, in `Ratchet/Check.lean` §Authoring a rule, next to the constructors it is about.

**The rule.** Before writing a `DJudge` constructor, find the `Denote/Sem/` lemma that
transports `StateOk` across the machine change the rule makes — `StateOk_reCtl` for
`ctl`/`kont`, `StateOk_ext` for an allocation, `StateOk_setLocal` for a local write,
`StateOk_ivarWrite` for an ivar. **Its hypotheses are the rule's premises; its conclusion's
environment is the rule's outgoing environment.** Both times I wrote the rule first and
guessed; both times the obligation refused.

**Why it bites when nothing reachable triggers it**, which is the part that makes it worth
stating rather than assuming people will notice: no rule produces a `Ty.sameAs` or a
`Ty.clos`, so `killAliasesTo`/`killClosOver` are the identity and `isAliasTy` is always false
on every environment the *checker* can reach. The obligation quantifies over every environment
a **conformant machine** can have. No amount of corpus testing finds these, and two of the two
rules with an interesting environment had one.

**Why it makes the next rule's proof simpler** — the reason this is a rule of thumb about
*authoring* and not just an observation about proving. `DKontOk.asgnK`'s tail index is
literally `envAfter Γ x τ`, and it matches `DJudge.vasgn`'s conclusion because both were
copied from `StateOk_setLocal`. The frame clause composes with the rule by `rfl`. Had the rule
said `envSet`, every frame clause, every sequence rule and every downstream consumer would
carry a rewrite between the two forms. A rule stated at the transport lemma's own environment
is a rule nothing has to translate.

**What was deliberately *not* done.** The tempting generalisation is to hoist this into a
checked invariant: *a rule may only grow the environment, never re-type an existing entry*,
enforced as a third conjunct on the clink target next to `SemJudgeA` and `SafeUnder`. It is
**false for Ruby** — `corpus/031-reassign-different-type.rb` is `x = 1; x = true; x` and must
type, because "real Ruby locals are not statically single-typed, and neither is this checker"
— and `killClosOver` re-types entries the rule did not bind *on purpose*, since writing `x`
invalidates any other binding whose type captured it. The nearer-true version (monotone in the
**domain**: `envKeys Γ ⊆ envKeys Γ'`) was floated and left alone too, on the grounds that
constraining how the environment may evolve buys less than keeping it open and letting the
obligation force soundness case by case. Recorded here so the idea is not re-proposed as new.

Cross-referenced from `Denote/Typed/JudgeA.lean` §3a (where the obligation refuses),
`HANDOFF.md` (now "two working rules") and `AGENTS.md` §F29's paragraph. One statement, three
pointers — not four copies.

**Its sibling is §F31**, landed the same day from the other direction. This norm is about the
premises a rule *needs* — read off the transport lemma. §F31 is about the premises a rule
*states* — and specifically that `ruleForm` leaves any head not in `dFamField` raw, so
`seq`'s and `prim`'s sub-derivation premises would have been the **syntactic** relation rather
than the family's, and the obligation would have been about a derivation the registry never
vetted. Together they bracket the same question: a rule's premises are not free variables, and
both halves of what constrains them now have a name.

## Clink 74 (2026-09-13) — typed/safe gap closed

- `Typed/Compose.lean` proves the escape clause of `DKontOk` and lifts a safe,
  answer-correct closed run to `SafeUnder` using `run_pushK`. Both premises are
  necessary: answer correctness alone says nothing about halts. `Typed/Run.lean`
  exposes the same contract at a machine entry for sequence/argument frames.
- `Typed/Sequence.lean` proves `SemA.seq` from an inductive list of **semantic**
  premises (`SemSeqA`), including the final empty `seqK`. `Typed/Branch.lean`
  proves `SemA.if'`; `Typed/Primitive.lean` composes the seven proved builtin rows.
  `DFam` now carries both list companions. All 16 constructors register and are
  counted by family-qualified names in the syntax/proof audit.
- The claimed `EnvOk` join prerequisite was absent and false: union normalization
  can expose a `sameAs` identity neither branch promised. `joinBinding` preserves
  identical bindings and otherwise removes exposed alias layers after joining.
  `JoinState.lean` now proves `StateOk_joinEnv` and checks the counterexample.
- A primitive counterexample compiled before strengthening conformance: append
  `{ klass := Boot.stringId }` (no payload), bind it as `x`, then evaluate
  `"a" + x`. `ext_push`/`StateOk_setLocal` proved conformance, `DJudge.prim`
  typed it as String, and `#guard typeStuck (run 100 …)` passed at the real boot.
  `Sem/PrimHeap.lean` therefore pins String payloads, the eight dispatch entries
  used by the seven primitive rows, and ZeroDivisionError's non-type-error chain.
  Dispatch pins are conditional on the context leaving the name unclaimed.
  The strengthened `bootOkB` is checked at the real boot (whose boolean `!`
  resolves to `Object#!`). Allocation now owes the new object's payload invariant.
- `Framed.nominal` transports a receiver's nominal type across argument evaluation;
  state conformance alone relates neither the captured receiver nor two heaps.
  Existing allocation and local-write proofs discharge it through `Ext` or heap equality.
- Sandbox runs use `UV_CACHE_DIR=/private/tmp/ruby-ratchet-uv-cache`; otherwise the
  agreement stage fails on the protected default uv cache. Baseline: reach 18,
  252 agree / 0 disagree, safety reach 8, 21 accepted rungs lacking safety proofs.
- `DJudgeAll.cons` now states `plainArgB e = true`: the interpreter treats splats,
  kwargs, and forwarding as argument-list syntax. An expression's semantic premise
  alone can be vacuous there. `DJudge.plainArg` proves every syntactic derivation
  satisfies the guard, so the checker returns exactly the same verdicts.
- Primitive dispatch is proved for every `SendSite`, including literal `self` receivers;
  the methods are public. String allocation retains its encoding tag. Integer division
  includes the ZeroDivisionError path, whose fresh object must remain a BasicObject.
- `CorpusSafety.lean` carries 29 concrete constructor-wise derivations. The checker is
  not used as a trusted shortcut. All 16 rules are exercised, including list `nil`/`cons`
  and sequence `last`/`cons`; the exemption ceiling falls from 2 to 0. Safety prefix is
  17; checker reach remains 18 because rung 018 is a correctly rejected unsafe program.
- Validation: the full quiet ratchet is GREEN (252 agree / 0 disagree), with the same
  29 accepts and no reduced floors or targets. The new malformed-payload, division-by-zero,
  argument-head, and alias-join controls compile. `safeRungs_safe` and all new semantic
  rule proofs use only `propext`, `Classical.choice`, and `Quot.sound`. No proof build
  approached five minutes; the largest primitive-row build took about 16 seconds.
- The first green commit necessarily closes all three rule gaps together: the existing
  gate forbids committing any of the intermediate red states.

## Clink 75 (2026-09-13) — decimal `Integer#to_s`

- Add the nullary `DPrim.intToS` row and pin its actual builtin in `primitiveMethods`.
  `StateOk_ext` already transports the dispatch pins; `stepSpec_string` supplies the
  allocation, String payload, result typing, and continuation safety obligations.
- The builtin reduces to `okStrEnc false (toString x)` by `rfl`, for every integer.
  Radix arguments stay outside this row: invalid bases can raise `ArgumentError`.
  Controls reject a forged Integer result and a nil radix; negative integers type.
- Rung 019 gains a constructor-wise safety proof. Floors: checker reach 19, 30 safe
  rungs; safety prefix stays 17 because 018 is a permanent unsafe control.
  The primitive proof builds in 15 seconds, with only the standard Lean axioms.
- Full quiet ratchet: GREEN, 252 agree / 0 disagree, 30 safe rungs, checker reach 19.

## Clink 76 (2026-09-13) — integer equality at any argument type

- `DPrim.intEq` quantifies over the argument type. The argument still needs its own
  semantic derivation and is evaluated before dispatch; arity remains exactly one.
- `Integer#==` can reverse into the argument's program-defined `==`.
  `MethodsExact.lookup` at `ctx0` proves `hasProgramEq = false` for every value;
  `PrimitiveEquality.lean` uses that fact to rule out the callback. No new heap
  invariant is needed beyond pinning the receiver's actual `Integer#==` builtin.
- The builtin proof retains the binary-string Unsupported path and proves Boolean
  result typing on every value path. Rungs 020 and 021 get independent derivations;
  controls reject wrong arity and an unsafe argument expression.
- Full quiet ratchet: GREEN, 252 agree / 0 disagree, checker reach 21, 32 safe rungs.
  Equality facts build in 30 seconds; composition in 15. Only standard Lean axioms.

## Clink 77 (2026-09-13) — scalar queries complete tier 2

- Add proved rows for Integer `zero?`/`<=`/`>=`, nil `==`, and String `length`.
  These preserve the machine, so `StateOk_reCtl` is the transport; string payload
  conformance already supplies the length receiver's representation. The byte-aware
  builtin path admits binary strings too. Nil equality inherits `Object#==` and
  accepts any argument type without the numeric reversal protocol.
- Each dispatch entry joins `primitiveMethods` and is checked at the actual boot.
  Controls reject extra query arguments and non-integer ordered comparisons.
  Six corpus safety derivations raise the safe-rung floor to 38 and checker reach
  to 31. Rung 032 (bare undeclared name) is the next checker frontier.
- The first full gate also found rung 189 newly accepted through `zero?`; its
  sequence/conditional safety proof joins this batch, as required by the gate.
- Full quiet ratchet: GREEN, 252 agree / 0 disagree, checker reach 31, 38 safe rungs,
  safety prefix 17, no owed rules or exemptions. Query equations build in 1.6 seconds;
  primitive composition in 15. All proofs use only standard Lean axioms.
- Deferred finding: rung 039's emitter produces `Int | (Int | String)` while `joinT`
  normalizes to `Int | String`; align the emitter, then add its existing-rule derivation.

## Clink 78 (2026-09-13) — normalized certificate joins

- Mirror `joinT` in the emitter: preserve its structural nil/nilable cases, then
  flatten unions, remove duplicates in first-occurrence order, and rebuild rightward.
  Rung 039 now claims the checker's `Int | String` instead of `Int | (Int | String)`.
- Raise `fragmentFloor` to 39. The new `validateD_safe_boot` bridge supplies safety
  from acceptance; the 38 worked corpus theorems remain regression examples.
- Full quiet ratchet: GREEN, fragment 39, checker reach 31, 252 agree / 0 disagree.

## Clink 79 (2026-09-13) — `if` without `else`

- The false path returns nil immediately, rather than evaluating a nil expression.
  `BranchMissing.lean` therefore composes `RunSpec.bind` with a direct answer on
  that path. `StateOk_joinEnv` determines the rule's outgoing environment:
  join the body's environment with the condition's, not the incoming environment.
- Add `DJudge.ifNoElse`, its checked certificate arm, clink, and bridge case.
  Rung 036's worked theorem exercises the new rule. Controls check nullable result
  claims and force the checker to reject rung 042's unsafe reassignment certificate;
  the same-type reassignment control passes. No emitter rejection is relied upon.
- Full quiet ratchet: GREEN, fragment 40, 17 proved rules, checker reach 31,
  252 agree / 0 disagree. The new semantic proof builds in under one second;
  `validateD_safe_boot` remains axiom-clean.

## Clink 80 (2026-09-13) — bare-name dispatch and NameError

- `BareNameFree` and `MissFree` already pin absence of `x` and user `method_missing`
  at `ctx0`. The rule admits exactly that table's current name, `x`, through a new
  `Deriv.bareName` leaf. Other bare names and ordinary `x()` sends are refused;
  the latter raises NoMethodError. Runtime controls confirm both exception paths.
- Generalize the checked exception-family predicate and allocation proof from
  ZeroDivisionError to a table including NameError. Each must descend from BasicObject
  and none may descend from NoMethodError, ArgumentError, or TypeError. Allocation
  then preserves framing and proves a safe escape; it need not produce a typed value.
- `BareName.lean` walks the actual dispatch path, including all Unsupported shadow
  exits. The checker, registry, emitter, and bridge gain the leaf together; rung 032
  exercises it. Floors rise to fragment 41, 18 rules, and checker reach 43.
- Full quiet ratchet: GREEN, 252 agree / 0 disagree, all new floors met. The bare-name
  proof builds in five seconds; the full acceptance-to-safety theorem is axiom-clean.

## Clink 81 (2026-09-13) — first-order array literals

- Reuse the certified list companion for left-to-right evaluation. `Array.lean`
  retains an accumulator at the joined element type, propagates safe escapes, and
  allocates only after the last element. `CoreOk.arrayBasic` checks the actual boot
  class needed by `ext_push`; no constant-name assumption substitutes for that id.
- `Framed` now preserves first-order denotations, including nested arrays. Heap-equal
  local writes use `denM_heap_only`; allocations use `denM_ext`. Move `FirstOrder`
  to the type vocabulary so the checker can require it. Higher-order types are
  excluded because later local writes can invalidate a captured environment.
- This is a contract for the current heap-nonmutating fragment, **not a mutator
  solution**: pushing into an empty array destroys its `arrayOf never` denotation.
  Collection writes will require a more precise retained-type framing discipline.
- The checker recomputes the element join and checks arity. Align the emitter with
  `elemTy`'s right fold; its structural nilable cases make fold direction significant.
  Controls cover forged types, arity, nesting, splats, unsafe elements, evaluation
  order, and higher-order retention. Rung 044's worked proof exercises the new clink.
- Full quiet ratchet: GREEN, fragment 41→46 (044–047 and 049), checker reach 43→47,
  19 proved rules, 252 agree / 0 disagree. The array proof builds in under a second;
  `validateD_safe_boot` remains axiom-clean. Next positive frontier: 048, hash literals.

## Clink 82 (2026-09-13) — interleaved hash literals

- Add `DJudgePairs`/`SemPairsA`, not two `DJudgeAll` walks: a value can assign a local
  the next key reads. The pair relation is a fourth `DFam` projection, carried through
  registration, certified builders, and the mutual bridge; no raw syntactic premise
  crosses the semantic boundary. A constructor-form control pins that boundary.
- `Hash.lean` proves key/value evaluation, safe escape propagation, duplicate-key
  replacement (old key, new value), and allocation. First-order framing retains both
  accumulator components; `CoreOk.hashBasic` supplies allocation's boot-class fact.
  The proof keeps `valueEql` abstract: only membership of the retained key matters.
- Fix the emitter's stale tagged-pair assumption: export supplies `[key_ast, val_ast]`.
  Walk pairs in source order and right-fold both joins, as `elemTy` does. Checker
  controls pin independent certificate-list lengths, forged joins, unsafe values,
  nested arrays, key/value ordering, and higher-order rejection. A runtime guard and
  CRuby probe agree on duplicate-key position and last-value behavior.
- Full quiet ratchet: GREEN, fragment 46→47, checker reach 47→49, 22 proved rules,
  252 agree / 0 disagree. The hash proof builds in under a second, axiom-clean.
  Next positive frontier: 050, array indexing.

## Clink 83 (2026-09-13) — array indexing and payload dispatch

- `arrayOf τ` constrains payload elements, not the object's dispatch class. A
  synthetic BasicObject with an array payload satisfies that shape yet `a[0]`
  reaches type-stuck; `ArrayIndex.lean` pins the witness as a runtime control.
  Add boot-checked `ArrayPayloadOk`, preserved across each allocation and local
  write. It pins payload-bearing arrays to boot Array, so subclass/eigenclass
  admission will need a more general dispatch invariant, not an unchecked premise.
- Add the `Array#[]` dispatch-table fact and the first-order `DPrim.arrayIndex` row.
  The semantic proof follows actual lookup, normalizes negative indices, proves
  in-range membership, and returns nil at either outer bound. The argument's
  evaluation preserves the receiver through `Framed.firstOrder`.
- Use `unfold runCollections`, not its generated simp equations: Lean fails to
  generate an equation for the unrelated overlapping `Array#<<` branch. Unfolding
  the definition proves the indexing equation directly; no evaluator change.
- Controls cover forged non-null result claims, wrong argument types/arity, empty
  and nested arrays, higher-order rejection, and an index that retypes a local.
  Runtime boundary cases match CRuby's `[nil, 10, 20, 10, 20, nil]` at -3 through 2.
- Full quiet ratchet: GREEN, fragment 47→48, checker reach 49→50, 252 agree /
  0 disagree. All 22 registered rules remain proved; the new primitive and the
  acceptance-to-safety theorem are axiom-clean. Next positive frontier: 051, hash indexing.

## Clink 84 (2026-09-13) — hash lookup and nil defaults

- `hashOf key val` describes entries, not missing-key behavior. An empty hash with
  default `true` returns a Boolean despite having no entry values; a runtime control
  pins this witness. Add boot-checked `HashPayloadOk`: Hash dispatch and an absent
  or explicit-nil default. Non-nil defaults/default procs need a type/default
  relationship before admission; they are not silently interpreted as nil.
- Preserve that fact across allocation and local writes. `HashIndex.lean` follows
  actual dispatch (including bypassing only the now-excluded default-proc path),
  retains the byte-string Unsupported gate, and gets result typing from membership
  of the pair returned by `find?`. `valueEql` itself needs no new theorem.
- The new primitive row accepts any query type, not just the stored key type, and
  retains first-order key/value denotations while the query runs. Controls cover
  misses, foreign query types, arity, forged non-null results, local retyping,
  higher-order rejection, explicit nil defaults, and the byte-string gate.
- Full quiet ratchet: GREEN, fragment 48→49, checker reach 50→51, 252 agree /
  0 disagree. All 22 registered rules remain proved; the new primitive and the
  acceptance-to-safety theorem are axiom-clean. Next positive frontier: 052, functions.

## Clink 85 (2026-09-13) — thread the semantic context before functions

- Two concrete obstacles to 052: `MethodsExact ctx0` excludes user definitions;
  `FrameOk ctx0.frame` excludes method activations. Generalize `ResultOk`/`RunSpec`
  to an outgoing `Ctx` and ivar spine, with defaults preserving current clients.
  The existing `bind` now uses context-general `bindSpec`, so current composition
  exercises the generalized proof rather than leaving it as unused scaffolding.
- `SemSafeCtxA` carries incoming/outgoing context, locals, and ivar spine separately.
  Prove equivalence to `SemSafeA` at `ctx0`/`ivar0`, plus context-general literal,
  local-read, assignment, and sequence rules. Assignment consumes `capStaleCtx`
  and outputs `killClosOverSpine`; these were hidden computations at `ctx0`/`ivar0`.
  Sequencing consumes exactly the predecessor's outgoing state, not its old table.
- No new checker admission yet. The user reiterated the body-checking requirement:
  check every definition against its parameter/return annotations before accepting,
  even if uncalled; calls must consume a checked signature, not re-infer the body
  at each argument shape. The emitter currently discards its body result type, so
  the trusted checker must enforce this. Add permanent rejection controls for bad
  uncalled bodies, definition-site locals, renamed parameters, and call-before-def.
  Positive define-then-call controls are required before claiming method coverage.
- Full quiet ratchet GREEN: fragment 49, checker reach 51, 252 agree / 0 disagree;
  all 22 rules proved. The context equivalence, assignment, and sequence proofs
  are axiom-clean. Coverage is unchanged; 052 remains the next positive frontier.

## Clink 86 (2026-09-13) — actual method entry and the caller-frame obligation

- Prove `classifyFull_required` and `enterUserMethod_required` over arbitrary lists
  of required positional names/arguments, not a two-argument special case. The
  latter names the actual fresh method frame and `frameK`, with no captured frame,
  block, or keyword bundle. No interpreter changes. Normalize preprocessing before
  case-splitting the reversed parameter list; no large evaluator proof is needed.
- `requiredFrame_envOk` derives the body's environment from the signature's types
  and the arguments' denotations. Lookup follows the actual first matching name;
  absent names read nil, never a caller local. First-order, non-alias parameter
  types are explicit premises: heap-only denotations survive the frame change;
  arbitrary captured-frame/behavioral types need a stronger transport.
- Runtime controls exercise body execution and caller return, zero-argument entry,
  absent caller locals, and both wrong-arity directions. These are semantics tests,
  not claims that the checker accepts methods; annotation/body checking stays owed.
- **Counterexample to the next proposed transport:** `Framed entered damaged` can
  hold while an inactive caller local changes from Integer to Boolean. The witness
  is not asserted reachable; it proves the current contract alone cannot restore
  caller `EnvOk`. `Framed` pins heap properties and the active stack, not the frame
  array. Add caller isolation/preservation (and its compositional transport) before
  claiming a call clink. A checked body must carry that effect information as well
  as its annotated answer type; assuming restoration would repeat the old pitfall.
- Full quiet ratchet GREEN: fragment 49, checker reach 51, 252 agree / 0 disagree,
  all 22 rules proved. New entry/environment proofs and the counterexample are
  axiom-clean; no coverage increase is claimed until definitions and calls certify.

## Clink 87 (2026-09-14) — preserve caller frames in the actual body contract

- Add `FramePres` to `Framed`, hence to every existing semantic rule. It preserves
  frame-count growth and the root's captured-parent field, and preserves inactive
  old frames when that parent is absent. The captured-parent field makes isolation
  compositional. Captured activations deliberately do not promise isolation; a
  runtime control still writes an outer local through one. No blanket ban on captures.
- Prove local-write preservation from the actual `setLocal.owner` walk. Equal
  heaps/stacks no longer construct `Framed` without a frame-effect proof; allocation
  and control updates supply equality, writes supply `FramePres.setLocal`. Existing
  sequence/argument rules compose it automatically. The clink-86 damage witness is
  retained as a heap/stack counterexample and now proved excluded by `Framed`.
- `MethodReturn` derives saved-frame preservation and `Framed` after popping a
  required method, then restores first-order caller locals (including alias value
  equalities) for an uncaptured caller. A worked same-name shadowing control restores
  `outer : Integer` after the callee writes its own `outer = true`. Captured callers
  need a captured-chain transport, not an assumed lookup equality after frame growth.
- Generalize `bindSpec`'s outgoing origin: a method continuation returns to the
  caller, so retaining the body's origin would demand the wrong stack balance.
  `methodFrame_runSpec` consumes the body contract through the actual `frameK`,
  handles value/escape/Unsupported outcomes, and leaves full caller `StateOk` as an
  explicit premise. That final conformance transport and checked-signature/context
  integration remain owed; explicit `return` also needs a body-answer contract that
  admits targeted returns. No checker method admission or coverage increase yet.
- Full quiet ratchet GREEN: fragment 49, checker reach 51, 252 agree / 0 disagree,
  all 22 rules proved under the stronger framing contract. Caller restoration,
  method-frame composition, and `validateD_safe_boot` are axiom-clean. The first
  gate attempt caught a doc-comment placement error; corrected before the green run.

## Clink 88 (2026-09-14) — full method-boundary conformance from the body proof

- `StateOk_reframe` transports the entire conformance record across a same-heap
  frame switch. Locals/frame validity are supplied; scope types must be first-order,
  value-only recursive assumptions empty, and constant lookup unchanged. The last
  premise matters: `constGet?` reads the static frame's definition class, so merely
  retaining the constant table is insufficient. Empty constant tables discharge it.
- Widen `FramePres`'s root metadata from the captured parent to `FrameScope`: self,
  block, cref, definition module, and captured parent. These are exactly the fields
  conformance reads. Locals, match state, and default visibility may still change.
  Local-write/equality/transitivity proofs carry this through every existing rule.
- `MethodState` proves full entry and caller restoration, then composes
  `required_method_runSpec` through actual `enterUserMethod`. Its body premise is
  `SemSafeCtxA` at the annotated parameter/return types; no signature-as-proof and
  no assumed caller `StateOk` remain in the composed result. Installation/dispatch,
  syntactic context/signature integration, and explicit-return answers remain owed.
- Worked `identity_after_dispatch`: every Integer argument, from the real boot,
  using the generic local-read body proof and full boundary lemmas. Additional boot
  facts (uncaptured current frame, Object receiver, empty continuation) are checked
  by `methodBootOkB`, not assumed from `ctx0`. This check must join the validator's
  boot contract at method admission. No coverage increase is claimed for a direct
  post-dispatch proof; the checker still rejects method declarations/calls.
- Full quiet ratchet GREEN: fragment 49, checker reach 51, 252 agree / 0 disagree;
  all 22 rules remain proved. Frame-switch conformance, the composed post-dispatch
  call, and the real-boot worked example are axiom-clean.

## Clink 89 (2026-09-14) — actual definition installation and ordinary dispatch

- `MethodDispatch` names the exact `def` record and heap write, proves the definition
  step when `method_added` is quiet, and derives lookup from the existing heap facts.
  Quiet includes absent hooks and the model's CRuby-shadowed Object/Kernel/BasicObject
  entries, not arbitrary user hooks. A differently named definition preserves this
  fact; defining `method_added` itself requires checking the installed state.
- Ordinary-object dispatch preserves all visibility and CRuby-shadow checks. A found
  entry shadows the reflective send family; no name blacklist is needed. Installation
  supplies lookup when the defining class is first in the receiver's ancestor chain,
  plus the empty-between-chain shadow check. Eigenclasses/prepends cannot silently
  bypass that premise. No semantics changes or concrete-body execution in these proofs.
- `required_method_call_runSpec` composes real `finishSend` dispatch with the annotated
  body contract and full method-boundary proof. Installation's **conformance transport**
  and the checker's context/checked-signature integration are still owed: an interpreter
  equality is not a definition clink. No method admission or coverage increase yet.
- Runtime controls exercise actual definition then call, primitive use in the body,
  caller-local restoration, explicit private-call failure, reflective-name overrides,
  and real singleton versus shadowed instance `method_added` hooks. All match CRuby.
  Every new theorem is axiom-clean; the dispatcher module builds in under a second.
- Full quiet ratchet GREEN: fragment 49, checker reach 51, 252 agree / 0 disagree,
  all 22 rules proved. The new runtime controls are imported by the full gate.

## Clink 90 (2026-09-14) — correct the proof-side user-code initial machine

- The method-installation pilot exposed `bootMachine.preludeMode = true`: `Sanity`
  reused `Prelude.boot`'s phase-one evaluator, while `Semantics.run` and the difftest
  SUT correctly construct fresh phase-two frames and clear prelude mode. In the old
  proof helper a user `def` would be marked `fromPrelude`, skipping hook/shadow checks.
  This was a proof/runner mismatch, not a bug in the executable model.
- Make `bootMachine` use the runner's exact `Machine.initOn` + boot-globals recipe;
  guard that prelude mode is off. Add `validateD_safe_run` over `Semantics.run` itself:
  successful boot agrees with `evalFrom bootMachine`, failed boot yields Unsupported.
  No interpreter changes, new axioms, or per-program concrete safety proofs.
- Full quiet ratchet GREEN at the corrected initial machine: fragment 49, checker
  reach 51, 252 agree / 0 disagree, all 22 rules proved. `validateD_safe_run` is axiom-clean.

## Clink 91 (2026-09-14) — full conformance across method installation

- `MethodHeap` transports first-order denotations (including collections, aliases,
  instance/ivar types) through `defineMethod`, and constructs `Framed`. A method write
  is not an `Ext`: its class payload really changes. Keep object-data projections,
  constant/ancestor facts, and differently named lookups; do not pretend the whole
  payload is fixed or extend this to behavioral arrows without their own argument.
- `StateOk_methodWrite` derives data/scope/negative-dispatch preservation, with the
  positive class/method tables supplied by the installation rule. `StateOk_defineTopMethod`
  discharges those too for the top-level method slice. Explicit limits: first-order
  types, empty recursive assumptions, no program classes, fresh method names, and no
  `method_missing` write (the query miss clauses require a stronger contract for that).
  Freshness is forced by legacy `DefsOk`/`extendDefs`: they require every entry to hold
  and prepend without replacing. Broader redefinition support must fix that table.
- `StateOk_reserveName` only weakens absence facts. It installs no syntax/signature and
  cannot authorize call-before-definition. The new body is recorded by the actual
  table write; a call separately consumes its annotation-checked semantic body proof.
- `MethodInstallControls` checks real-boot installation/lookup/hook premises once,
  proves the actual identity-definition step, derives the full installed state, and
  proves its dispatched call for every Integer argument from the generic local-read
  body proof. No per-program post-state validation or concrete-body safety shortcut.
  These controls exposed clink 90's boot mismatch. Checker context/checked-signature
  integration remains owed; definitions/calls are still not admitted or counted.
- All new proofs are axiom-clean and each module builds in under a second.
- Full quiet ratchet GREEN: fragment 49, checker reach 51, 252 agree / 0 disagree,
  22 rules proved. Installation and real-boot controls are included in the full gate.

## Clink 92 (2026-09-14) — primitive bodies outside the top-level context

- Generalize all 16 primitive-row proofs and `StepSpec` to arbitrary `Ctx`/ivar spine.
  A method frame previously could type a local but not `x + y`: the dispatch proof
  demanded `ctx0`. Make its real premise explicit (`nameFreeN`), including equality's
  reverse-dispatch exclusion. String receivers additionally need the existing base-chain
  guard; nominal String membership alone does not exclude program subclasses.
- `SemAllCtxA` and `SemSafeCtxA.prim` thread distinct contexts, locals, and spines through
  receiver then arguments. Dispatch guards concern the **final** context, since evaluating
  either can change the heap. The old registered primitive rule specializes this proof;
  no duplicated evaluator or weaker top-level safety contract.
- Upgrade the installed-method pilot from identity to `add(x, y)`. Its body is proved
  against the two Integer annotations at arbitrary context/spine (with the `+` guard),
  then composed through full installation conformance and actual dispatch for every
  pair of Integers. No per-call body inference or concrete-body safety proof. Context/
  checked-signature integration in the validator remains owed; no method admission yet.
- All new proofs are axiom-clean; the composition and installed-call modules build in
  under a second (the largest rebuilt primitive module took 25 seconds).
- Full quiet ratchet GREEN: fragment 49, checker reach 51, 252 agree / 0 disagree,
  22 rules proved. The annotation-body and actual installed-call proofs are in the gate.

## Clink 93 (2026-09-14) — context-indexed control flow

- Complete the seven literal rules at arbitrary context/spine. Generalize sequence
  evaluation to `SemSeqCtxA`, threading each statement's outgoing index into the next;
  both the old registered rule and the two-expression convenience form now reuse it.
- `RunSpec.weaken` transports final conformance/result typing without weakening safety.
  A context-general frame composition proves both conditional forms. Branches must agree
  on outgoing context/spine; only locals/result types join. The omitted-else branch must
  preserve the condition's context/spine. Different declaration tables or ivar effects
  require a proved join, not an optimistic merge. Existing registered rules specialize
  these proofs and retain all previous behavior.
- Gate controls include a generic annotated Integer body with string allocation before
  an arithmetic conditional, an omitted else, and multi-statement literal sequences.
  No concrete call values enter the body proof. Arrays, hashes, and bare names are the
  remaining context-specialized expression proofs before the judgment/checker migration;
  method definitions/calls remain rejected. No coverage increase claimed.
- New proofs are axiom-clean and build in under a second. Full quiet ratchet GREEN:
  fragment 49, checker reach 51, 252 agree / 0 disagree, 22 rules proved.

## Clink 94 (2026-09-14) — complete the fragment's context-general proofs

- Arrays use `SemAllCtxA`; hashes use `SemPairsCtxA` with separate key/value state
  transitions. Generalize allocation conformance and the accumulator proofs without
  changing first-order retention or duplicate-key behavior. The old registered rules
  specialize the new ones. Body controls cover nested collections from an annotated
  Integer parameter and a key assignment whose binding is consumed by its value.
- Bare `x` needs explicit absence guards for `x` and `method_missing`, plus `selfTy = none`;
  the old proof obtained them by reducing `ctx0`. Defining either name cannot silently
  retain the missing-name proof. The guard failures and the generic rule are controlled.
- All 16 expression rules now have `SemSafeCtxA` counterparts, and all three list
  companions thread full state indices. This completes the semantic prerequisite for
  the judgment/checker migration, not the migration itself. Definitions must still
  consume annotation-checked bodies and calls must consume checked signatures; both
  remain rejected by `validateD` until that connection is proved.
- All new proofs are axiom-clean; collections build in under a second and bare-name
  dispatch in 3.4 seconds. Full quiet ratchet GREEN: fragment 49, checker reach 51,
  252 agree / 0 disagree, 22 rules proved.

## Clink 95 (2026-09-14) — annotations, not observed argument types

- Pin the user's failure mode: `x + 1` checks at `x : Integer` but not at
  `x : T.nilable(Integer)`. The body-level checks already distinguish these, independently
  of the still-gated declaration rules. Permanent definition controls reject both an
  uncalled nilable-annotated body and the same definition followed only by an Integer call.
- Interpreter controls show why call samples are insufficient: the Integer call returns
  2, while the admitted-by-annotation nil call is type-stuck. Neither call results nor
  caller-local types may replace the declared parameter environment during body checking.
- CRuby reproduces `2` / `NoMethodError`. Full quiet ratchet GREEN: fragment 49,
  checker reach 51, 252 agree / 0 disagree, 22 rules proved; no coverage claim for these controls.

## Clink 96 (2026-09-14) — context-indexed judgment and registry

- `DJudge` and all three companions carry separate incoming/outgoing contexts and ivar
  spines. Copy guards and transitions from the proved `SemSafeCtxA` rules: assignments
  invalidate captured spines; primitive guards read the post-argument context; branches
  agree on context/spine and join local/result types. No new expression rules.
- `DFam`, generated obligations, and the mutual `djudge_certified` bridge now quantify
  over these indices. `dregistry_context`/`djudge_context` compose to the generic run
  contract. Old safety/invariant statements remain valid top-level specializations.
  A syntactic `x + y` derivation from Integer annotations crosses the generalized registry.
- Trailing `optParam` indices preserve existing corpus notation. First-class family values
  require `@DJudge` (etc.) or Lean eagerly specializes their default indices. No wrapper
  inductive or raw body judgment bypasses the four-field registry.
- The executable checker still returns top-level-specialized certificates in this batch;
  its outgoing-state data and checked-signature integration remain next. A generic branch
  checker will need proof-producing context compatibility, not an unchecked `BEq`: `Ctx`
  contains nested syntax and has no `DecidableEq` (automatic deriving on the mutual syntax
  is unsupported). No declaration-only accepts and no coverage increase are claimed.
- Registry and bridge build in under a second, axiom-clean. Full quiet ratchet GREEN:
  fragment 49, checker reach 51, 252 agree / 0 disagree, all 22 rules proved.

## Clink 97 (2026-09-14) — context-aware certificate replay and a checked-body call

- `check` and all companions now take incoming context/spine and return all outgoing
  indices in `Certified*`, backed by the same `DJudge` proof. Sequential subchecks consume
  those outputs; assignment/dispatch guards are no longer replaced by top-level `rfl`s.
  `DTyped` existentially carries the outputs; `validateD_safe_boot`/`_run` remain unchanged.
- `CtxEq` proves the existing conservative syntax comparator sound by mutual functional
  induction, then checks every context field and returns an optional equality proof.
  Branches cast only with that proof and decidable spine equality. This is not full
  decidable syntax equality: unsupported `exprEq`/`paramEq` cases return no proof, even
  on identical syntax. Such comparisons decline, not merge. No unchecked BEq cast.
- Method-context controls replay primitive bodies and both conditional forms, preserve
  the returned method context, reject an overridden primitive name, and distinguish
  Integer from nilable-Integer annotations. Different method bodies compare unequal.
- `certified_context`/`certified_safe` interpret a result at arbitrary indices. The installed
  `add(x, y)` pilot now consumes a data certificate checked at its Integer annotations
  through this bridge, then proves actual dispatch safe for every pair of Integers.
  Move its import after the bridge (via `Safety`) to avoid a dependency cycle; the full
  gate still builds it. No per-call inference or body-execution shortcut.
- Definition/call rules and the checked-signature invariant remain owed. This is body
  replay connected to a real call, not whole-program method admission or a 052 claim.
- Context comparison builds in 4.1 seconds; checker, bridge, and installed-call pilot each
  build in under a second, axiom-clean. Full quiet ratchet GREEN: fragment 49, checker
  reach 51, 252 agree / 0 disagree, all 22 rules proved.

## Clink 98 (2026-09-14) — a checked signature is a body artifact

- `checkMethodBody` checks a `defDecl` certificate against the actual definition: name,
  required parameter names/order, first-order non-alias parameter types, first-order return
  type, and the body at precisely those annotations. Its `CheckedBody` stores the `DJudge`
  proof, with unchanged context/spine but arbitrary outgoing locals. Caller locals and
  argument values are not inputs. Return compatibility is exact until semantic subsumption
  is proved; the legacy `subTy` is not evidence of denotation inclusion.
- `checked_body_context` sends the stored derivation through the same registry;
  `checked_method_runSpec` consumes the artifact at actual method entry. The installed
  `add` pilot now checks its entire signature and calls through this API for arbitrary
  Integer arguments. Neither a raw body hint nor a return assertion can fill its premise.
- Controls distinguish wrong returns, renamed/missing/extra formals, wrong definition
  names, aliases, and unsupported bodies. Nullable identity succeeds; nullable `x + 1`
  fails even though Integer callers would work. These are body-artifact checks, not
  whole-program definition accepts. Installation/order-sensitive callable tables and the
  `defDecl`/`callSig` rules remain owed; no 052 or declaration-only coverage is claimed.
- Artifact checker, bridge, and installed-call proof each build in under a second,
  axiom-clean. Full quiet ratchet GREEN: fragment 49, checker reach 51,
  252 agree / 0 disagree, all 22 rules proved.

## Clink 99 (2026-09-14) — conformance must describe the code dispatch executes

- `DefsOk` previously pinned only parameters/body/undefined. That is insufficient for
  consuming a body proof: a builtin ignores the body; a captured method binds a different
  environment. Add `TopMethodCode`: Object owner/cref, no alias super-name, builtin,
  captured frame, predeclared locals, or prelude provenance. Visibility remains unrestricted
  for implicit-self calls. Installation now proves these fields and transports old entries
  unchanged. The ordinary definition constructor discharges them from its real frame.
- `defsOk_lookup` derives the actual lookup hit from the conformance table and the
  receiver's ancestor chain. `checked_top_call` uses that hit and a stored `CheckedBody`,
  with no independently chosen runtime method. The installed `add` pilot now goes through
  this route; its boot check additionally pins cref. Negative metadata controls cover the
  routes that would invalidate ordinary body entry while leaving the syntax fields unchanged.
- This is a necessary strengthening before method admission, not a bug in an already
  admitted method rule. Physical method-ready frame facts still need to enter conformance;
  the checker still declines whole-program methods. User status question answered explicitly:
  body/call pilot proofs are not an end-to-end `validateD` example.
- State, installation, lookup, and pilot proofs each build in under a second, axiom-clean.
  Full quiet ratchet GREEN: fragment 49, checker reach 51, 252 agree / 0 disagree,
  all 22 rules proved. Reach has not increased.

## Clink 100 (2026-09-14) — method-ready facts belong in conformance

- `Scope.runtimeMain` requests the ordinary main-receiver world (at top level and inside
  its methods); false imposes no such restriction. `ctx0` requests it. `StateOk.runtime`
  then supplies `MainReady`: receiver, owner, cref, no capture, user-code phase, live ordinary
  payload, Object-headed ancestors, nominal membership, class presence, and a quiet hook.
  `mainReadyB` is checked by the existing `bootOkB`, not a second validator hypothesis.
- Transport is proved across allocation, local writes, frame entry/return, and method-table
  writes. `Ext` alone does not pin `preludeMode`, so `StateOk_ext` explicitly requires phase
  preservation; all allocating callers prove it by `rfl`. Frame transport likewise pins
  capture and phase. Hook mutation is excluded explicitly at method writes. Branch context
  equality compares the new flag, so a merge cannot silently discard the runtime contract.
- `checked_top_call` now obtains its physical dispatch/entry facts from conformance. Both
  method pilots use ordinary `bootOkB`; remove their extra method-only boot gates. This closes
  the known invariant gap, not the expression-rule/checker integration: no new method program
  is accepted yet. The checked body artifact still cannot be replaced by signature data.
- Runtime and state-transport proofs build in under a second; context equality stays at
  4.1 seconds. All are axiom-clean. Full quiet ratchet GREEN: fragment 49, checker reach 51,
  252 agree / 0 disagree, all 22 rules proved.

## Clink 101 (2026-09-14) — generic definition and call obligations compose

- `topDeclCtx` reserves the name and records the installed definition; `topBodyCtx` selects
  its method frame. `SemSafeCtxA.defDecl` installs the actual method and transports the full
  state, requiring a body proof at its declared parameters/return even when uncalled.
- `SemAllCtxA.startArgs` handles arbitrary ordinary argument lists, carrying each prior
  argument's first-order denotation through later evaluations. Its callback receives the
  final context/locals/spine and typed values. `SemSafeCtxA.callSig` composes that walk with
  actual installed lookup, the annotation-based body proof, and caller restoration.
- Move semantic resolution/application below the syntactic bridge (`MethodResolve`);
  the checked-artifact adapter remains in `MethodLookup`. Otherwise importing the semantic
  call obligation into the registry would create a cycle through `checked_body_context`.
- A composed `def add …; add(x, y)` theorem now works for arbitrary Integers from `bootOkB`,
  using one `CheckedBody` for both rule premises. The full gate builds this control.
  Its `validateD` rejection stays explicit: no new judgment constructors, registration,
  or executable definition/call admission yet. Next is caching already-checked body proofs
  and consuming their signatures at calls, not re-inference from particular arguments.
- Definition, argument, call, and composed program proofs each build in under a second,
  axiom-clean. Full quiet ratchet GREEN: fragment 49, checker reach 51,
  252 agree / 0 disagree, all 22 registered rules proved. No reach increase is claimed.

## Clink 102 (2026-09-14) — definitions and calls validate end to end

- Register `defDecl`/`callSig` with explicit annotation-body premises. Move `CheckedBody`
  and `checkMethodBody` into the mutual checker: definitions check once at declared parameter
  and return types, including uncalled bodies. Calls consume cached proofs and compare their
  arguments to the declared types; neither caller locals nor particular values type the body.
- Cache entries carry their full context/spine. Reuse requires proof-producing context
  equality and installed-definition membership. Thread caches through all evaluation orders;
  a compatible branch may retain either universal proof. No context weakening is assumed:
  later installations can stale earlier entries. 057 needs transport or definition-time
  refresh; recursive signatures still cannot bootstrap a proof. Return/argument compatibility
  remains exact until semantic subsumption is proved.
- The old bridge's recursion happened to decrease on expression size. A call's stored body
  breaks that measure. Replace it with explicit mutual derivation induction (`DJudge.rec`),
  keeping list hypotheses inside the proof instead of separate recursive wrappers. The bridge
  builds below a second, at the default heartbeat limit, with only standard Lean axioms.
- Controls cover positive define-and-call, zero args, body-local writes/caller isolation,
  nullable identity, wrong arity/type/return, uncalled annotation violations, unsupported and
  recursive bodies, and stale/replaced definitions. The nullable increment stays rejected
  even with only Integer calls. 052's worked derivation independently exercises both new rules.
- Measured ascent: 052, 055, 058, 059 accepted; fragment 49→53, checker reach 51→56,
  registered rules 22→24, worked theorems 44→45; 0 owed/exempt. Agreement remains
  252 / 0 disagree. All corresponding floors raised; full quiet ratchet GREEN.

## Clink 103 (2026-09-14) — refresh annotated bodies at definition boundaries

- A new definition enlarges `Ctx`, so old body proofs cannot be cast into it. Store each
  body's certificate hint beside its checked artifact; `refreshBodies` replays oldest first
  at the new context before checking the new definition. Replay takes parameter/return types
  from the existing artifact, not from the hint or call arguments. Calls remain cache lookups.
- This supports acyclic method dependencies without changing the judgment or semantic rules.
  Refresh rechecks dispatch guards; a new definition that invalidates an older body is refused
  even if it is never called. This conservatively performs quadratically many body replays;
  dependency-sensitive transport is a later optimization, not an unchecked weakening now.
- Controls cover `inc(inc(x))`, three-deep dependencies, calling older methods after refresh,
  uncalled/called nullable-annotation violations, wrong returns, invalidated primitive guards,
  tampered replay hints, and fuel exhaustion. Recursive signatures still cannot prove themselves.
- Measured: 057 now validates, fragment 53→54, checker reach 56→59; 060 recursion is next.
  The registry remains 24 proved rules, 0 owed/exempt; worked examples remain 45.
- Correct 057's legacy metadata: its source checks a predecessor, not a forward reference.
  Forward references remain a target; no source-order-independent admission is claimed.
- Full quiet ratchet GREEN: 252 agree / 0 disagree; annotation controls and the unchanged
  axiom-clean semantic bridge pass. `Check` builds in 1.1s; method controls in 0.3s.

## Clink 104 (2026-09-14) — guard recursive calls by actual execution fuel

- A cached signature cannot prove its own body. `RunSpecAt N` bounds both safety and answer
  typing; `∀ N, RunSpecAt N` is proved equivalent to the old `RunSpec`, not a weaker target.
  Its continuation composition bounds the inner run too (`safe_pushK_le` still required
  unbounded inner premises). `runA_rest_le` supplies the remaining-budget inequality.
- Bounded method entry reuses conformance, annotated binding, lookup, and caller restoration.
  Extract `methodFrame_continue_spec` so bounded/unbounded paths share the return proof.
  Bounded argument evaluation feeds `SemSafeCtxAt.callSig`: body/arguments at N, call at N+1.
  This strict decrease is paid by `stepFn`, not by a guessed numeric termination measure.
- The guarded induction closes `def spin(x); spin(x); end; spin(0)` semantically, for Integer
  annotations. It deliberately claims no termination. A control rejects a Boolean answer
  at Integer even at zero fuel; an unevaluated expression at zero is vacuous, so no finite
  bound alone admits a program. The recursive data certificate remains explicitly rejected.
- Next for 060: bounded expression composition, scoped recursive-body derivations, and their
  fundamental lemma before checker integration. Do not install an unchecked self-signature
  or count this semantic pilot as validator coverage. All new proof modules build below a
  second with standard Lean axioms only. Fragment/reach remain 54/59; no floor increase.
- Full quiet ratchet GREEN: all 24 registered rules proved, 0 owed/exempt, and
  252 CRuby/model agreements with 0 disagreements. The full gate builds the bounded controls.

## Clink 105 (2026-09-14) — check recursive bodies at their annotations

- Split `DJudge.lean` from `Check.lean`. Two scoped families carry the definition, parameter
  annotations, return annotation, and fixed context/spine. Closed subtrees embed ordinary
  derivations; only conditionals, primitives, and self-calls surrounding recursion need new
  rules. All six families cross `DFam`; no raw body premise bypasses the registry.
- `RecHyp N` grants the annotated body only below execution bound N, with existential outgoing
  locals. Bounded argument/conditional/primitive composition preserves the same contract.
  The real send step pays the self-call's strict decrease; `recursive` closes the hypothesis
  by strong induction. This proves every execution bound, not just checker fuel 200, and
  claims no termination. Primitive dispatch reuses its existing unbounded proof.
- `checkRec` is a proof-carrying fallback, not an unchecked cache entry. Definition-site
  body checking and refresh close the scoped proof before storing `CheckedBody`; ordinary
  calls still consume it. Annotation/name/arity/context checks remain explicit. Controls
  include factorial definition+call at Integer, divergent recursion, invalid uncalled base
  branches, nullable parameters, bad self-calls, and refresh with invalidated dispatch guards.
- Use `DJudge.rec` directly: tactic `induction` mishandled duplicate constructor names with
  differing arities across families. The fundamental lemma builds in under a second.
  Worked 060 constructs its own Church derivation; the syntax predictor distinguishes scoped
  nodes from closed embeddings, and the independent proof-term audit agrees on all seven
  new rules. No exemptions or new axioms; new files remain below 1000 lines.
- Full quiet ratchet GREEN: fragment 54→55, checker reach 59→60, rules 24→31,
  worked theorems 45→46, 0 owed/exempt, 252 agree / 0 disagree. 061 classes is next;
  explicit return, forward references, and mutual recursion remain separate frontiers.

## Clink 106 (2026-09-14) — instance reads and the constructor frame boundary

- Prove self/ivar reads at arbitrary `Ctx`/locals/spines. Spine lookup respects first-binding
  shadowing; absence uses `SelfSpineOk`'s completeness clause, not a lower-bound assumption.
  `ignoreResult` permits a void/ignored result only after safety and outgoing conformance
  are proved. 061's initializer manifest uses `.any`, so body checking must preserve those
  obligations even though its returned value is discarded.
- Before attempting write preservation, refute the old frame contract (§F33): assigning
  Integer to an unset ivar destroys a first-order instance type asserting nil there.
  `nil_ivar_write_not_framed` is generic; a small concrete heap supplies a kernel-checked
  witness and actual assignment step, without claiming boot conformance.
  A second witness uses a distinct array containing the receiver: excluding `self` alone
  from retained values would still be unsound.
- Prove what `bindIvar` does preserve: all fields except ivars, heap size, dispatch metadata
  (`Proof.IvarOnly`), and other objects. These are reusable write facts, not a substitute
  for retained-value preservation. The next structural task is refined framing for mutable
  self/constructor ownership; simply adding `ivarAsgn` under `Framed` cannot work.
- The full gate imports all new controls; no checker/registry admission or floor change.
  New proof modules build in under a second with standard Lean axioms only.
- Full quiet ratchet GREEN: fragment/reach remain 55/60, 31 proved rules, 0 owed/exempt,
  46 worked theorems, 252 agree / 0 disagree. The class frontier remains open.

## Clink 107 (2026-09-14) — preserve callers across fresh initialization

- `InitGrow` anchors old-object equality before allocation; it permits fresh ivars and
  ignores frames. Keep class payloads/ancestors fixed and retain `freshBasic`: arbitrary
  conformant states may contain dangling references. Exact instance denotations supply
  their own old liveness, so their ivars agree without `Ext.freshIvars`. A mutual type/spine
  induction preserves all first-order denotations, including nested collection aliases.
- Existing allocations imply `InitGrow`; it composes and survives repeated `bindIvar`
  writes to receivers fresh relative to the original anchor. `Framed.of_initGrow` recovers
  the unchanged universal frame after stack balance and frame isolation are supplied.
  Factor method-frame restoration out of heap transport; ordinary method callers retain
  their existing contract. `initializer_pop_framed` uses the separate heap/frame anchors.
- Controls cover two real writes with arbitrary Integer values, the initialized result
  shape, caller publication at any conformant heap (also actual boot), and refusal of the
  old `Ext` relation for that result. F33's old-object/array-alias refutations remain gates.
  No class admission: an initializer body still needs a scoped safety/state/effect judgment
  checked from annotations; the publication lemma is not a body certificate.
- New modules build in under a second, with standard Lean axioms only. No floor changes.
- Full quiet ratchet GREEN: fragment/reach 55/60, 31 proved rules, 0 owed/exempt,
  46 worked theorems, 252 agree / 0 disagree. 061 remains the next expected acceptance.

## Clink 108 (2026-09-14) — the initializer's semantic body contract

- `SemInitA` uses `InitRunSpec`, not the impossible interior `Framed` claim. It retains
  all-fuel safety, answer typing, and full outgoing `StateOk`, plus fresh writable self,
  frame isolation/balance, and `InitGrow` at the preallocation anchor. `InitFrame.publish`
  connects its answers to the unchanged caller frame contract. Step, answer, continuation
  composition, rebasing, and weakening are proved against the actual runner.
- `StateOk_bindIvar` transports structural/dispatch facts, including hash defaults and
  runtime readiness. The six value-sensitive components are explicit postconditions:
  locals, fields, block, self, constants, and constant paths. Behavioral assumptions
  transport through `Later`; no universal old-field preservation is smuggled back in.
- Field updates use first-visible lookup plus completeness. Prove spine shape, lookup after
  `ivarSet`, unchanged other slots, and reconstruction with first-binding shadowing. Local
  reads and alias equalities remain unchanged, but each retained local/field denotation must
  be supplied at the post heap. Duplicate-field controls cover hidden incompatible types.
- `InitExpr` composes variables, assignments, and arbitrary nonempty sequences. Its write
  premise is a semantic preservation obligation, not certificate data. The 061 body pilot
  discharges it for the annotated Integer environment, proves both writes and full outgoing
  conformance, then safely forgets only the return value (`void` → `.any`). No concrete call
  arguments occur in this proof. A corollary recovers the initialized instance type; a
  wrong-result control refutes the run contract even at fuel zero.
- This is not checker admission. Next add the scoped syntactic body/sequence families to
  the registry and annotation-checked certificate path, then class installation and calls.
  No signature may bypass that body proof. New modules build in under a second and use
  standard Lean axioms only; no existing rule or floor is weakened.
  Do not blindly embed ordinary derivations: `Framed` alone does not imply `InitGrow`
  (method-table installation is one counterexample). Each admitted subtree needs its effect proof.
- Full quiet ratchet GREEN: fragment/reach 55/60, 31 proved rules, 0 owed/exempt,
  46 worked theorems, 252 agree / 0 disagree. 061 remains outside the checker.

## Clink 109 (2026-09-14) — executable write-preservation obligations

- `IvarStable` is a sufficient type predicate, not a replacement for ownership/effect
  reasoning. It covers scalars, nominal classes/empty-spine instances, nullable/union
  types, and recursively stable arrays/hashes; field snapshots and captured/behavioral
  types decline. Prove denotation equivalence through `bindIvar` by type/spine induction.
- `writeTypesB` checks the assigned type, retained locals/fields, self, block, and constants.
  Fields use first-visible lookup and skip the overwritten name, so hidden duplicates or
  an overwritten old snapshot do not reject needlessly. Aliases preserve value equality;
  their underlying local types must still be stable. Both lexical and qualified constant
  conformance follow from the checked constant-table entries.
- `InitState.bindIvar` discharges all six value-sensitive components of `StateOk_bindIvar`;
  `SemInitA.ivarAsgnChecked` now has a Boolean guard ready for a constructor-mirroring
  certificate checker. No empty-block/constant-table assumption is needed. Replace the
  Integer-only Point pilot lemma with this generic proof; also prove a collection-parameter
  write with a non-void collection return. Controls independently refute unstable assigned
  values, locals, fields, self, blocks, constants, and nested collection aliases.
- Keep registration with end-to-end class integration: the zero-exemption coverage gate
  requires new rules to occur in whole-program corpus proofs, not only body pilots. No new
  expression judgment or checker acceptance is claimed by these type predicates.
- Full quiet ratchet GREEN: fragment/reach 55/60, 31 proved rules, 0 owed/exempt,
  46 worked theorems, 252 agree / 0 disagree. New proof modules build in under a second,
  using standard Lean axioms only.

## Clink 110 (2026-09-14) — carry fresh-class prerequisites through the invariant

- Reuse `RubyCore.Proof.Judgment.ClsFresh`'s operational/heap lemmas, not its judgment.
  The real default-superclass path allocates a class and its eigenclass, registers the
  constant, and pushes the class-body frame. It needs Object's eigenclass already cached
  and class/dispatch edges in bounds; ancestor-fuel saturation proves neither.
- `ClassReady` carries these facts in `CoreOk`, reflected by the existing `bootOkB` gate.
  Allocation, method installation, and ivar writes preserve it; same-heap transports reuse
  it. `Ext` needs an explicit edge-preservation implication, not an unconditional premise
  that would break reflexivity on arbitrary heaps. The non-class producer derives its
  fresh class pointer's bound from BasicObject ancestry and reuses `chainsIn_push`.
- A counterexample explains that strengthening: a fresh object's eigenclass can point to
  BasicObject while its hidden `klass` dangles. Old-object equality and `freshBasic` do not
  imply `ChainsIn`. This is not a claim that the existing literal producers were unsafe.
- `stepFn_class_fresh` consumes full state conformance and reduces the actual entry to the
  model's composite. Name registration and post-creation readiness are proved; real-boot
  controls check the pushed frame and both fresh ancestor chains. No fixed allocation id
  is baked into the theorem. Replace the temporary class probe with these gated controls.
- No class acceptance yet: full body-state transport, annotation-checked body families,
  and constructor entry/return still owe their proofs. No registry or floor changes.
  New proof modules build in under a second, with standard Lean axioms only.
- Full quiet ratchet GREEN: fragment/reach 55/60, 31 proved rules, 0 owed/exempt,
  46 worked theorems, 252 agree / 0 disagree. 061 remains the next expected acceptance.

## Clink 111 (2026-09-14) — fresh-class heap publication preserves old types

- `ClassHeap` transports the observations first-order types actually read: successful
  class-name resolutions, nominal/exact instance membership, ivars, and array/hash payloads.
  Registration changes Object's class payload and creates two more, so the old `Ext` and
  `InitGrow` relations do not apply. Reuse the model's old-id and fresh-chain facts instead.
- Preserve successful names, not absence: the newly registered name was unbound. A boot
  counterexample forces the composite to overwrite String and refutes `DataPres`; it is
  intentionally not the actual Ruby reopen branch. The fresh-name guard remains essential.
- Do not assume all values are live. A dangling reference may already have a nominal
  BasicObject type. `ClassReady` now also pins BasicObject ancestry for Class and Object's
  eigenclass, checked at boot and transported everywhere. These are exactly the two chains
  the newly allocated objects use. Live exact instances retain their eigen/klass and fields;
  successful collection projections pin their references in range.
- `DataPres` factors the type/spine induction out of initializer publication and reuses it
  for class creation, covering nested collections and instance snapshots. It is a heap
  preservation contract, not another expression judgment. `Framed.of_freshClass` recovers
  the unchanged full caller contract once frame balance/isolation are supplied.
- Boot publication and nested-snapshot controls join the full gate. Full outgoing class-body
  state, annotation-checked method installation, and constructor entry/return remain next;
  no class rule, admission, or floor changes. New proofs build in under a second, axiom-clean.
- Full quiet ratchet GREEN: fragment/reach 55/60, 31 proved rules, 0 owed/exempt,
  46 worked theorems, 252 agree / 0 disagree. 061 remains the next expected acceptance.

## Clink 112 (2026-09-14) — preserve queries at fresh class dispatch sites

- `ClassDispatch` maps fresh class/eigenclass lookup to Object/Object's eigenclass;
  old live sites stay fixed and out-of-range sites remain methodless. Native-name shadow
  prefixes need a separate proof: identical modeled lookup does not imply identical
  dispatch. `NativeQuiet` retains explicit guards for the class and eigenclass names;
  eventual class admission must discharge them, not whitelist the Point control.
- `ClsQueryOk` previously covered only existing class-object receivers. A fresh eigenclass
  dispatches directly through Class, which those receivers need not expose. Extend its
  domain with that site, including the existing boot Bool and all state transports.
  Do not freeze Class's eigenclass or drop the invariant to make preservation go through.
- A heap countermodel redirects old class receivers through Module and gives Class an
  incompatible `to_s`: readiness, saturation, and every old receiver check pass, but an
  actual fresh-class entry exposes the bad direct-Class path. The strengthened check
  rejects it. This is an invariant countermodel, not a reachable-program claim.
- `ClassQueries` proves preservation of QueryOk, ClsQueryOk, and NilQueryOk; real boot Point
  entry composes all three. A forced native-name composite separately checks that lookup
  inheritance can coexist with a native shadow. Controls join the full safety build.
  Proof modules build in under a second, with standard axioms only. No new class admission,
  signature-only acceptance, registry rule, or floor change: full class-body conformance
  and annotation-checked instance-method/constructor integration remain next.
- Full quiet ratchet GREEN: fragment/reach 55/60, 31 proved rules, 0 owed/exempt,
  46 worked theorems, 252 agree / 0 disagree. 061 remains the next expected acceptance.

## Clink 113 (2026-09-14) — class entry preserves builtin and installed-code conformance

- `ClassCore` preserves primitive dispatch/errors, String/Array/Hash payload contracts,
  and every CoreOk field. Primitive rows start at old bounded ids, so both lookup and
  native shadow prefixes stay fixed. Regexp's live id follows from its named-class fact,
  not the smaller boot-id bound used by primitive rows.
- `ClassHeap.get_nonclass` pins the entire object whenever the successor has no class
  payload, including out-of-range ids; both new objects are classes. This preserves hash
  defaults as well as array/hash dispatch. String's converse-shaped invariant separately
  excludes both fresh ids from String dispatch. Move `ClassReady.freshClass` into the heap
  module so these semantic facts need not import typed execution proofs.
- Core-name preservation handles a newly bound name as well as old bindings: CoreOk permits
  the absent IOError constant to become a class. Do not blanket-ban core names; the fresh-name
  premise already prevents overwriting String/Regexp. Both Point and IOError entry are checked.
- `ClassMethods` preserves own method lists (empty for fresh ids), exact code lookups,
  ClassesOk, DefsOk including ordinary-method metadata, and MethodsExact. No body text is
  installed early and no annotation becomes its own proof. `class_entry_core` composes all
  nine conformance components through the actual step from arbitrary conformant states.
- New controls join the full gate; modules build in under a second, with standard axioms
  only. Remaining class-body scope/constant/negative facts and checked constructor integration
  are still required before 061 can be admitted. No rule, floor, or exemption changes.
- Full quiet ratchet GREEN: fragment/reach 55/60, 31 proved rules, 0 owed/exempt,
  46 worked theorems, 252 agree / 0 disagree.

## Clink 114 (2026-09-14) — fresh class scope and caller restoration

- `ClassFrame` proves the actual fresh frame is live, uncaptured, outside a method, without
  a block or inherited locals, with an empty complete ivar spine and self at `.clsOf name`.
  Move the class-name registration lemma into the heap module to keep this below typed rules.
- `ClassConstants` transports inherited constant lookup on old chains for names other than
  the newly registered name. The fresh class's empty own table adds no lexical shadow;
  the new name resolves directly through Object's updated table. Together with incoming
  main scope and ConstScopeOk, this proves the outgoing ConstScopeOk without assuming every
  inherited scope is empty. A class-local Integer binding refutes extending that conclusion
  beyond an empty scope; it is a regression control, not an admitted constant-write rule.
- `ClassReturn` separates the pre-allocation heap anchor from the post-entry body anchor.
  Compose `Framed.of_freshClass` with uncaptured-frame restoration to recover full caller
  framing and first-order local types; no weaker caller contract or same-heap assumption.
  Reuse the method-return machinery, exposing its existing uncaptured-local lookup lemma.
- `class_entry_scope` composes nine frame/scope facts through actual entry. Execution controls
  check new/existing/missing names and `x = 7; class Point; x = 9; end`: body result 9,
  caller x still 7. All new proof modules build in under a second, with standard axioms only.
  Full context assembly, remaining negative/constant-table invariants, and checked
  instance-method/constructor integration remain required; no rule or admission changes.
- Full quiet ratchet GREEN: fragment/reach 55/60, 31 proved rules, 0 owed/exempt,
  46 worked theorems, 252 agree / 0 disagree.

## Clink 115 (2026-09-14) — preserve builtin ancestry across class creation

- A countermodel passed the **complete previous boot-check conjunction**, verified before
  changing the invariant: Object's eigenclass points to Float, with Float's `===`/`to_s`
  entries made compatible with the class-query rows. Fresh Point creation then introduces
  a proper Float subclass via its new eigenclass, violating BaseChainsOk. This is an
  invariant countermodel, not a reachable-program bug or an admitted class program.
- `ClassReady.eigenSeparate` excludes builtin value bases as Object's eigenclass. The same
  boot gate checks it; allocation, definitions, ivar writes, and class creation preserve it.
  Share the existing base table in `BuiltinBases`, rather than duplicate a blacklist or
  freeze a concrete eigenclass id. Split `coreDataB` from readiness to retain an executable
  audit of every old check while confirming the strengthened check rejects the countermodel.
- `ClassBases` proves all BaseChainsOk clauses: preserve positive names/chains; invert new
  resolutions only at old ids; exclude each fresh class from builtin-base descent using
  Object's distinct id and the new metaclass-separation fact. All old and out-of-range sites
  are covered. A dangling constant can become an alias to the new class, so unrestricted
  reverse name preservation is false; a control checks that case still preserves base chains.
- `class_entry_bases` composes the proof through actual class entry and joins the full gate.
  New modules build in under a second, with standard axioms only. Full context assembly,
  receiver-sensitive absence facts, constant/path-table transport, and checked instance
  methods/constructors remain; no rule, exemption, floor, or admission changes.
- Full quiet ratchet GREEN: fragment/reach 55/60, 31 proved rules, 0 owed/exempt,
  46 worked theorems, 252 agree / 0 disagree.

## Clink 116 (2026-09-14) — preserve absence facts when class entry changes self

- A fake prelude `lambda` on Object's metaclass passed the complete previous boot check,
  verified before changing the invariant. Fresh Point self then reached that unrecorded,
  nonbuiltin method. This is a heap-invariant countermodel, not a reachable Ruby bug.
- `NameFreeOk` covers two dispatch sites: current self and the Object class object. Fresh
  class self inherits the latter. A heap-global or all-class-object condition is false at
  real boot because of the shim's `T.proc`; retain that positive countercontrol. The existing
  boot checker tests actual absence at both sites, retaining the stronger fact BareNameFree
  needs. Allocation, local assignment, reframe, method installation, and ivar writes preserve
  the enlarged domain; reservations still disable absence rules without granting a method.
- `ClassNames` maps both successor sites to old sites and proves NameFreeOk through actual
  fresh class entry. Controls include real boot and Point entry. New modules build below
  one second, with standard axioms only. No rule, admission, exemption, or floor changes;
  full class-body conformance and annotation-checked instance methods/constructors remain.
- Full quiet ratchet GREEN: fragment/reach 55/60, 31 proved rules, 0 owed/exempt,
  46 worked theorems, 252 agree / 0 disagree.

## Clink 117 (2026-09-14) — preserve existing declared-class contracts

- `ClassDeclared` transports all DeclClassOk clauses through fresh registration: BasicObject
  membership, non-module/class status, constructor metadata/native-shadow/miss guards,
  initializer absence, and both directions of named ancestry. ClassesOk supplies the old
  positive resolutions, so fresh registration cannot silently activate a formerly vacuous
  declaration. Reverse ancestry uses old-id-bounded name inversion, not global name equality.
- The new class is deliberately not advertised by this lemma. An execution control shows
  why: even with no own methods, it can inherit Object#initialize with a required argument.
  A default zero-argument constructor needs a real lookup premise, not an empty-table test.
  A positive control finishes Older then enters Point, retaining Older’s constructor and
  ancestry facts. Both controls then call Point.new: the empty default constructor succeeds,
  while the inherited required argument produces ArgumentError. `class_entry_declared`
  composes the proof through the actual class step.
- New modules build below one second, with standard axioms only. No rule, admission,
  exemption, or floor changes. Constant/path-table transport, full state assembly, and
  annotation-checked instance-method/constructor integration remain required.
- Full quiet ratchet GREEN: fragment/reach 55/60, 31 proved rules, 0 owed/exempt,
  46 worked theorems, 252 agree / 0 disagree.

## Clink 118 (2026-09-14) — full conformance at fresh class-body entry

- `ClassTables` proves bare/qualified constant and nested-class conformance. Bare constants
  cannot collide with a genuinely fresh name: ConstsOk plus ConstScopeOk already rules that
  out. Qualified claims are conditional on owner/value existence, so naive transport fails.
  Controls separately activate an absent owner, change a leaf under existing Object, and
  activate a differently named dangling alias; an untouched LIMIT remains Integer.
- `ClassTablesFrame` makes the input obligations explicit: first-order values, already
  resolved qualified owners, and untouched qualified leaves. This is a conservative frame,
  not a postcondition or an admission route. It is vacuous for empty tables; nonempty tables
  require these proofs, not merely owner != the fresh name. More precise shadowing-sensitive
  frames may relax the leaf condition later. Behavioral assumptions remain empty because
  their existing Later relation does not permit class registration.
- `classBodyCtx` changes scope only: frame/block absent, self at `.clsOf name`, no main-world
  requirement. It does not install the class's future methods or advertise a constructor.
  `ClassNative.nativeFrameB` checks both new native names for each still-unreserved query,
  with a kernel soundness proof; Point/IOError pass and String fails.
- `FreshClass.state` assembles **all** StateOk fields, using the preceding heap, dispatch,
  ancestry, method, frame, and constant proofs. `class_entry_state` connects it to the actual
  step; `boot_class_state` supplies the real-boot witness. New modules build below a second,
  with standard axioms only. Registration in the positive class table, annotation-checked
  method bodies, constructor integration, and outgoing state remain; no rule or admission
  changes and no signature-only shortcut.
- Full quiet ratchet GREEN: fragment/reach 55/60, 31 proved rules, 0 owed/exempt,
  46 worked theorems, 252 agree / 0 disagree.

## Clink 119 (2026-09-14) — ordinary instance-method metadata and installation

- A call-through countermodel changes only the builtin tag of Point#answer. The old
  ClassesOk parameter/body/undefined checks still match `def answer; 1; end`, but dispatch
  executes Object#nil? instead; `Point.new.answer + 1` becomes type-stuck. The unmodified
  definition and call return 2. This is a metadata countermodel, not validator acceptance.
- `OrdinaryMethodCode` factors the existing seven top-level code facts with explicit owner
  and cref parameters. TopMethodCode keeps its old meaning. ClassesOk now additionally
  requires InstanceMethodCode: ordinary top-level-class lexical scope, with public methods
  except private initialize. This is the current class fragment's scope/visibility contract;
  nested lexical scopes and visibility changes need separate contracts, not erased metadata.
  Existing transports preserve the stronger claim. Executable controls independently alter
  owner, cref, superName, capture, declared locals, prelude status, and visibility.
- `InstanceInstall` proves def constructs that metadata. A fresh class inherits its
  method_added lookup from Object's metaclass, so MainReady's quiet-hook fact transports;
  existing installation preserves it away from method_added. Compose through the real def
  step. Initializer privacy is explicitly checked. Proofs use standard axioms only and new
  modules build in at most 2.5 seconds.
- No signature certifies a body here, and no new rule, admission, exemption, or floor is
  added. Positive class-table publication, annotation-checked body caches, instance entry/
  dispatch, constructor integration, and outgoing conformance remain required.
- Full quiet ratchet GREEN: fragment/reach 55/60, 31 proved rules, 0 owed/exempt,
  46 worked theorems, 252 agree / 0 disagree.

## Clink 120 (2026-09-14) — publish installed instance-method records

- `classWithMethod`/`instanceDeclCtx` publish exactly one executed member, never a scan of
  the remaining body. A new first-match descriptor retains previous method records; freshness
  is an explicit premise, so overwriting a recorded body requires a different update proof.
- `ClassesOk_publish_instance` derives the installed record with all metadata and preserves
  old records. Its freshness guard is indexed by **heap owner**, not class name: unrelated
  owners can share a method name, but aliases cannot keep stale body records. Controls change
  Point#answer while Other#answer still returns 2; an Alias of Point loses its old Integer
  body record, and the actual aliased call plus one becomes type-stuck.
- `StateOk_methodWrite_tables` generalizes the existing state transport to updated class and
  def tables, retaining the old top-level API as a specialization. `StateOk_publish_instance`
  derives code/def conformance and all ordinary state fields after name reservation. It still
  requires the outgoing constructor and nested-name contracts explicitly; it does not infer
  those from signatures or empty method tables. `step_instance_publish` joins metadata,
  actual installation, and positive publication through the real def step.
- New modules build below a second, with standard axioms only. No body-safety claim, rule,
  admission, exemption, or floor changes. Scoped body-state requirements, checked-body cache,
  constructor/nested contracts, and instance entry/dispatch remain required for 061.
- Full quiet ratchet GREEN: fragment/reach 55/60, 31 proved rules, 0 owed/exempt,
  46 worked theorems, 252 agree / 0 disagree.

## Clink 121 (2026-09-14) — request the lexical class world explicitly

- Full old-StateOk counterexample: a class-valued self still permits a private-default
  activation. Defining answer there then explicitly calling Point.new.answer is type-stuck.
  This compiled before strengthening StateOk; the retained control clears only the new
  request. A second theorem rejects private defaults when the request is present.
- `Scope.runtimeClass` names the lexical owner, independently of self's type. It persists
  through withFrame: ordinary method activations share their class's owner/cref. ClassScopeAt
  pins resolution/live owner, defmod/cref/capture, user phase, effective public default, and
  quiet method_added. Effective visibility, rather than exact frame kind, permits both class
  bodies and method activations without admitting top-level private defaults. Ctx equality
  compares the request; boot has none. No global class-valued-self inference is introduced.
- StateOk carries the contract through allocation, locals, ivar writes, method installation,
  and frame switches. Entry supplies the real method frame's public default; return recovers
  the caller's. Fresh class entry derives the world from MainReady. Hook checking is shared
  with ordinary installation. `step_scoped_instance_state` now obtains metadata/hook facts
  from incoming conformance and proves actual installation plus full outgoing conformance;
  constructor/nested contracts remain explicit, and signatures still certify no bodies.
- New modules build below a second; InstanceInstall remains about 2.4 seconds. Standard
  axioms only. No new rule or admission: checked class-body caches and instance/constructor
  execution remain required for 061.
- Full quiet ratchet GREEN: fragment/reach 55/60, 31 proved rules, 0 owed/exempt,
  46 worked theorems, 252 agree / 0 disagree.

## Clink 122 (2026-09-14) — preserve open receiver fields at method entry

- A receiver's `.inst cn I` denotation is a lower bound, but the old SelfSpineOk required
  unmentioned fields to be nil. A proved counterexample precedes the change: empty open
  instance fields coexist with @extra = 7. The real define/call read_extra also returns 7.
- `Scope.closedIvars` requests completeness separately; boot/fresh class scopes retain it,
  `instanceBodyCtx` does not. Ctx equality checks the flag. State transport and checked writes
  preserve it. Unknown open reads get `.any`; known fields retain their type. This grants no
  unchecked calls or return-annotation casts. The existing Integer getter proof still works.
- `InstanceEntry` derives open self-spine/type through requiredFrame for arbitrary typed
  receivers, without concrete-call specialization. `StateOk_forgetIvars` safely erases field
  information only while opening the spine; a full-state real-boot witness has empty open
  fields and reads 7. New modules build below a second, with standard axioms only.
- No rule or admission added. Full instance-entry scope/dispatch conformance, class-body
  caches, and constructor integration remain; the absence facts for a changed receiver
  and its lexical constants must be justified rather than copied from the caller.
- Full quiet ratchet GREEN: fragment/reach 55/60, 31 proved rules, 0 owed/exempt,
  46 worked theorems, 252 agree / 0 disagree.

## Clink 123 (2026-09-14) — connect installed instance code to explicit dispatch

- `InstanceResolve` derives the exact receiver's live identity and dispatch class, recovers
  code/metadata from ClassesOk, and equates real explicit finishSend with enterUserMethod.
  Required-frame typing, self liveness, and lexical scope follow from receiver/code facts;
  phase and quiet-hook obligations remain explicit. No body safety follows merely from a row.
- `classFrontB` checks no prepends; its kernel proof establishes the MRO's first element
  through deduplication. A real prepend retains Point's answer row but calls Interceptor's
  Boolean body. A separate heap countermodel changes only a receiver's payload to Proc:
  exact nominal typing, own code, and MRO still match, yet call executes the closure. Thus
  ordinary payload cannot be inferred from the receiver type. The unmodified define/call
  controls return 1; explicit initialize correctly raises despite its valid private metadata.
- New modules build below a second, standard axioms only. No rules, admissions, or floors
  changed. Persistent class heap contracts must discharge these guards and the remaining
  scope/absence facts before full instance entry can consume an annotated body proof.
- Full quiet ratchet GREEN: fragment/reach 55/60, 31 proved rules, 0 owed/exempt,
  46 worked theorems, 252 agree / 0 disagree. Concurrent playground updates are preserved;
  their runner diagnostic's accidental shell substitutions were fixed in a separate commit.

## Clink 124 (2026-09-14) — full annotated instance-body entry

- `InstanceSite` names heap-only facts: class identity, MRO head, quiet hook, lexical constant
  agreement, and shadowable-name guarantees. `classFrontB` moved here without changing its
  meaning. Allocation preserves the site; fresh class creation establishes it. Ordinary
  receiver payload remains a separate dispatch obligation, not a restriction on `Ty.inst`.
- Fresh instances inherit Object, not its metaclass. NameFreeOk's third site now covers that
  chain; the same boot Bool and all transports cover it. A component countermodel masks x on
  both old sites while a fresh instance reaches a hidden Object#x and fails at +1. A second
  actual call fails through class-local LIMIT despite the global Integer constant value.
- `instance_enter_state` derives full StateOk when self, block, scope, and spine change;
  parameter types come from annotations, not concrete values. The real enterUserMethod
  theorem pins the actual body control. A single checked inc body supplies the body-local
  RunSpec for every Integer argument; nullable parameters and a Boolean return annotation
  reject. An independent actual class-definition/new/call returns 4.
- New modules compile below a second, standard axioms only. No new rule or admission.
  Persistent site publication across method definitions, full caller restoration, constructor
  contracts, and class/body certificate integration remain required for 061.
- Full quiet ratchet GREEN: fragment 55, checker reach 60, 31 proved rules, 0 owed/exempt,
  46 worked theorems, 252 agree / 0 disagree.

## Clink 125 (2026-09-14) — preserve instance sites through definition publication

- `InstanceSite.methodWrite` preserves identity, MRO head, constants, hooks, and negative
  names at arbitrary owners, including aliases. The written name must be reserved; a new
  method_added needs another hook proof. Recontextualization weakens only negative names.
  Ivar-only changes preserve sites without imposing a receiver-payload restriction.
- `step_scoped_instance_world` joins actual installation, positive method-table publication,
  full state, and the derived outgoing site. No outgoing site is assumed. The fresh-class
  definition control proves the site after execution; an unreserved shadowable method is
  proved to destroy it. Explicit x dispatch still returns 1; a heap-injected singleton hook
  makes a later harmless definition execute false + 1 and become type-stuck.
- New modules build in at most 1.3 seconds, standard axioms only. No rules or admissions.
  Sites remain explicit alongside StateOk; persistent conformance storage, caller restoration,
  constructors, and annotation-checked class/body certificate integration remain.
- Full quiet ratchet GREEN: fragment 55, checker reach 60, 31 proved rules, 0 owed/exempt,
  46 worked theorems, 252 agree / 0 disagree.

## Clink 126 (2026-09-14) — persist sites in full conformance

- `StateOk.classSites` covers installed class names plus the pending runtimeClass request.
  These existing Ctx fields already identify the obligations; no new certificate/context
  field was added. A site's representation depends only on the negative-name function,
  keeping caller scope out of its meaning. Shared definitions moved below State to avoid a
  dependency cycle; the same boot Bool discharges the initially empty site collection.
- All state transports preserve sites. Definition publication obtains the new member's site
  from the requested scope, retains old sites at arbitrary owners, and stores the result in
  full outgoing conformance. `InstanceSiteClass` proves fresh class creation preserves old
  sites: the new constant changes absence to a class value, but lexical/global agreement
  survives. Controls exercise that value through an old method and refute nonfresh rebinding.
- `checked_instance_entry` now recovers the installed code and site from StateOk, checks the
  argument-domain obligation at the stored body's annotations, and connects explicit dispatch
  to full body-state entry and its checked RunSpec. No separate site or method metadata is
  assumed. Its RunSpec deliberately remains body-local; ordinary payload and caller return
  are not inferred from nominal typing or from the body result.
- New modules build below a second, standard axioms only. No rules, exemptions, or admissions.
  Caller restoration, constructor/payload contracts, and class/body certificate integration
  remain required for 061.
- Full quiet ratchet GREEN: fragment 55, checker reach 60, 31 proved rules, 0 owed/exempt,
  46 worked theorems, 252 agree / 0 disagree.

## Clink 127 (2026-09-14) — preserve caller field observations

- Refuted the old frame contract before extending caller restoration (§F34). An eigenclass
  prevents every exact-instance denotation, so an ivar write can preserve all old frame
  clauses while destroying a closed caller spine. The countermodel includes full StateOk
  at an actual fresh-class entry; it is not a newly discovered accepted unsafe program.
- `FieldsPres` preserves first-order types of every field on old live objects, not exact
  field values. Heap-size monotonicity keeps the quantified domain live during composition.
  `Framed` carries this separate observation contract; the type grammar is unchanged.
  Equal heaps, allocation, definitions, fresh classes, preallocation-anchored initialization,
  and frame return prove it. Fresh constructor fields remain writable before publication.
- `method_pop_selfSpine` restores the caller's known fields and optional completeness without
  equating caller/callee self or spines. `checked_body_pop_fields` consumes the annotation
  body proof, preserving its return type and recovering caller fields. Full caller StateOk,
  constructor/payload contracts, and class-rule admission remain; no new rule or admission.
- New modules compile below a second, standard axioms only. Full quiet ratchet GREEN:
  fragment 55, checker reach 60, 31 proved rules, 0 owed/exempt, 46 worked theorems,
  252 agree / 0 disagree.

## Clink 128 (2026-09-14) — retain main's world and compose full instance calls

- Split current-frame requirements from retained heap requirements. `Pos.mainWorld` is a
  positive request, seeded at ctx0 and retained by class/instance body contexts; `CtxEq`
  compares it. `StateOk.mainSite` carries main's heap readiness, shadowable-name guards,
  bare-name absence, builtin-only method_missing, and lexical/global constant agreement.
  A normalized frame is only a heap-view device, not an alternative executor.
- The same boot Bool proves the initial site. Allocation, field writes, name reservation,
  method publication, and fresh class creation preserve it. Fresh constants become visible
  consistently rather than preserving their old absence. These facts are not inferred from
  first-order value framing or from the callee's current receiver.
- A component countermodel installs builtin x: full Framed and MainReady survive, but bare
  absence fails and an actual call returns false. This does not claim an old full-StateOk
  counterexample. A positive real fresh-class entry retains the main site in full StateOk.
- `instance_pop_main_state` restores the entire caller state from the checked body's state,
  saved frame/fields, and retained site. `checked_instance_call_from_main` composes the
  installed-code lookup, annotated binding/body, and real frameK return into a full RunSpec;
  it no longer stops at the body boundary. Ordinary receiver payload remains an explicit
  constructor obligation. Non-main callers, class exit/publication, constructor integration,
  and class/body certificate rules remain. No new syntactic rule or admission.
- New modules compile below a second, standard axioms only. Full quiet ratchet GREEN:
  fragment 55, checker reach 60, 31 proved rules, 0 owed/exempt, 46 worked theorems,
  252 agree / 0 disagree.

## Clink 129 (2026-09-14) — execute class bodies and restore scope, not stale tables

- `returnScopeCtx` keeps the body's outgoing positive/negative tables and restores only
  caller scope. Generalize main restoration accordingly; ordinary instance calls retain
  their previous API as the unchanged-table specialization. Outgoing constant types and
  lexical/global compatibility remain explicit, not inferred from the caller's old table.
- `ClassReturnState` composes preallocation framing, uncaptured caller restoration, and
  full outgoing conformance through the actual frameK. `ClassRun` adds the real fresh-class
  entry step and applies a semantic body proof at full entry StateOk. No alternate executor,
  constructor assumption, or signature-only body admission is introduced.
- Controls consume a checker-produced literal-body certificate, retain installed-table/name
  reservations on scope exit, and execute a class definition + instance call while preserving
  a shadowed caller local. The latter is an execution control, not validator admission.
  Class publication, constructor integration, and annotated class/body rules remain gated.
- New proofs compile below a second, standard axioms only. Full quiet ratchet GREEN:
  fragment 55, checker reach 60, 31 proved rules, 0 owed/exempt, 46 worked theorems,
  252 agree / 0 disagree.

## Clink 130 (2026-09-14) — retain the root constructor dispatch

- Countermodel (§F35): retag Class#new to Object#nil?; the full old boot conjunction still
  passes, but actual fresh Point.new returns false. Instance-code conformance cannot supply
  constructor metadata. A global class-query row fails boot: Range/Struct legitimately
  define prelude constructors. Keep the requirement at Object's class-object dispatch site.
- `NewDispatch` states found-builtin/visibility/shadow and missing-method facts. Its finite
  Bool is added to bootOkB; `MainSite.newDispatch` retains the root fact under the existing
  mainWorld request and nameFreeN new guard. Context weakening, allocations, field writes,
  reserved method writes, and fresh classes all preserve it; no new Ctx field is needed.
- `ClassNewEntry` transfers that fact down the actual fresh eigenclass chain with a native
  new-shadow guard. A full-StateOk entry control consumes it; execution controls separate
  ordinary Point.new from the wrong tag and retain the legitimate prelude exceptions.
  Class publication, initialized allocation, and annotated body/certificate rules remain.
- New proofs build in about two seconds or less, standard axioms only. Full quiet ratchet
  GREEN: fragment 55, checker reach 60, 31 proved rules, 0 owed/exempt, 46 worked theorems,
  252 agree / 0 disagree.

## Clink 131 (2026-09-14) — bound global references before publishing fresh identities

- The full-old-boot countermodel (§F36) stores a dangling Future constant. Class allocation
  turns it into an alias of Point; a real new/is_a? call returns true outside the proposed
  ancestor-name list. Saturated ancestor walks and bounded dispatch edges do not bound data.
- Add `ConstRefsLive` to ClassReady, not a source annotation or a new type. Its finite boot
  check bounds only global constant references; ordinary aliases to live objects remain
  allowed. Ext, method writes, and ivar writes preserve the table and grow its bound. Fresh
  registration introduces one bounded reference and preserves the others, for any definee.
- `ClassIdentity.named_fresh_only` proves that allocation cannot create an unadvertised
  global class alias. The actual-entry control derives it alongside full StateOk; it is
  not a constructor or complete ancestry proof. Those publications and body rules remain.
- New proofs build below a second, standard axioms only. Full quiet ratchet GREEN:
  fragment 55, checker reach 60, 31 proved rules, 0 owed/exempt, 46 worked theorems,
  252 agree / 0 disagree.

## Clink 132 (2026-09-14) — distinguish Object's chain from main's dispatch chain

- Countermodel (§F37): existing receivers detour through Kernel with Object prepended;
  Object itself is isolated. All previous boot checks pass, but actual Point.new allocates
  an instance without BasicObject ancestry. MainReady's chain cannot supply the superclass
  fact used by fresh ordinary constructors.
- `ClassReady.objectChain` pins Object's own chain, checked at boot and preserved by Ext,
  definitions, field writes, and fresh registration. This is a heap prerequisite, not an
  annotation or an assertion about unexecuted class text.
- `ClassShape.ordinary` proves the fresh class's live id, non-Class/non-Module status,
  non-module payload, exact physical root chain, and both no-payload-core allocation tests.
  `class_entry_ordinary` composes it with actual entry and full StateOk. Constructor execution,
  ancestor-name correspondence, declaration publication, and body/certificate rules remain.
- New proofs build in about a second or less, standard axioms only. Full quiet ratchet
  GREEN: fragment 55, checker reach 60, 31 proved rules, 0 owed/exempt, 46 worked theorems,
  252 agree / 0 disagree.

## Clink 133 (2026-09-14) — constructor dispatch to annotated initializer entry

- `ConstructorEntry` proves real new interception, plain allocation, and required-parameter
  entry. NewDispatch excludes a user singleton override; OrdinaryClass supplies allocator
  shape. The separate non-Math-id premise is necessary because invoke special-cases that id.
- `ConstructorState` preserves full caller conformance across allocation and establishes
  InitState at the actual initializer frame, anchored before allocation. `initializerBodyCtx`
  requests closed empty fields; an ordinary instance annotation remains open. Parameter
  binding uses the annotated domain, not concrete-value body inference.
- `constructor_body_entry` consumes SemInitA at that state. The Point specialization uses
  the complete two-write body proof for arbitrary Integer arguments. Execution controls
  include new/getter, wrong arity/type, and a singleton new that bypasses initialization.
  The run theorem is body-local: newK/caller return, class publication, and initializer
  certificate/class rules are not admitted by these operational controls.
- New proofs build in about a second, standard axioms only. Full quiet ratchet GREEN:
  fragment 55, checker reach 60, 31 proved rules, 0 owed/exempt, 46 worked theorems,
  252 agree / 0 disagree.

## Clink 134 (2026-09-14) — return the initialized receiver to the typed caller

- `ConstructorReturn` separates frame isolation (measured at initializer entry) from heap
  preservation (anchored before allocation). It restores the actual caller frame/locals,
  publishes Framed, and reuses full main-world restoration. The result type combines the
  receiver's retained identity with its outgoing ivar spine, not initialize's return type.
- `InitRunSpec.bindRunSpec` composes the scoped initializer contract into an ordinary
  caller continuation. Method frame-return lemmas now accept a trailing continuation;
  existing callers specialize it to nil. `ConstructorRun` handles both frameK and newK,
  including escapes, and connects the result to actual new dispatch and annotated binding.
- The Point run theorem covers all Integer arguments and first-order caller locals.
  Controls distinguish new's receiver from initialize's Integer result, reject assigning
  that receiver Integer type, and execute a getter alongside a restored String caller local.
  No class/body certificate rule is admitted; positive class publication and annotation-body
  families remain the checker frontier.
- New proofs build below a second, standard axioms only. Full quiet ratchet GREEN:
  fragment 55, checker reach 60, 31 proved rules, 0 owed/exempt, 46 worked theorems,
  252 agree / 0 disagree.

## Clink 135 (2026-09-14) — connect the physical root chain to its names

- The full-old-boot countermodel (§F38) redirects Kernel to a new module included by each
  primitive base. Existing named-ancestor rows remain correct, but a fresh Point does not
  inherit that module. Object's physical chain and the global root bindings are separate facts.
- Add `RootNames` to CoreOk, alongside its canonical String/Regexp facts. The finite boot
  check pins the three root bindings and excludes unlisted global aliases of their ids;
  non-root aliases remain allowed. Allocation, method writes, ivar writes, and fresh class
  registration preserve it. Registration uses the actual missing-name premise, not arbitrary
  constant replacement; ClassReady's lower-level generic allocator contract is unchanged.
- `ClassRootNames.named_chain` composes those facts with fresh-name uniqueness and ordinary
  allocation shape, proving both directions of named ancestry. The actual-entry control
  carries full StateOk. No signature/body admission or constructor-readiness claim is added:
  publishing an empty class record would still require the separate inherited-initializer fact.
- New proofs build below a second, standard axioms only. Full quiet ratchet GREEN:
  fragment 55, checker reach 60, 31 proved rules, 0 owed/exempt, 46 worked theorems,
  252 agree / 0 disagree.

## Clink 136 (2026-09-14) — publish class headers without default constructors

- Remove the legacy `ctorGet? = none → userInit? = none` clause from DeclClassOk. No current
  judgment consumes it; ConstructorRun already requires positive lookup and an annotated
  initializer-body proof. An empty own table cannot describe inherited absence. A future
  default allocator must prove `userInit? = none` separately, not infer it from the header.
- `classHeaderCtx` publishes only the newly executed class header. `declared_header` composes
  physical shape, guarded constructor dispatch, and complete named ancestry; full StateOk
  publication reuses the pending lexical site. No new readiness flag or future-body scan.
- The table frame is semantic before it is executable: old negative-new and positive-ancestry
  claims must still be justified. Its finite guard compares ancestor results and checks
  missing-new implication; adding a formerly unknown superclass is rejected. This works over
  nonempty old tables, not only ctx0. Unqualified names cannot introduce nested-path claims.
- Actual entry controls cover ordinary boot and a conformant world with Object#initialize.
  The latter publishes a valid Point header but a zero-argument new raises ArgumentError;
  the identity initializer has an independent annotation-domain body proof. Neither headers
  nor code-table publication grant callable signatures. Class/body admission remains gated.
- New proofs build below a second, standard axioms only. Full quiet ratchet GREEN:
  fragment 55, checker reach 60, 31 proved rules, 0 owed/exempt, 46 worked theorems,
  252 agree / 0 disagree.

## Clink 137 (2026-09-14) — annotated instance-definition publication

- Share `DeclLookupFrame` between header and member updates. Ordinary instance writes preserve
  DeclClassOk; nested claims remain unchanged for unqualified owners. `new`, `method_missing`,
  and `method_added` require different contracts and are excluded by this installation route.
- `memberFreshB` uses complete named ancestry and class sites to prove different heap owners.
  Comparing names alone is insufficient; banning the name globally is unnecessary. Same-name
  methods at a provably different class remain legal, while duplicate writes at one owner
  fail. `StateOk_install_member` derives all outgoing state from these input guards, with no
  assumed post-installation constructor/nested facts.
- Semantic definition rules require formal/annotated parameter agreement, first-order
  parameter/return types, and the entire body proof. Ordinary methods use an open self shape;
  initialize uses SemInitA from empty fresh fields to its proved outgoing shape. The proof
  contexts contain the installed declaration; no concrete call argument types the body.
- Controls consume a checked inc artifact, reject nullable/wrong-return annotations before
  any call, and apply the full Point initializer definition contract at real fresh entry.
  Runtime controls execute class/new/member calls, including another owner's same-name method.
  These are semantic rules, not new DJudge/checker admissions. Constructor composition and
  initializer-body certificate integration remain; old body proofs will need context refresh.
- New proofs build below a second, standard axioms only. Full quiet ratchet GREEN:
  fragment 55, checker reach 60, 31 proved rules, 0 owed/exempt, 46 worked theorems,
  252 agree / 0 disagree.

## Clink 138 (2026-09-14) — execute the complete annotated Point class

- `class_header_runSpec` composes header publication, a context-changing body proof, and
  real class-frame exit. The caller keeps outgoing declarations, not its stale input table.
- Point's complete class statement now has an all-fuel RunSpec for arbitrary first-order
  caller locals. Initialize uses its Integer parameter annotations and void result; getX
  uses the initialized field shape and its Integer return annotation. The final table gets
  fresh body proofs, including rechecking initialize after getX rather than casting context.
- `declared_constructor_code` derives actual builtin-new dispatch and user-initializer
  lookup/code from StateOk and installed rows. `after_run` exposes these facts at the real
  returned caller state. Controls execute class/new/getter, wrong arity, class-result Symbol,
  and preserved String caller locals. The generated 061 class subtree matches this program.
- The complete 061 expression is not yet admitted. ConstructorRun still asks separately
  for physical allocation shape; the named-ancestry header does not store that premise.
  Getter call composition and initializer-body certificates also remain. No checker/rule
  count is advanced by these semantic class-statement proofs.
- New proofs build below a second, standard axioms only. Full quiet ratchet GREEN:
  fragment 55, checker reach 60, 31 proved rules, 0 owed/exempt, 46 worked theorems,
  252 agree / 0 disagree.

## Clink 139 (2026-09-14) — constructor allocation from published conformance

- `Pos.plainAlloc` names proved plain-object allocators, separately from class/method rows.
  `StateOk.allocators` carries their live class ids, module/special-id exclusions, rootedness,
  and absence of payload-core allocation. This does not assert every declared class is plain
  or that an initializer is absent/safe. Context equality compares the capability list.
- `PlainAllocator` replaces ConstructorRun's unnecessarily exact fresh-class ancestry premise;
  ordinary inheritance need not have that exact list. Fresh publication proves the capability;
  allocation, method installation, ivar writes, class creation, and frame entry/return preserve
  it. Caller restoration keeps outgoing capabilities, not the caller's stale list. Freshness
  excludes Math using the live Regexp id; the earlier Proc lower bound would be insufficient.
- `PointConstructor.constructor_run` now derives allocation and dispatched initializer code
  from StateOk, then applies the initializer proof at its Integer parameter/void annotations.
  `after_class_constructor` composes this after a real class answer for arbitrary Integers and
  caller locals, retaining framing from before class creation. Controls reject capability-only
  context changes and show that allocation capability grants no method/initializer declaration.
- Constructor/getter expression composition and initializer-body certificates remain. These
  proofs do not add a DJudge rule or raise checker reach. Targeted builds are axiom-clean.
- Full quiet ratchet GREEN: fragment 55, checker reach 60, 31 proved rules, 0 owed/exempt,
  46 worked theorems, 252 agree / 0 disagree. New constructor controls build below a second.

## Clink 140 (2026-09-14) — class-parameterized constructor expressions

- Generalize argument evaluation to the actual send site and a Framed-preserved predicate.
  The existing implicit-call API is its True specialization; bounded recursive calls keep
  their existing proof. `sendVia` preserves a first-order receiver through every argument,
  retains earlier argument types, and consumes final-context dispatch at the evaluated values.
  It grants no method signature or dispatch permission by itself.
- `constClass` obtains the published identity from ClassesOk and uses ConstScopeOk to prove
  the actual lexical read. `declared_constructor_run` derives allocation and code for arbitrary
  published classes; `construct` composes arbitrary receiver/argument expressions with it.
  Class, initializer, arity, parameter/return annotations, and output fields are parameters;
  no Point module is imported by these production lemmas. Point's wrappers only instantiate
  them. This route still requires plain allocation, required positional parameters, an
  annotation-domain SemInitA body, and the existing caller/scope guards.
- `RunSpec.thenSeq` shares real sequence-frame composition with the existing sequence rule.
  `class_new_run` proves the complete class statement followed by new, with initialized Point
  result and full caller conformance. Controls cover `new(a = 3, a)`, retained caller `a`, both
  initialized fields, and allocation in an argument while retaining the receiver's identity.
- Independent FlagBox control: full class/new proof with one Boolean parameter, a Boolean
  initializer return, and no fields, using the same production API. Its body is proved for
  every context, not the concrete call value; new still returns the instance. Production
  lemmas must stay parameterized, with concrete classes confined to worked instantiations.
- Getter dispatch/composition and initializer-body certificates remain. No class/constructor
  DJudge rule or new validator acceptance is inferred from these semantic proofs.
- New proofs are axiom-clean and build below a second. Full quiet ratchet GREEN:
  fragment 55, checker reach 60, 31 proved rules, 0 owed/exempt, 46 worked theorems,
  252 agree / 0 disagree.

## Clink 145 (2026-09-14) — generic class rules cross the registry

- DJudge gains seven constructor-mirroring rules: ivar/class reads, class/member/initializer
  definitions, construction and explicit instance calls. Every rule is class/body/annotation-
  parameterized and retains the full body premise; definitions cannot admit uncalled bad bodies.
- DFam carries both InitJudge families, including the anchored heap semantics, for 44 rules
  across eight families. InitBridge folds their six constructors through the registry before
  the ordinary bridge consumes initializer premises. No raw syntactic body bypasses closure.
  CheckedInitializer.sem now uses that same bridge rather than a separate semantic induction.
- Move the checked-body return specialization above Bridge, retaining generic frame return
  below it. This breaks the class-rule/registry import cycle without a new assumption.
- The whole 061 derivation independently exercises all thirteen new rules, checking the
  initializer and getter at definition and final call contexts, never at particular arguments.
  RuleAudit reads constructor applications, not the generic bridge (which would over-report
  its cases). Its syntax predictor now distinguishes class bodies and direct constructor
  receivers without fixed class names; exact per-proof comparison remains mandatory.
- This raises registered rules and worked proofs, not executable acceptance: class/body-cache
  integration remains. The 061 AST is cross-checked against the generated corpus; existing
  FlagBox and multiclass controls continue using the same generic semantic interfaces.
- New derivation/bridge proofs build around one second and use standard axioms only. Full
  quiet ratchet GREEN: fragment 55, checker reach 60, 44 proved rules, 0 owed/exempt,
  47 worked theorems, 252 agree / 0 disagree.

## Clink 146 (2026-09-14) — whole-class checking with annotation-preserving caches

- `BodyCache` separates top/member/initializer artifacts; every entry carries its body proof.
  Lookup checks owner, actual code membership and exact body context, not only a selector.
  `check` now consumes all seven class-related rules registered in 145. No emitter change.
- Initializers start from annotated parameters and fresh empty fields. Their checked output
  supplies member self fields; missing initializers supply only an open empty annotation,
  never a default constructor. Calls compare argument types and receiver fields with cached
  annotations. They do not re-infer bodies, specialize parameter types, or trust claimed fields.
- Every member update rechecks old initializers and members in the enlarged context, using
  stored signatures and replay hints. Initializers go first, then members oldest first.
  Top-level artifacts remain unavailable in the class world and are rechecked at class exit
  in the restored main scope, including uncalled ones. Branches require compatible signature
  caches as well as code contexts; equal code alone does not determine its annotations.
- Whole-program controls vary class names and Integer/Boolean/nullable/array annotations,
  include definition-plus-call positives, and reject dishonest returns, narrowed nullable
  bodies, unchecked initializer suffixes, wrong arguments/fields, stale hints and unsupported
  allocators. Two classes sharing initialize/get retain independent signatures. Installing +
  rejects invalidated uncalled member and top-level arithmetic bodies.
- Kernel-normalizing a whole checked class merely to extract a test artifact hit Lean's
  heartbeat limit. The controls instead inspect the Option result with #guard, while body
  proof construction and the generic soundness theorem remain kernel checked; no new axiom.
- Actual emitted certificates now accept 061–063, 068, 071 and 072: fragment 55→61 and checker
  reach 60→63. The next frontier, 064, needs an instance-caller return contract before method-
  to-method calls can join; main-only guards remain intact.
- Full quiet ratchet GREEN: 61 accepted, reach 63, 44 proved rules, 0 owed/exempt,
  47 worked theorems, 252 agree / 0 disagree. No semantic lemma or axiom was added.

## Clink 143 (2026-09-14) — annotation-checked initializer data certificates

- Ordinary CheckedBody requires an unchanged field shape; it cannot certify initialization.
  `InitJudge`/`InitJudgeSeq` instead mirror SemInitA's anchored contract: local reads, guarded
  field writes, complete sequences, and result erasure for void/untyped annotations. The
  first-order parameter/return and output-field requirements remain explicit. No class,
  parameter count/type, field name, or body is fixed in the production relation or proof.
- `checkInitializerBody` checks the full source body in the parameter annotation environment,
  checks formal names/order and return compatibility, and computes the output fields. It has
  no caller locals or values as inputs. `.any` erases only a successfully checked result;
  an unsupported/bad suffix still rejects. Source/hint disagreement and exhaustion decline.
- Refresh reconstructs annotations from the earlier checked artifact and rechecks in the
  new context; it cannot cast a stale proof or accept new annotations from a replay hint.
  Controls cover nullable-domain/wrong-return failures, alias-sensitive writes, renamed
  classes, repeated field writes, missing locals/suffixes, and tampered hints.
- Point's actual definition and complete class/new/getX proofs now use checked initializer
  data at definition and after getter installation. FlagBox independently uses the same
  checker and refresh with one Boolean parameter/return and no fields. The actual emitted
  061 initializer was decoded from its rung JSON and checked, inferring both Integer fields.
- This is a body-certificate prerequisite, not whole-program admission. Neither new family
  is a DJudge premise yet; both must enter DFam/the registry before class rules consume them.
  Getter/body-cache and class/constructor certificate integration remain next.
- Generic soundness builds in 0.5s; concrete certificate/composition proofs in 1.4s or less,
  standard axioms only. Full quiet ratchet GREEN: fragment 55, checker reach 60,
  31 proved rules, 0 owed/exempt, 46 worked theorems, 252 agree / 0 disagree.

## Clink 144 (2026-09-14) — pure class-rule guards and constructor-ready semantic forms

- Registration exposed remaining semantic-only premises: native shadowing, frame-type
  stability, constant-scope compatibility, and class-table framing. The checker cannot
  supply heap predicates or import Denote. `ClassRules` now packages these as pure checked
  guards, interpreted by generic proofs, while keeping annotated body premises explicit.
- Preserve Ratchet's isolation: `NativeGuards` copies the projection of CRuby metadata
  needed for seven queries and the singleton-send exclusion set. Kernel-reduced finite
  coverage proofs link it to the model's real tables. Unknown query names decline; a new
  native blocker fails the coverage proof. No interpreter imports or assumed table agreement.
  The actual invoke/send proofs still enforce payload, privacy, and native interception.
- `reframeTypesB` checks all value-sensitive frame types. `plainClassTablesB` supports any
  number of unqualified records (not just an empty table); those have no nested-name claims.
  Constant annotations still require the existing stronger scoped-owner framing route.
- Class, member, initializer, constructor and instance-call forms now expose only syntax/
  type guards and body contracts. Point's full program and independent Boolean FlagBox use
  them. A two-class sequential proof/run exercises retained old classes and outgoing names;
  controls compare copied/native guards and reject stale names, qualified tables and bad scopes.
- These interfaces prepare DJudge admission; they do not add a rule or bypass the registry.
  The next change must carry InitJudge/InitJudgeSeq through DFam and preserve annotation-based
  body caches across class/member updates and caller restoration.
- New proofs build below two seconds and use standard axioms only. Full quiet ratchet
  GREEN: fragment 55, checker reach 60, 31 proved rules, 0 owed/exempt,
  46 worked theorems, 252 agree / 0 disagree.

## Clink 141 (2026-09-14) — generic instance calls and the complete 061 semantic proof

- Do not infer empty payload from `.inst`: the retained Proc#call countermodel disproves it.
  `DirectSendName` is an alternative, excluding the interpreter's eleven payload-intercepted
  names and generated CRuby singleton names. Its finite Bool proves the semantic predicate;
  actual dispatch is proved for arbitrary heaps/classes. The ordinary-payload route remains
  available, including names that cannot use this conservative alternative. No new heap flag.
- `instance_method_run` takes class/method records, parameter/return annotations, receiver
  fields, and a full body proof. It recovers actual code from StateOk and composes entry/body/
  return. The older checked-body call API is now a specialization, not a duplicate proof.
  `instanceCall` uses generic receiver/argument evaluation and the final context. Privacy,
  required arity, lexical resolution, and first-in-MRO obligations remain intact.
- Point's worked `full_run` composes class definition, constructor, and getter at Integer
  for arbitrary Integer arguments and first-order caller locals. Both bodies are proved at
  their annotations, not at those call values. The actual generated 061 program was compared
  with `fullProgram 1 2` using the Lean Rung decoder and `exprEq`; they match. Runtime controls
  check the result and caller-local restoration. Record#answer also runs unchanged with a
  Proc payload while Record#call runs the closure instead; only the former passes the guard.
- This is still a semantic proof, not a new DJudge/checker admission. Class freshness remains
  an explicit class-entry premise; class/initializer certificate families and cache integration
  must discharge the remaining obligations before the validator may accept 061.
- New proofs use standard axioms only; dispatch builds in 1.1s and composition below a second.
  Full quiet ratchet GREEN: fragment 55, checker reach 60, 31 proved rules, 0 owed/exempt,
  46 worked theorems, 252 agree / 0 disagree.

## Clink 142 (2026-09-14) — context-justified freshness for arbitrary classes

- Countermodel before strengthening: add `Occupied = 1` to the boot heap. Every existing
  boot check passes, but `class Occupied` raises TypeError. Empty positive class/constant
  type tables are not absence; live-reference bounds do not constrain Integer bindings.
- `Pos.globalConsts` is an upper bound on global names possibly bound now, not their types.
  StateOk interprets it; a finite data seed is checked against the actual prelude by the same
  boot Bool. Extra listed names are conservative. No opaque boot computation enters the
  checker and no additional pilot-specific boot hypothesis is introduced.
- Fresh entry adds only its executed name. Method definitions, allocations, field writes,
  and frame changes preserve the bound; restoring a caller must retain the outgoing bound,
  not reset it to the caller's pre-class value. Context equality includes it. This is distinct
  from whole-program `Neg.boundConsts`, which cannot express pointwise runtime absence.
- `StateOk.freshClassName` and the class-header run lemma are name/class/body-generic.
  The latter now consumes a static guard. Point and FlagBox only instantiate it, removing
  their external heap-freshness hypotheses, including the complete Point/new/getX proof.
  Their method bodies still require full parameter/return-annotation proofs, even uncalled.
- Controls preserve the full-old-boot countermodel, reject missing seed names and occupied
  names, retain names after definition/return, and reject incompatible branch bounds.
  Class/initializer certificate admission remains gated; no new validator reach is claimed.
- New proofs are axiom-clean and build below a second. Full quiet ratchet GREEN:
  fragment 55, checker reach 60, 31 proved rules, 0 owed/exempt, 46 worked theorems,
  252 agree / 0 disagree.

## Clink 147 (2026-09-14) — restore generic instance callers, not only main

- 064 exposed the missing caller contract, not a need for Point-specific dispatch.
  `restore_instance_state` recovers the saved lexical owner and receiver independently;
  their class names may differ from each other and from the callee. Post-call class sites
  supply heap facts; the saved frame, first-order values and field preservation supply data.
- No new Ctx or Framed field: named class-object identity is already preserved by
  `Framed.firstOrder` at `.clsOf`. `Framed.classNamed` exposes that consequence. `CallWorld`
  and its pure Bool select ordinary main/instance callers from existing scope/self/table
  data, requiring retained sites for both the lexical owner and receiver name.
- Actual instance dispatch/run now quantifies over the send site; the main-only interfaces
  specialize the same proof. Receiver-bearing, implicit and bare-name expressions all consume
  the complete parameter/return-domain body proof. Implicit arguments retain the receiver's
  first-order type while threading outgoing context/locals/fields. No call-site inference.
- Controls use Alpha→Beta, Boolean callee fields/results versus Integer caller fields,
  a caller-field read after return, and bare/implicit/explicit self-calls. Entire getter
  bodies have semantic proofs; real definition/new/call runs check the corresponding paths.
  Missing lexical/receiver sites, class-object self and absent runtime worlds decline.
- This is the semantic prerequisite, not 064 admission. Registry and cache/checker integration
  remain; no rule, floor or accepted-program count changes in this chunk.
- New proofs build in about a second, standard axioms only. Full quiet ratchet GREEN:
  fragment 61, checker reach 63, 44 proved rules, 0 owed/exempt, 47 worked theorems,
  252 agree / 0 disagree.

## Clink 148 (2026-09-14) — annotation-checked method-to-method calls, 064 admitted

- `instanceCallB` packages the generic caller-world guard; a pure implication retains every
  former main-call case. The existing explicit method rule now uses it. Constructor calls
  still need the main-only rule; ordinary return framing does not justify initialization.
- `vcallMethodSig` carries the entire zero-parameter annotated body through DFam/Clink/Bridge.
  Ruby's bare `area` is its actual vcall site, not an implicit-send AST rewrite or a missing-
  name exemption. The checker requires empty certificate arguments, a zero-parameter cached
  signature, exact receiver fields/context, actual owner/code membership and checked return.
  No cache layout change or call-site body inference was needed.
- Definition-time refresh already supplies predecessor bodies under the enlarged table.
  This now admits nested members while continuing to reject invalidated uncalled bodies.
  Controls vary class names and Integer/Boolean/nullable/array annotations, reject wrong
  returns/arity/hints, retain two owners' independent signatures, and restore an Integer
  caller field after a different class's Boolean-returning call.
- The emitted 064 certificate validates at String. `RectDerivations` independently builds
  the whole class/new/describe derivation from registered constructors, checking area from
  its Integer fields and describe by consuming that full body proof. The proof-term audit
  sees the new rule in both definition and final call contexts; actual execution returns
  `"area=12"`. Rect is a worked instance, not a production-rule premise.
- Floors ascend: fragment 61→62, checker reach 63→64, rules 44→45, worked proofs 47→48.
  065 inheritance is next; the still-unregistered parenthesized implicit/self-read forms
  are not silently accepted by the broader runtime proof.
- Full quiet ratchet GREEN: all 45 rules exercised, 0 owed/exempt, 48 worked programs
  cross-checked, 252 agree / 0 disagree. New proofs use only standard axioms.

## Clink 149 (2026-09-14) — distinct receiver/owner calls and the inherited-lookup obstruction

- Inherited bodies need `self : inst receiver fields`, but method owner/cref belong to the
  defining class. `instance_enter_state_at` and real entry now take two sites and use the
  existing Frame's receiver/defining-class fields. The former same-class APIs specialize
  them; no new context flag or class-specific premise.
- `resolved_instance_run` consumes actual lookup/code, the native-shadow prefix check, and
  a full annotated body at that mixed context. It composes binding/body/caller restoration
  for arbitrary classes, bodies, annotations and call sites. Existing own-method calls use
  this proof, deriving their empty prefix from the own-first lookup. Neither an ancestor's
  signature nor its row alone supplies the inherited lookup premise.
- Controls apply a Boolean annotation-domain body at Satellite self / Depot scope for every
  Boolean argument, reject nullable/wrong returns, and execute real inherited initialization,
  lookup, entry and call. Exact Depot self typing is false at that Satellite activation.
- §F39 is proved, not merely suspected: `unrecorded_shadow_preserves_state` preserves full
  current StateOk while writing a globally reserved selector absent from its owner's rows.
  A boot-grounded instance retains Object#answer's Integer body and Child's empty declared
  table but dispatches Child#answer to false. A separate actual Parent/Child inheritance run
  retains the ancestor row/chain while the inserted child override makes `answer + 1` stuck.
  Present calls require an own positive row, so this is not an accepted unsafe program.
- Inheritance needs owner-specific absence/dispatch conformance plus explicit-superclass
  creation. No checker rule, floor or accepted-program count changes in this prerequisite.
- Generic resolved-call proof builds in 0.5s; controls in 1.1s, standard axioms only.
  Full quiet ratchet GREEN: fragment 62, checker reach 64, 45 proved rules, 0 owed/exempt,
  48 worked theorems, 252 agree / 0 disagree.

## Clink 150 (2026-09-14) — owner-local absence and generic inherited lookup

- `ownNames` unions selectors across all retained records of a class name. Using only the
  latest snapshot would lose declarations when a new record was based on an earlier header.
  `ClassOwnNames` bounds the actual own table, including builtin/prelude/undefined entries;
  it grants neither positive code nor a body proof. No extra Ctx flag is needed.
- Generic transports cover allocation, fresh-class/header publication, and method writes.
  Publication requires covering every name aliasing the written physical owner.
  `memberOwnersB_sound` derives a sufficient separation guard from declared ancestry in
  either direction; unequal strings alone do not justify independent bounds.
- `classesOk_methodOn_after_prefix` combines positive code with absence at every preceding
  physical owner. Actual chain order and native-prefix guards remain explicit. All names,
  tables, code and owners are parameters. The full annotation-domain call proof is unchanged.
- Shared method-write membership now also proves the existing `MethodsExact` transport.
  Controls cover history, inheritance, unrecorded overrides and aliased owners. F39's full-
  StateOk witness is retained and strengthened with rejection by the new owner-local bound.
- This chunk establishes the invariant and transports, not its integration into StateOk.
  F39 remains open until all state producers carry the bound; no inherited checker rule,
  acceptance or floor change. Fresh-superclass creation also remains ahead of 065.
- New proofs build in under a second each, standard axioms only. Full quiet ratchet GREEN:
  fragment 62, checker reach 64, 45 proved rules, 0 owed/exempt, 48 worked theorems,
  252 agree / 0 disagree.

## Clink 151 (2026-09-15) — owner bounds in full conformance, F39 closed

- StateOk now requires ClassOwnNames. Allocation, frame/field changes, fresh classes,
  header publication and method installation preserve it; boot needs no extra check because
  its declaration table is empty. No Ctx flag or annotation escape hatch.
- StateCore retains exactly the former fields, not a second admission route. Shared method-
  write proofs produce it; the full-state wrappers also require the owner bound. This keeps
  F39's entire old-contract witness proved, while `hidden_override_not_state` excludes it
  from current conformance. The typed semantic contracts still all require StateOk.
- The existing memberFreshB includes memberOwnersB. Its semantic proof derives the needed
  physical-alias separation; publication never infers it from different strings. Existing
  member/body rules keep their full annotation premises and consume the stronger guard.
- F40 identifies the next lookup fact: an unnamed included module preserves own bounds,
  classFrontB and every globally named ancestor-membership answer while intercepting an
  inherited call. The executable control probes those premises, not full StateOk. Physical-
  chain correspondence and explicit-superclass creation remain ahead of 065.
- All new lemmas are class/body/annotation-generic and axiom-clean. Full quiet ratchet GREEN:
  fragment 62, checker reach 64, 45 proved rules, 0 owed/exempt, 48 worked theorems,
  252 agree / 0 disagree. No new acceptance or moved floor in this prerequisite.

## Clink 152 (2026-09-15) — complete ordered ancestry, F40 closed

- NamedChain relates every declared name to its physical owner in order. StateOk.classChains
  requires it whenever the static ancestor walk resolves; an unknown walk grants no claim.
  This strengthens membership, not a no-mixin heuristic. No new Ctx flag or boot check: the
  initial class table is empty, and fresh creation proves the complete root chain.
- Allocation, frame/field changes and method writes preserve the correspondence. Header and
  member publication reuse DeclLookupFrame to prevent newly activated old claims. All class
  names/tables are parameters; no Point-specific physical ids are assumed.
- `declared_inherited_code` derives the actual lookup from static ancestry, positive code
  and owner-local absence. `declared_inherited_run` obtains both sites from conformance and
  consumes the full annotated body at receiver/lexical-owner context, with ordinary caller
  restoration. Native-prefix and payload guards remain explicit; signatures alone do nothing.
- F40's unnamed interceptor retains its prior weak premises but fails classChainsB. The
  generic `unnamed_ancestor_not_state` proves exclusion by full conformance. Fresh-class,
  inherited execution and annotation-negative controls remain in the gate.
- Explicit-superclass creation, inherited initializer binding/return and receiver-aware
  annotation-body caching remain ahead of 065. No checker rule or floor changes here.
- New core proofs build in under a second; standard axioms only. Full quiet ratchet GREEN:
  fragment 62, checker reach 64, 45 proved rules, 0 owed/exempt, 48 worked theorems,
  252 agree / 0 disagree.

## Clink 153 (2026-09-15) — generic cached-parent subclass entry and ancestry

- `Subclass.heap` factors actual alloc/register/alloc/attach for arbitrary lexical owner,
  name, superclass and superclass metaclass. The existing Object-based heap/machine is its
  exact specialization. `enter_fresh` proves model entry; `step_resolved` includes the real
  superclass continuation's non-module class check and retains its surrounding continuation.
- One `ancestors_new_head` lemma covers both fresh class and metaclass chains. Existing
  ancestry remains unchanged; new walks prefix the corresponding parent chain. No Point,
  fixed user-class id, method body or annotation appears as a production-proof assumption.
- Cached parent metaclass is an explicit readiness premise. Controls remove only the cache
  pointer while retaining instance-chain/own-table checks, then observe the actual extra
  allocation: +3 objects rather than +2. Both paths execute inherited `echo(Boolean)`; a
  module superclass is type-stuck. This probes those two invariants, not full StateOk.
- This is entry/heap groundwork, not body acceptance or complete subclass conformance.
  Parent-metaclass readiness, full state transport, inherited initialization and receiver-
  aware annotation-body caching remain ahead of 065. Existing definition/call rules still
  require full annotation-domain bodies, including uncalled methods. No floor changes.
- New entry/chain proofs and controls build, standard axioms only. Full quiet ratchet GREEN:
  fragment 62, checker reach 64, 45 proved rules, 0 owed/exempt, 48 worked theorems,
  252 agree / 0 disagree.

## Clink 154 (2026-09-15) — subclass readiness through shared growth contracts

- `ClassGrowth` transports old edges/walks once; the producer supplies fresh edge bounds
  and singleton module walks/class heads into old parents. Both walk fuels are covered.
  `SubclassReady` discharges these for arbitrary class/metaclass parents, preserving
  ChainsIn, Saturated, ConstRefsLive and ClassReady. The +2 heap-size bound supplies slack
  for the new head; no acyclicity is inferred just from bounded edges.
- Default-superclass field/liveness/readiness lemmas now specialize these proofs, replacing
  duplicated arguments. `enter_fresh_ready` composes them with the actual entry equation.
  Cache readiness remains explicit; class/body/annotation assumptions are not specialized.
- Controls check readiness/saturation and inherited calls on cached and uncached paths.
  A synthetic in-bounds self-cycle fails saturation. F41's actual entry from a modified heap
  retains ClassReady/Saturated while a parent metaclass aliased to Float introduces a proper
  Float subclass and breaks BaseChainsOk. This probes those premises, not full StateOk.
- Full conformance must discharge parent-metaclass separation (derive it from existing
  stronger facts or retain an appropriate invariant), rather than reusing Object-only
  separation. Full subclass state transport and inherited body/initializer checking remain
  ahead of 065; no rule, body-admission requirement or floor changes here.
- New proofs and controls build in seconds, standard axioms only. Full quiet ratchet GREEN:
  fragment 62, checker reach 64, 45 proved rules, 0 owed/exempt, 48 worked theorems,
  252 agree / 0 disagree.

## Clink 155 (2026-09-15) — metaclass readiness retained in class sites, F41 closed

- InstanceSiteAt now includes MetaReady: a cached eigen pointer, its BasicObject ancestry,
  and separation from builtin value bases. The ancestry is needed to preserve old nominal
  types when allocation makes formerly dangling references live; separation addresses F41.
  Pointer bounds already follow from ChainsIn and are not duplicated in the new predicate.
- StateOk's existing classSites field retains these facts for declared classes and pending
  class scopes. Boot's site table is empty, so no extra boot check or Ctx flag. Fresh default
  class entry proves the facts from actual contents. Allocation, method/field writes, frame
  switches and unrelated class creation preserve them; old F39 witnesses still build.
- `MetaReady.subclass_old` and `Subclass.meta_fresh` are class/name/parent-generic. The
  actual `enter_declared_fresh` now derives its cached-parent premise from conformance,
  preserves readiness/saturation and publishes the fresh metaclass's readiness. Full
  StateOk transport, not a new annotation claim, remains the next obligation.
- F41's modified heap retains all its earlier weak premises but fails metaReadyB. Generic
  `aliased_meta_not_state` excludes it for any declared class/base; `uncached_parent_not_state`
  similarly excludes missing-cache inputs from current conformance. The model's uncached
  path still executes and restores ready parent/child metaclasses in the positive control.
- Every method definition/call still requires the complete annotation-domain body proof.
  No checker rule, acceptance or floor changes; inherited initializer/body caching remains.
- Entry and exclusion proofs build in seconds, standard axioms only. Full quiet ratchet
  GREEN: fragment 62, checker reach 64, 45 proved rules, 0 owed/exempt, 48 worked theorems,
  252 agree / 0 disagree.

## Clink 156 (2026-09-15) — shared first-order preservation through subclass entry

- `dataPres_of_class_growth` factors old reads, bounded ancestry, fresh BasicObject
  membership and name preservation into DataPres. Its existing type/spine induction covers
  all first-order types, including nested collections and instance fields. SubclassData
  proves these observations for arbitrary parents; default-superclass DataPres now uses it.
- `enter_declared_data` derives the parent's metaclass ancestry from full conformance and
  proves actual entry preserves old data. `Subclass.framed` restores the heap/field half
  of caller framing once the stack and inactive-frame obligations are supplied. Neither
  theorem substitutes a signature for a checked body or claims full outgoing StateOk.
- Controls retain a hash of arrays of Boolean-field instances and execute inherited
  initialize/getter calls. Both allocated ids and the still-dangling next id retain their
  BasicObject type. Synthetic stale-name registration loses the old exact-instance type.
  Removing only a parent metaclass's superclass retains ClassReady/Saturated but loses a
  dangling reference's BasicObject type after actual entry; the already-retained MetaReady
  rejects it, and `unrooted_parent_not_state` proves generic full-state exclusion.
- Full subclass state transport and inherited constructor/body-cache checking remain ahead
  of 065. No checker rule, annotation requirement, acceptance or floor changes.
- New proofs and controls build in seconds, standard axioms only. Full quiet ratchet GREEN:
  fragment 62, checker reach 64, 45 proved rules, 0 owed/exempt, 48 worked theorems,
  252 agree / 0 disagree.

## Clink 157 (2026-09-15) — shared superclass/metaclass dispatch and query transport

- SubclassDispatch's source map sends the fresh class to its superclass, the fresh
  metaclass to the parent's metaclass, and other ids to themselves. Old reads, whole
  lookup and native-prefix preservation cover arbitrary parents, lexical owners and runtime
  class names. Default-superclass dispatch is now a specialization, not a second proof.
- SubclassQueries transports primitive dispatch/errors, QueryOk, ClsQueryOk and NilQueryOk.
  The fresh class receiver maps to the actual parent class receiver; a fresh metaclass
  still requires the pre-existing direct-Class query site. Default-superclass query/core
  lemmas delegate to these generic proofs. Native guards remain mandatory.
- `enter_declared_queries` composes actual entry with these conformance components, deriving
  parent/metaclass facts from StateOk and consuming the existing NativeFrame guard. It does
  not claim full outgoing StateOk or execute/accept the class body.
- Controls execute Beacon/Flare inherited instance and singleton calls. A synthetic heap
  registers Facade but stores runtime name String: pure inherited lookup agrees while
  to_s gains a native interceptor. Thus the generic guard uses runtime name q, not the
  registration key. Singleton definitions remain model controls, not checker admission.
- Builtin-base, payload, declaration and scope transports still precede full subclass
  conformance; inherited initializer/body caching remains. No rule, annotation requirement,
  acceptance or floor changes.
- New proofs and controls build in seconds, standard axioms only. Full quiet ratchet GREEN:
  fragment 62, checker reach 64, 45 proved rules, 0 owed/exempt, 48 worked theorems,
  252 agree / 0 disagree.

## Clink 158 (2026-09-15) — shared subclass identity, core and installed-code preservation

- SubclassNames preserves old names/root bindings and proves the freshly registered
  identity. Reverse old-name transport requires an old id; fresh-name uniqueness consumes
  ConstRefsLive. Runtime display name remains independent of the global registration key.
- SubclassCore preserves CoreOk and String/Array/Hash payload contracts. SubclassMethods
  preserves exact own method lists/code, ClassesOk, DefsOk and MethodsExact; fresh empty
  tables agree with the formerly out-of-bounds lists. This publishes no future body and
  does not imply absence of inherited initialize. Default-superclass lemmas delegate to
  these generic proofs, including non-class reads and name identity.
- `enter_declared_core` derives parent/metaclass liveness from incoming StateOk and
  composes actual entry with these components and unique fresh identity. All production
  statements quantify over classes/parents/bodies; no Point-specific proof is introduced.
- Controls retain Relay's alias, ordinary method metadata and heap payloads, then execute
  inherited initialization/getter calls for two fresh class names. Zero-argument new still
  raises ArgumentError despite the child's empty own table. A synthetic dangling alias
  becomes live at actual subclass entry, retaining the need for ConstRefsLive.
- Full builtin-base/declaration/scope transport and inherited initializer/body-cache
  checking remain ahead of 065. Complete annotation-domain body proofs, including uncalled
  methods, remain mandatory; no checker acceptance, rule or floor changes.
- New proofs and controls build in seconds, standard axioms only. Full quiet ratchet GREEN:
  fragment 62, checker reach 64, 45 proved rules, 0 owed/exempt, 48 worked theorems,
  252 agree / 0 disagree.

## Clink 159 (2026-09-15) — guarded builtin ancestry and existing subclass-table transport

- SubclassBases preserves BaseChainsOk through both fresh heads. Parent separation is
  required only for active negative-answer guards; metaclass separation comes from
  existing MetaReady. The pure subclassBaseFrameB checks those active rows against the
  resolved parent chain, canonical core bindings and root mixin guard. Its soundness uses
  existing StateOk declaration/site/base facts; no new state field or boot check.
- This is a sufficient frame, not a builtin-parent blacklist: a whole-program String
  subclass disables that row's negative answer, and the guard can still pass. The generic
  transport accepts any proof of the physical separation condition, not only this Bool.
  An actual Float-parent entry with a ready metaclass invalidates the unguarded boot
  exclusion; aliased_parent_not_state rules out hidden active-base aliases generically.
- SubclassDeclared preserves existing DeclClassOk (including constructor lookup and both
  named-ancestry directions), ClassOwnNames and ClassChains. Default-superclass proofs
  specialize these transports; names, superclass/metaclass, code and contexts are arbitrary.
- `enter_declared_tables` composes actual entry with these four components and derives the
  physical parent/metaclass obligations from conformance plus the static guard. Controls
  retain old rows, execute three-level inheritance plus an unrelated same-selector class,
  and decline unknown/stale parent facts or unavailable canonical core bindings.
- Full scope/site/allocator transport and new subclass publication still precede 065;
  inherited initializer and receiver-aware body caching remain. No checker rule, body
  annotation requirement, acceptance or floor changes.
- New proofs and controls build in seconds, standard axioms only. Full quiet ratchet GREEN:
  fragment 62, checker reach 64, 45 proved rules, 0 owed/exempt, 48 worked theorems,
  252 agree / 0 disagree.

## Clink 160 (2026-09-15) — retained class-object name facts and generic subclass frames

- InstanceSiteAt gains classNames, using NamesAt at the class object's dispatch id;
  instance names remain a separate site. Both use existing nameFreeN, so reserving a name
  weakens the obligation without publishing code or certifying a body. Fresh default-class
  publication, allocation/frame changes, reserved method writes, ivar writes and unrelated
  class creation preserve it. Boot's empty class-site table needs no extra check or Ctx flag.
- F42's injected prelude-marked lambda leaves selected old instance/top-level contracts
  intact but intercepts subclass-body self and raises ArgumentError. The new classNames
  check rejects it; a generic theorem excludes full StateOk. An ordinary parent still
  returns Proc, and the unrelated shim T.proc confirms this is not a heap-global restriction.
- SubclassFrame proves uncaptured, empty local/ivar/block and saved-frame facts for any
  parent, namespace and cref. Global class-object self typing uses Object registration.
  SubclassNameEntry transports NameFreeOk from the parent metaclass's retained names;
  default-superclass frame/name proofs delegate to these generic results.
- `enter_declared_frame` composes actual entry with the frame/name components, deriving
  its parent-site and metaclass evidence from StateOk. No new body's annotations are
  assumed or checked by this theorem. Constants, complete sites, allocator/publication and
  inherited initializer/body-cache integration still precede 065; no acceptance/rule/floor
  changes, and every method body still requires its full annotation-domain proof.
- New proofs and controls build in seconds, standard axioms only. Full quiet ratchet GREEN:
  fragment 62, checker reach 64, 45 proved rules, 0 owed/exempt, 48 worked theorems,
  252 agree / 0 disagree.

## Clink 161 (2026-09-15) — generic constant scope and class-site publication at entry

- SubclassConstants preserves old constant reads away from the registered key and maps
  the fresh class's inherited lookup to its actual parent. Parent instance/global scope
  agreement implies that inherited fallback cannot reveal a globally absent constant.
  Fresh lexical resolution checks Object before that fallback. This consumes existing
  site facts, not a new invariant or a claim that superclass tables are empty.
- SubclassSites preserves every old site, including both instance/class name exclusions,
  and publishes the fresh site's empty front, names, constants, hook and MetaReady. Its
  parent capabilities do not require an ordinary-parent front or a declared Object row,
  so default-superclass creation uses the same proofs. ClassScopeReady is generic too.
- `enter_declared_sites` derives parent capabilities from StateOk and composes actual
  entry with ConstScopeOk, ClassScopeReady and ClassSitesOk at the new class-body context.
  Existing default-superclass constant/site/scope lemmas now delegate to these transports.
- Controls retain old sites, expose the executed new binding consistently, and return a
  global Integer through both the class body and an inherited method. A parent-only SECRET
  is inherited operationally but contradicts the existing site scope; a generic theorem
  excludes that shape from StateOk. These model inputs do not admit casgn or certify bodies.
- Main-site/constant-table/allocator transport remains before full entry assembly, then
  new-header publication and inherited initializer/body-cache integration for 065. No rule,
  acceptance, floor or full annotation-domain body requirement changes.
- New proofs and controls build in seconds, standard axioms only. Full quiet ratchet GREEN:
  fragment 62, checker reach 64, 45 proved rules, 0 owed/exempt, 48 worked theorems,
  252 agree / 0 disagree.

## Clink 162 (2026-09-15) — full class-generic subclass entry conformance

- SubclassMain/Tables/Globals preserve retained main dispatch, first-order constant/path
  claims, old allocator capabilities and the executed global-name bound. ClassTablesFrame
  moved unchanged to its own file to avoid a dependency cycle; old public wrappers remain.
- SubclassState assembles every StateOk field at entry. ParentCaps bundles existing input
  facts, derived either from main/Object or a declared parent's site and static base guard.
  It is not a new state invariant, Ctx field, or checker admission route. The default-parent
  StateOk and transport lemmas delegate to these same class/body-generic proofs.
- SubclassStateEntry connects full conformance to actual enterClassBody and the resolved
  superclass continuation. DeclClassOk supplies its non-module check; cached eigenclass,
  parent bounds, dispatch names, constants and builtin separation come from incoming state.
- Full-state Carrier→Relay controls start with a checked literal parent body, prove its
  actual three-step run, restore main, then enter the child directly and via classDefK.
  The parent allocator and declaration table are nonempty. Boot execution is not assumed:
  the entry lemma plus kernel reduction proves the run under the existing bootOkB premise.
- No rule/acceptance/floor changes. New subclass-header publication, class-run composition
  and receiver-aware inherited initializer/body-cache checking remain before 065. Every
  method still requires a full annotation-domain body proof, including uncalled methods.
- New proofs and controls build in seconds, standard axioms only. Full quiet ratchet GREEN:
  fragment 62, checker reach 64, 45 proved rules, 0 owed/exempt, 48 worked theorems,
  252 agree / 0 disagree.

## Clink 163 (2026-09-15) — publish an executed subclass header from its actual parent

- SubclassAllocator derives plain allocation from the parent's capability; it does not
  reuse Object's exact root chain. SubclassNewEntry follows the parent's metaclass for
  Class#new dispatch, retaining native-shadow checks. SubclassNamedChain prepends the fresh
  class to the parent's complete ordered and bidirectional name/id ancestry, including the
  reverse-name obligations that rule out aliases omitted by a declaration.
- SubclassHeaderFrame checks the known parent/new child chains and frames old table claims
  using finite comparisons. Unknown parents, self-cycles and newly activated old chains
  decline; no assumption about fuel-insensitive static walks is needed. The guard mentions
  neither heap ids nor semantic judgments and introduces no body-acceptance route.
- SubclassHeader publishes every StateOk field at the existing fresh lexical site, deriving
  declared ancestry, empty own-name bounds and plain allocation. ClassPublish factors the
  common empty-record publication, requiring both instance and singleton declaration lists
  empty; default headers and constructor dispatch reuse it and the generic parent proof.
  SubclassHeaderEntry composes actual entry with full publication.
- Real-boot Carrier→Relay header control consumes the proved parent run. A second control
  consumes FlagBox's checked Boolean initializer/class-run proof, then publishes FlagChild
  from any resulting full state. Executable controls check inherited one-argument arity,
  zero-argument ArgumentError, the instance result despite a Boolean initializer result,
  and exact chains/own-name bounds through FlagLeaf. These calls are model probes, not a
  claim that the checker now admits subclass bodies.
- No rule/acceptance/floor changes. Full subclass-run composition and receiver-aware
  inherited initializer/body-cache checking still precede 065. All method bodies remain
  checked across their entire annotation domains, including uncalled methods.
- New proofs and controls build in seconds, standard axioms only. Full quiet ratchet GREEN:
  fragment 62, checker reach 64, 45 proved rules, 0 owed/exempt, 48 worked theorems,
  252 agree / 0 disagree.

## Clink 164 (2026-09-15) — checked subclass execution and superclass context threading

- ClassActivation factors class-frame restoration independently of the heap producer or
  superclass: publication supplies the initial Framed proof, the checked body supplies the
  next, and caller restoration retains the body's outgoing declarations. Default class
  return/run proofs now delegate to it; SubclassBodyRun uses the generic subclass heap anchor.
- SubclassRun composes non-module validation, actual entry, full header publication and
  the checked body through classDefK/frameK. SubclassExpr then evaluates any typed superclass
  expression, preserving its outgoing Ctx/Env/ivar indices, and propagates escapes normally.
  In particular, the class result restores the superclass expression's updated caller,
  not the stale incoming one. SubclassRule packages only static guards plus semantic body
  premises; no DJudge constructor or unchecked annotation-cache route is added.
- Checked controls run FlagBox→FlagChild→FlagLeaf, with an annotation-checked Boolean
  initializer and child method. Superclass evaluation itself creates Sibling and a String
  caller local; the child installs its method and shadows that local with an Integer. Full
  outgoing state/result proofs retain Sibling, the new method and the caller String across
  both subclasses. Wrong/nilable return-domain annotations are rejected before calls;
  executable inherited-new/call and wrong-arity controls remain separate from admission.
- Diagnostic: an attempted context-changing control used a top-level def after a class,
  which the existing empty-class-table guard rejects. Its failed Option.get certificate
  caused a downstream Lean crash; isolating that prefix exposed the rejection. The control
  now uses supported sibling-class publication; no top-def guard was weakened.
- No rule/acceptance/floor changes. Receiver-aware inherited initializer binding, return
  and annotation-body cache checking remain before 065. Every body still needs its full
  annotation-domain proof, including uncalled methods.
- New proofs and controls build in seconds, standard axioms only. Full quiet ratchet GREEN:
  fragment 62, checker reach 64, 45 proved rules, 0 owed/exempt, 48 worked theorems,
  252 agree / 0 disagree.

## Clink 165 (2026-09-15) — receiver/owner-generic inherited initialization

- initializerBodyCtxAt uses the existing receiver/defining-class Frame split; allocation
  establishes the child's exact self type and closed empty fields, while the actual method
  owner establishes lexical scope. Constructor entry extends both sites through allocation.
  The frame/new return proof separates those names too: lexical scope restores the caller,
  and initialized self determines the result. Own constructors delegate to the split proof.
- InheritedConstructor uses the ordered declaration/physical-chain correspondence and
  owner-local absence to derive actual initialize lookup. Allocation and new dispatch come
  from the receiver's retained capabilities. InheritedConstructorExpr evaluates receiver
  and arguments first and uses their final Ctx/Env/spine for lookup and the full body proof.
  No production lemma fixes a class name, owner, parameter domain, return or field shape.
- The FlagBox→FlagChild control replays the existing initializer certificate at its original
  Boolean parameter/return annotations in the child-receiver/parent-owner context. The
  complete checked class/new runs prove an instance result for both Boolean values; the
  initializer's Boolean result is not mistaken for new's result. Wrong return annotations
  and nullable-to-Boolean domains reject before calls; actual inherited zero-argument new
  raises ArgumentError. The semantic call lemma accepts any plain Boolean-typed argument
  expression, not just those two values.
- No rule/acceptance/floor changes. Receiver-aware full-domain body-cache replay and
  subclass judgment/bridge/checker integration remain before 065. No signature-as-proof,
  call-site specialization, new invariant field or admission shortcut is introduced.
- New proofs and controls build in seconds, standard axioms only. Full quiet ratchet GREEN:
  fragment 62, checker reach 64, 45 proved rules, 0 owed/exempt, 48 worked theorems,
  252 agree / 0 disagree.

## Clink 166 (2026-09-15) — complete receiver-aware annotation-body caches

- MemberRoute checks the declared ancestor split, owner/code membership and every earlier
  owner-local absence. The union over retained records prevents a stale newest record from
  hiding an earlier override. Callable artifacts pair that route with an exact-context body
  proof; receiver/owner keys also participate in branch-signature agreement.
- Refresh rebuilds effective receiver variants from own-definition sources, preserving
  their original parameter/return annotations. All initializers precede member replay;
  members use each receiver's proved initialized fields and earlier checked dependencies.
  A new definition is added before the completeness gate. That gate enumerates declared
  selectors, not existing cache entries; generic lemmas recover full callable artifacts
  from success. Missing variants and applicable replay failures cannot be silently skipped.
- Controls replay LabelBox→LabelChild→LabelLeaf with String fields. A child initializer
  assigning String passes; Integer or nilable-String invalidates the inherited String getter
  and rejects without a call. Dropped variants, retagged parent proofs, wrong owners,
  shadowed lookup and changed receiver branch keys fail. Semantic consumers pass the cached
  full-domain proofs through real inherited initializer/member dispatch, retaining the
  explicit native-prefix obligation. The class/new pilot publishes the child's String
  field, and the model's inherited getter returns that String.
- Kernel replay of the expanded cache exceeded the default elaborator heartbeat budget
  with rfl/decide. Switching those certificate witnesses to decide +kernel reduces the
  complete cache-control build to about a second, without raising limits or native_decide.
  New-member replay expands only that member after earlier bodies were already refreshed
  in the new context; it does not repeat their identical checks.
- The full gate exposed an older subclass control carrying the parent's declaration table
  but no body cache; its now-failing Option.get triggered Lean's known elaboration crash.
  The control now threads the parent's existing checked initializer through superclass and
  child checks, and explicitly tests empty-cache rejection. Kernel-checked projection
  equalities keep semantic composition from repeatedly normalizing the whole checker run.
- No rule/acceptance/floor changes. Subclass and inherited-call judgment/bridge/emitter
  integration, including a proved native-prefix guard, remains before 065. No signature
  stands in for its body and no concrete call argument specializes an annotation.
- Full quiet ratchet GREEN: fragment 62, checker reach 64, 45 proved rules, 0 owed/exempt,
  48 worked theorems, 252 agree / 0 disagree. New controls/proofs take seconds and use only
  standard axioms.

## Clink 167 (2026-09-15) — whole-program inherited fields, 065 admitted

- Register subclassDecl, newInherited and callInherited against their generic semantic
  forms. Receiver/argument/superclass evaluation threads Ctx, locals and fields; lookup
  consumes first-owner route evidence and full receiver/owner-indexed annotation proofs.
  InitJudge still crosses DFam through its registry bridge. No production premise fixes
  Point, Animal, Dog, a field shape or an annotation domain.
- The native-prefix obligation cannot assume runtime heap labels match declared names.
  A pure selector set conservatively covers all 561 instance names in the model's 32 rows;
  NativePrefix kernel-checks that coverage and proves absence on every heap/prefix. Inherited
  native selector names decline for now. Own calls keep their existing empty-prefix route,
  with a generic dependent-record equality lemma recovering the original own body indices.
- The checker uses the receiver cache for new/explicit calls and replays all effective
  inherited bodies at class exit. The existing emitter/schema already supplies superclass
  names and inherited signatures, so no emitter change or annotation reinference is needed.
  Controls accept String/Integer/Boolean and multilevel calls; reject uncalled incompatible
  or nullable fields/domains, wrong arguments/arity/result claims, hidden parent lookup after
  an override, unknown/cyclic parents and unsupported default allocation. Own overrides and
  own native names retain positive controls. A valid-looking call cannot rescue a bad body.
- Whole 065 has an independent Church derivation for every String input, exercising the
  three new clinks and evaluating the actual corpus instance to "Rex". Rule prediction now
  extracts class declarations and selects own/inherited lookup without hardcoded class
  names; the proof-term audit cross-checks it per rung. Default root classes use the static
  table's implicit-root convention, not a fabricated Object record. No exemptions.
- Measured fragment 63, checker reach 65, 48 proved rules and 49 worked theorems; floors
  raised accordingly. 066 remains gated on default allocation; inherited bare/implicit calls
  remain separate integration work. New proof/control builds take seconds, standard axioms
  only; decide +kernel avoids elaborator recursion limits on the large native-name set.
- Full quiet ratchet GREEN: fragment 63, checker reach 65, 48 proved rules, 0 owed/exempt,
  49 worked theorems, 252 agree / 0 disagree.
