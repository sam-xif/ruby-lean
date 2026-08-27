# `Judgment/` — implementation notes (J-numbers)

Decision record for the declarative judgment layer (`judgment-layer.md` J0), per the
§7 working norms. Format follows `Cert/implementation-notes.md` (V-numbers).

## J1 — a `Prop` needs no fuel and no kernel reduction

`Judge` is an inductive relation, so none of `chk`'s load-bearing constraints apply:
no fuel, no L73 reducibility discipline on this path, no `.induct` derivability
concerns (inversion is `cases`). The library is off the default build target for
Metatheory's reason (`lake build Judgment`).

## J2 — `JCtx extends FrameCtx`, adding the two channels `chk` lacked

`FrameCtx`'s six channels are reused by structure extension (no copy; their
docstrings stay the reference). Two new channels, each converting a claim-gated `chk`
arm into a **sound rule**:

* `blk : Option BlockSig` — the enclosing method's declared block signature, set by
  `defDecl`/`defs` from the chosen declaration, read only by `yield'`, cleared by
  `jBlockCtx` (a `yield` in a block targets the *home* method's block — a pairing
  this context cannot see).
* `inRescue : Bool` — set by `JudgeRescues` on handler bodies, read only by
  `retry'`, cleared on entering method/block/class bodies.

Two arms remain **assumption rules**, marked `[ASSM]` in the file: `var .cvar` /
`vasgn .cvar` — class variables are the one namespace `Decls` has no channel for.
The chosen type is discharged by nothing here; the future fix is a `cvars` field on
`Decls` (a `Types/` change with its own L-number), after which these become
declared rules like ivars.

## J3 — claims become derivation choices; assumed rows live in `D`

Everywhere `chk` consults the certificate, `Judge` quantifies over the choice and the
derivation records it (D1's stackmaps as proof-theory). Consequences:

* `joinTy` disappears from the rules: the `if`/`begin` joins are one rule each with
  a chosen upper bound (`joinTy`'s answer is an instance, by `joinTy_sub`).
* The chosen continuation environment is **checked** (`SubEnv Γc` into each branch
  exit) where `chk`'s `claimEnv` was unchecked — the sound form of the same arm.
* There are **no claim-fallback rules** on `send`/`vcall`/`const`/`yield`: an
  asserted signature or constant is a row in the certificate's table `D`
  (deltaRows → residue), consumed by the ordinary rule. This is §9.1's "a
  certificate names the declaration table" carried to its conclusion.

## J4 — subsumption

One non-syntax-directed rule: weaken the type up (`subTy`), weaken the exit
environment by **dropping bindings** (`SubEnv`). See J13 for what "dropping, not
coarsening" costs.

## J5 — narrowing, first rung

`ifNarrowElse`/`ifNarrowNone`: a condition that is a bare local read of a
`.nilable σ` narrows the local to `σ` in the then-branch (truthy ⇒ not nil ⇒ a σ).
Sound for every σ including `.bool`. The **else**-branch is *not* narrowed to
`.nilT`: when `σ = .bool` the falsy value may be `false : bool`, so else-narrowing
needs a `σ ≠ .bool` side condition — deferred. The `x.nil?`-condition family (the
`&.` desugar shape) is the next rung.

## J6 — loop rules deviate from `chk`, in the sound direction

* Stability is **containment** (`SubEnv Γl ·` at each subcomputation exit), not
  `chk`'s environment equality — the back edge re-enters at `Γl`, which is all it
  needs.
* The loop's exit environment is **`Γl`** (the stackmap), not the entry `Γ`. `chk`
  answers the entry environment, which is unsound when a claimed `Γl` widens a
  binding the body then retypes — coverage-tier only there (`claimFree` excludes
  it from the sound tier), but the spec states the right thing.
* `brk (some e')` requires the value below the loop's type, which is `.nilT` for
  every loop this judgment types (a valued `break` makes the loop evaluate to the
  value; `while` is typed `nil`). `chk` claim-gates this; the spec restricts it.

## J7 — `redo'` carries the premise `chk`'s arm lacks

`redo` re-enters the loop **body** (typed at `Γl`) from the current environment, so
it owes `SubEnv Γl Γ` exactly as `nxt` does. `chk`'s `redo'` arm checks only
`ctx.inLoop.isSome` — flagged as a possible gap in `chk`'s coverage tier (mid-body
*retyping* of a local, then `redo`, re-enters the body with a wrong assumption).
`redo` is not in `inferFrag`, so no sound-tier claim is affected; verify before
filing against `chk`.

## J8 — [SOUNDNESS-OPEN] `begin'` handlers at the entry environment

Transcribed from `chk`: handlers judged at the region's entry `Γ`. Counterexample
shape: the body retypes a local (`x = "s"` after `x : Int` at entry), then raises —
the handler runs at the mid-body environment, where the entry-env assumption about
`x` is false. Neither `chk` nor `Judge` is in the sound fragment here, so nothing
proved is wrong; the question must be **resolved at J1 preservation**, not patched
silently. Candidate fixes: (a) judge handlers at `Γ` masked of every local the body
assigns (needs an assigned-names predicate), (b) per-raise-point environments
(heavier). Decided to transcribe-and-flag rather than guess.

## J9 — the `def` rules

* `defDecl` generalizes `chk`'s claimed arm to a full chosen `MethodDecl`
  (params, return, **block signature**) — the block signature is what opens the
  `blk` channel for `yield` (J2). It adds `declaresName D name = false`, which
  `chk`'s claimed arm lacks: redefining a name whose row is in force silently
  retargets the row at the new body. (For `chk` this is coverage-tier; noted.)
* `defPromote` is `chk`'s deterministic nullary arm guard-for-guard, including
  `ret := none` on the body (a `return` inside a promoted body refuses) and the
  eight-clause promotion guard, threading `addRow`.
* `defs` chooses a declaration, judges the body at `selfCls := none`, threads no
  row. No `singleton_method_added` guard (`chk` has none either) — noted as an open
  question for the oracle.

## J10 — private binding helpers, and the norm-7 debt

`bindParamsJ`/`bindTargetsJ`/`paramNames` are non-fuel spellings of
`Cert.bindParams`/`Cert.bindTargets` (a `Prop` needs no fuel; the spec states the
recursion directly). This is the `defFree`/`defFreeF` precedent, and the debt is
paid the same way: an equivalence lemma (`Cert.bindParams n ps τs Γ = bindParamsJ
ps τs Γ` for sufficient `n`) lands with the adequacy work. `destr` sub-names bind at
`.any` via `paramNames` (transitive collection) rather than nested recursion —
extensionally what `Cert.bindParams` does.

`defFree` (the promotion guard) is used **by import from `Types/Core.lean`** — no
copy. This couples the module graph to the file that defines `infer`; acceptable
because the concern retired at V12 was the checked *path* calling `infer`, which a
`Prop` cannot. If module hygiene ever matters, move `defFree` down to `Syntax.lean`
(own L-number) as `isMatchView` was.

## J11 — deliberate refusals (arms with no rule), the complete list

* `.block` / `.blockpass` outside a send's `blk` slot — not values the machine
  evaluates; the send rules consume them in place (`chk` refuses too).
* `.undef` — row removal; no sound rule against a table with no notion of removal.
  (`chk` covers it claim-gated; the spec refuses. If a rule is ever wanted, its
  premise is "no claimed row mentions the name", which needs a row-mention
  predicate.)
* `.alias'` with the old name's row **in force** — same invalidation problem;
  admissible only when `declaresName D old = false` (that rule exists).
* Block-bearing `super`/`zsuper` — a `blk`-carrying row is deliberately unreadable
  (L242).
* `self` in a class body / at toplevel — `selfCls = none` refuses; a `.clsOf
  ctx.cls` answer is sound in a class body but wrong at toplevel (`main` is an
  Object *instance*), and `top`'s threading does not pin the two apart. Candidate
  widening once it does.
* Implicit-receiver literal-block sends other than `lambda` — `chk` reaches them
  only via a claim; here the assumed row lives in `D` and `sendIterA`/`sendIter0`
  need the receiver's type, which an implicit receiver supplies via `JudgeRecv`
  only in the args-bearing rule (`sendIterA`). The no-args implicit case is the
  gap; add when a corpus shape wants it.

## J12 — `JudgeElems` recurses through `Judge`'s own splat rules

`chkElems` special-cases `.splat (some o)` inline and accepts only `.cls "Array"`;
the relation just recurses, so an `.arrayOf` splat element is admissible here and
refused by `chkElems`. Sound (an `arrayOf` is an Array — `spreadA` accepts it);
recorded because it is a place a future `chk → Judge` adequacy lemma will notice.

## J13 — environment weakening is exact-type; the precision ceiling is real

`SubEnv` (reused from `Types/Ty.lean`) can **drop** a binding but never **coarsen**
one. Consequence, measured in `Examples.lean`: after `if x then … else …` narrows
`x : Int?` to `.int` in one branch, no continuation environment can retain `x` at
all (`.int` at one exit, `.nilable .int` at the other, and no common exact type), so
the join forgets the variable. The upgrade is a subtype-aware weakening
(`envGet? Γ' x = some σ ∧ subTy σ τ`) or a per-binding `joinTy` env-join — a
`Types/` widening with its own L-number, wanted before real narrowing-heavy corpora.
`chk` has the same ceiling (`subEnvB` is exact), so this loses nothing today.

## J14 — unions: the `Ty` arm is inert; `SubJ` carries the meaning; joins widen and conditionals re-narrow

`Ty.union` (L269, `Types/Ty.lean`) is deliberately **inert on the checker path** —
the alternative (a union-decomposing `subTy`) cannot stay structurally recursive on
`τ` and a well-founded `subTy` stops kernel-reducing under `chk` (norm 5 / L73),
hit at design time. The semantics live here:

* **`SubJ`** (`Sub.lean`) — declarative subtyping: `subTy` embedded whole by `base`,
  union decomposition on both sides, `nilableL` for the left decomposition `subTy`
  cannot state. Every `subTy`/`subTys` premise in `Judge` became `SubJ`/`SubJs`, so
  the relation is a strict widening and every J0 derivation still stands.
* **Widened joins for free**: the join rules already take a chosen bound, so
  `τj := mkUnion τt τe` is always eligible (`mkUnion_sub`) — no rule changed.
  `mkUnion` collapses equal sides and normalizes a `nilT` side to `.nilable`, so
  optionals keep one spelling.
* **Re-narrowing**: J5's rules generalized — premise is now any `envGet?` type;
  then-branch at `dropNil τ₀` (strips the nil half of a nilable *or union*; sound
  for every type, `false : bool` included), else-branch at `elseNarrow τ₀` (`nilT`
  when `boolFree τ₀`, unchanged otherwise) — which **retires J5's deferred
  else-branch narrowing**, with the `σ = bool` unsoundness handled by the
  `boolFree` gate instead of a side condition.
* **The named bill** (unchanged from L269): `ValueTy` has no union disjunction arm,
  so machine typing cannot yet witness a union-typed value — the J1 obligation
  before preservation can cover the union join rules. Union *receivers* also do not
  dispatch (`tyClassNames = []`); narrowing-then-dispatch is the intended pattern,
  and an all-members-agree `sigOf` arm (the L260 nilable shape) is the future
  widening if direct union dispatch is ever wanted.

Demonstrated in `Examples.lean`: `if true then 1 else "s"` at `.union .int
(.cls "String")` (a join `chk` refuses without a claim), and `x : nilT ∪ Int`
re-narrowed to `.int` by `if x` — `dropNil` reduces definitionally, so the
derivations are `rfl`-driven.

## J15 — why narrowing keys on truthiness only (no `nil?`/`is_a?` condition rules)

Answering the design question "is full-language narrowing easy?" — **no**, for two
specific, checkable reasons; truthiness over the full type language *was* easy and
is done (J14):

1. **Predicate methods are user-shadowable.** `if x.nil?` narrows soundly only if
   `nil?` resolves to `Object#nil?`/`NilClass#nil?` — but `def nil?; true; end` on
   any class makes the test lie, `defDecl` accepts such a body (no row is threaded,
   so `declaresName` does not see it), and the invariant carries no "predicate
   methods unshadowed" conjunct. Truthiness is the one test the machine performs
   **without a dispatch**, so it is unforgeable. A `nil?` rule needs either a
   no-shadow heap conjunct (machine typing, J1+) or a syntactic no-`def nil?`
   fragment condition.
2. **`is_a?`-narrowing needs `Sub`.** `subTy` has no subclass relation (`Sub` is
   equality below `any`), so "keep the union members below `.cls C`" misclassifies
   a subclass instance: `x.is_a?(C)` answers true for `D < C`, but the member
   `.cls D` is not below `.cls C` and would be dropped — narrowing would then be
   *unsound*, not just imprecise. Blocked on the ancestors-walk `Sub` rung
   (`PLAN.md` W5 T2), which is where the DRuby-style occurrence typing bill
   actually lands.
