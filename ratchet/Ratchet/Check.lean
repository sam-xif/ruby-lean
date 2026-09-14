import Ratchet.Deriv
import Ratchet.CtxEq
import Ratchet.MethodCtx

/-!
# `Ratchet/Check.lean` — the certificate checker, and the judgment it decides

Layers 1–3 of `../docs/semantics/answer-typed-schema.md` §3, built **standalone**. Nothing
here imports `Denote/`. The retained `Ratchet/Judge.lean` supplies the context/type
substrate, not the older checker or judgment (deleted in clink 68). This file owns the
answer-typed judgment, authored one justified rule at a time.

What is reused is **type-level only** — `Ratchet/Ty.lean`'s `Ty`, `Env`, `envGet?`, `envSet`,
`joinT`, `joinEnv` — and `Ratchet/Expr.lean`'s syntax. Neither mentions a judgment.

## The three layers, and which one is trusted

| layer | here | note |
|---|---|---|
| 1 | `Deriv` (`Ratchet/Deriv.lean`) | what the untrusted emitter writes |
| 2 | `check` | decides whether a certificate is a derivation *of this program*, **and types it** |
| 3 | `check_sound` | `check … = some … → DJudge …`, by induction on the fuel |

`check` **re-derives every type a certificate claims** and compares. A `Deriv.prim` carries
`recvTy` and `retTy`; `check` computes both from the sub-derivation and the primitive table
and rejects a mismatch. That is why a wrong certificate cannot produce a wrong accept, and it
is the property `Ratchet/DerivControls.lean` §4 pins.

## Why fuel

`check` recurses on a `Nat` rather than structurally on `Deriv`, for the reason `chk` did: a
`partial def` cannot be reasoned about, and `Deriv` is a nested inductive (`List Deriv`
fields) whose structural recursion Lean will accept but whose *induction* in a mutual block
with list companions is a fight. Fuel makes recursive checking explicit. Fuel
exhaustion answers `none`, so it can only cost completeness.

## Authoring a rule: **let the transport lemma write the premises and the outgoing environment**

A working rule, paid for twice (`found-issues.md` §F29, at `var` and again at `vasgn`). It is
a rule of thumb rather than a checked invariant, deliberately — see the end of this section.

**The procedure.** Before writing a `DJudge` constructor, find the `Denote/Sem/` lemma that
transports `StateOk` across the machine change the rule makes:

| the rule changes | the lemma |
|---|---|
| only `ctl`/`kont` | `StateOk_reCtl` — no premises, environment unchanged |
| the heap, by allocating | `StateOk_ext` (via `ext_push`) — environment unchanged |
| a local | `StateOk_setLocal` — **premises**, and a specific outgoing environment |
| an ivar | `StateOk_ivarWrite` |

Then: **its hypotheses are the rule's premises, and its conclusion's environment is the
rule's outgoing environment.** `vasgn` is the worked case — `StateOk_setLocal` wants
`capStale x τ τ = false` and (through `stripAlias`) `isAliasTy τ = false`, and concludes at
`envSet (killClosOver (killAliasesTo Γ x) x τ) x τ`, which is why `envAfter` exists and why
those two premises are on the constructor. Both times I wrote the rule first and guessed
`envSet` with no premises; both times the obligation refused to close.

**Why it bites even though nothing reachable triggers it.** No `DJudge` rule produces a
`Ty.sameAs` or a `Ty.clos`, so `killAliasesTo` and `killClosOver` are the identity on every
environment the *checker* can reach, and `isAliasTy` is always false there. The obligation
does not quantify over reachable environments — it quantifies over every environment a
**conformant machine** can have. That gap is the whole reason the discipline is worth stating:
testing cannot find these, and two of two rules with an interesting environment had one.

**Why it makes the *next* rule's proof simpler**, which is the real payoff. `DKontOk.asgnK`'s
tail index is literally `envAfter Γ x τ` — it matches `DJudge.vasgn`'s conclusion because both
were copied from the same lemma, so the frame clause composes with the rule by `rfl`. Had the
rule said `envSet`, every frame clause, every sequence rule and every consumer downstream
would carry a rewrite between the two. A rule stated at the transport lemma's own environment
is a rule nothing has to translate.

**The other half of the same question is §F31**: this rule says where a premise's *content*
comes from, and §F31 says a premise's sub-derivation must be the **family's** relation and not
the raw syntactic one, or the obligation is about a derivation the registry never vetted. A
rule's premises are constrained from both sides.

**Why this is not hoisted into a stated invariant.** The tempting generalisation — *a rule may
only grow the environment, never re-type an existing entry* — is **false for Ruby**:
`corpus/031-reassign-different-type.rb` is `x = 1; x = true; x` and is a legitimate program
that must type. And `killClosOver` deliberately re-types entries the rule did not bind, because
writing `x` invalidates any other binding whose type captured it. So how the environment may
evolve stays open, and soundness is forced at proof time instead. That is a choice for
flexibility, with the obligation as the forcing function.

## What is deliberately not in the judgment yet

`DJudge` has eighteen rules (plus six in the three list companions). Everything else a `Deriv` can express —
`callMethodSig`, `classDecl`, `newInst`, `ivarRead`, `ivarAsgn`, `constCls`,
`selfExpr` — answers `none`, by name, in `check`'s last arms. They join a rule at
a time, and each one joining is a rung.

`DJudge` now carries distinct incoming/outgoing contexts and ivar spines, as do all three
companions. Guards and state transitions are copied from the context-general semantic
proofs. Trailing `optParam` indices keep existing top-level derivations readable; defaults
are only notation, not a restriction of the relation. Use `@DJudge` when passing the entire
family as a value. The executable checker accepts the incoming context/spine and returns
the outgoing indices with their derivation. Branch compatibility uses proof-producing
`ctxEq?`; unsupported comparisons decline rather than assert an equality. Neither method
rule is admitted yet: a stored signature must be justified by its annotation-checked body.
-/

set_option autoImplicit false

namespace Ratchet

/-! ## §1 The primitive table

The rules for sends this fragment can type, as an inductive (`DPrim`) with a decision
procedure (`dprim?`) and a soundness lemma between them. Sixteen rows.

The table grows with proved builtin obligations. `Judge.lean`'s `PrimSig` has ~90 rows and `Denote/`'s
`Sem.Judge.prim` — the obligation that every one of them is true of CRuby — is one of the 35
rules with no proof, priced at "~200 conformance facts, two per row"
(`implementation-notes.md`, EMERGENCY EXIT). A table that grows a row at a time is a table
whose semantic obligation can grow a row at a time too, which is the whole argument for
starting again here rather than inheriting.

Each row is proved against the executable semantics in `Denote/Typed/PrimitiveBuiltin.lean`,
under the heap conformance facts in `Denote/Sem/PrimHeap.lean`. -/

inductive DPrim : Ty → String → List Ty → Ty → Prop
  /-- `Integer#+`, `-`, `*`, `/` at an `Integer` argument. `/` included: integer division by
      zero raises `ZeroDivisionError`, which is outside the
      `NoMethodError`/`ArgumentError`/`TypeError` family this ladder is about, so the row is
      about types and not about totality. -/
  | intAdd : DPrim .int "+" [.int] .int
  | intSub : DPrim .int "-" [.int] .int
  | intMul : DPrim .int "*" [.int] .int
  | intDiv : DPrim .int "/" [.int] .int
  /-- `Integer#<`; `<=` and `>=` also have rows below. -/
  | intLt : DPrim .int "<" [.int] .bool
  /-- Decimal conversion allocates a String; optional radix arguments are separate rows. -/
  | intToS : DPrim .int "to_s" [] (.cls "String")
  /-- Conformance excludes the reverse call to a program-defined `==` on the argument. -/
  | intEq {α : Ty} : DPrim .int "==" [α] .bool
  | intZero : DPrim .int "zero?" [] .bool
  | intLe : DPrim .int "<=" [.int] .bool
  | intGe : DPrim .int ">=" [.int] .bool
  | nilEq {α : Ty} : DPrim .nilT "==" [α] .bool
  | strLength : DPrim (.cls "String") "length" [] .int
  /-- `String#+` at a `String` argument — a `TypeError` at any other, which is why the
      argument type is pinned rather than free. -/
  | strAdd : DPrim (.cls "String") "+" [.cls "String"] (.cls "String")
  /-- `!` on a boolean. Ruby's `!` is defined on every object, but this row is the only one
      the fragment can justify: on an arbitrary receiver the result is still `Boolean`, and
      claiming that needs to know the program has not redefined `!` — the `nameFree`-shaped
      premise this judgment has no context to state. So: booleans only, and the restriction
      is recorded rather than assumed away. -/
  | notBool : DPrim .bool "!" [] .bool
  /-- Index evaluation must retain the receiver's element denotations. -/
  | arrayIndex {τ : Ty} : FirstOrder τ = true → DPrim (.arrayOf τ) "[]" [.int] (.nilable τ)
  /-- Hash query types need not match stored keys; misses return nil. -/
  | hashIndex {σ τ α : Ty} :
      FirstOrder (.hashOf σ τ) = true → DPrim (.hashOf σ τ) "[]" [α] (.nilable τ)

/-- The decidable counterpart. A miss is `none`, never a guess. -/
def dprim? : Ty → String → List Ty → Option Ty
  | .int, "+", [.int] => some .int
  | .int, "-", [.int] => some .int
  | .int, "*", [.int] => some .int
  | .int, "/", [.int] => some .int
  | .int, "<", [.int] => some .bool
  | .int, "to_s", [] => some (.cls "String")
  | .int, "==", [_] => some .bool
  | .int, "zero?", [] => some .bool
  | .int, "<=", [.int] => some .bool
  | .int, ">=", [.int] => some .bool
  | .nilT, "==", [_] => some .bool
  | .cls "String", "length", [] => some .int
  | .cls "String", "+", [.cls "String"] => some (.cls "String")
  | .bool, "!", [] => some .bool
  | .arrayOf τ, "[]", [.int] => if FirstOrder τ then some (.nilable τ) else none
  | .hashOf σ τ, "[]", [_] => if FirstOrder (.hashOf σ τ) then some (.nilable τ) else none
  | _, _, _ => none

theorem dprim?_sound {σ : Ty} {m : String} {as : List Ty} {τ : Ty}
    (h : dprim? σ m as = some τ) : DPrim σ m as τ := by
  unfold dprim? at h
  split at h
  · rw [Option.some.injEq] at h; subst h; exact .intAdd
  · rw [Option.some.injEq] at h; subst h; exact .intSub
  · rw [Option.some.injEq] at h; subst h; exact .intMul
  · rw [Option.some.injEq] at h; subst h; exact .intDiv
  · rw [Option.some.injEq] at h; subst h; exact .intLt
  · rw [Option.some.injEq] at h; subst h; exact .intToS
  · rw [Option.some.injEq] at h; subst h; exact .intEq
  · rw [Option.some.injEq] at h; subst h; exact .intZero
  · rw [Option.some.injEq] at h; subst h; exact .intLe
  · rw [Option.some.injEq] at h; subst h; exact .intGe
  · rw [Option.some.injEq] at h; subst h; exact .nilEq
  · rw [Option.some.injEq] at h; subst h; exact .strLength
  · rw [Option.some.injEq] at h; subst h; exact .strAdd
  · rw [Option.some.injEq] at h; subst h; exact .notBool
  · split at h
    · rw [Option.some.injEq] at h; subst h; exact .arrayIndex (by assumption)
    · cases h
  · split at h
    · rw [Option.some.injEq] at h; subst h; exact .hashIndex (by assumption)
    · cases h
  · exact absurd h (by simp)

/-! ## §1a The environment a write leaves behind

`envSet` alone is not it. A local write can invalidate two kinds of binding elsewhere in the
environment, and both are `Ratchet/Ty.lean`'s functions rather than anything new here:

* **an alias** (`Ty.sameAs y τ`) recorded for the desugarer's `&&`/`case` temporaries — once
  `x` holds a new object, a binding that said "same value as `x`" no longer does
  (`killAliasesTo`);
* **a closure's captured spine** — a `Ty.clos` records the locals as of its creation, and
  rebinding one of them makes that record stale (`killClosOver`).

Neither can arise in the fragment `DJudge` types today: no rule produces a `sameAs` or a
`clos`, so both functions are the identity on every environment the checker can reach. They
are here anyway, because the **obligation** quantifies over every environment a conformant
machine can have, and `StateOk_setLocal` is stated at exactly this environment. Writing
`envSet` instead would make `SemA.vasgn` unprovable — the same shape as §F29 one rule over. -/

/-- The environment after writing `x : σ`. Exactly `StateOk_setLocal`'s outgoing environment,
so the rule and the conformance lemma agree by construction rather than by a rewrite. -/
def envAfter (Γ : Env) (x : String) (σ : Ty) : Env :=
  envSet (killClosOver (killAliasesTo Γ x) x σ) x σ

/-- Argument-list syntax is interpreted specially by `startArgs`, rather than evaluated
as an ordinary expression. A semantic argument premise must exclude those heads. -/
def plainArgB : Expr → Bool
  | .splat _ | .kwargs _ | .fwd => false
  | _ => true

/-! ## §2 The judgment

`DJudge Γ e τ Γ' κ I κ' I'`: expression `e` transforms the incoming state index into the
outgoing one and returns type `τ`. Omitting the four trailing indices selects top level.
Three companions: arguments/array elements (`DJudgeAll`), statement sequences (`DJudgeSeq`),
and interleaved key/value pairs (`DJudgePairs`).

Every rule is one line and says one thing. That is the property worth protecting: the old
judgment's rules acquired premises over time (`nameFree`, `ctxKept`, `capStaleCtx`,
`primDispatchOk`) because each was found to be *needed* by a semantic obligation or a
soundness bug, and the reason they could accumulate unnoticed is that nothing forced a rule
and its justification to arrive together. -/

mutual
inductive DJudge : Env → Expr → Ty → Env → (κ : optParam Ctx ctx0) →
    (I : optParam Ty .ivar0) → optParam Ctx κ → optParam Ty I → Prop
  /-- An integer literal, negative ones included: `-5` desugars to `int (-5)`, not to a
      unary send. -/
  | intLit {κ : Ctx} {Γ : Env} {I : Ty} {n : Int} : DJudge Γ (.int n) .int Γ κ I
  /-- A float literal, carried as IEEE-754 bits by the syntax layer. -/
  | fltLit {κ : Ctx} {Γ : Env} {I : Ty} {b : UInt64} : DJudge Γ (.flt b) .float Γ κ I
  /-- A string literal is an *instance* of `String`; `Ty` has no string arm. -/
  | strLit {κ : Ctx} {Γ : Env} {I : Ty} {s : String} : DJudge Γ (.str s) (.cls "String") Γ κ I
  | symLit {κ : Ctx} {Γ : Env} {I : Ty} {s : String} : DJudge Γ (.sym s) .sym Γ κ I
  | truLit {κ : Ctx} {Γ : Env} {I : Ty} : DJudge Γ .tru .bool Γ κ I
  | flsLit {κ : Ctx} {Γ : Env} {I : Ty} : DJudge Γ .fls .bool Γ κ I
  | nilLit {κ : Ctx} {Γ : Env} {I : Ty} : DJudge Γ .nil .nilT Γ κ I
  /-- Reading a local. The type comes from the environment, so there is nothing for a
      certificate to choose and `Deriv.var` carries only the name.

      **`halias` — recovered by the answer-typed obligation** (`found-issues.md` §F29, and
      it is `§F5` found a second time the same way). Without it the rule is not provable:
      `StateOk`'s environment component gives `denM (stripAlias τ)`, so at a binding whose
      type is a `Ty.sameAs` the conclusion claims more than conformance supplies. No
      `DJudge` rule *produces* a `sameAs`, so no reachable environment has one — but
      `SemJudgeA` quantifies over every environment with a conformant machine, which is
      what made the gap visible. -/
  | var {κ : Ctx} {Γ : Env} {I τ : Ty} {x : String} :
      envGet? Γ x = some τ → isAliasTy τ = false → DJudge Γ (.var .lvar x) τ Γ κ I
  /-- Assignment. Its *value* is the right-hand side's (Ruby's `x = e` evaluates to `e`) and
      its *effect* is to record that type for `x`. The binding lands in `Γ₁` — the
      environment the right-hand side left behind — not in `Γ`, because the right-hand side
      may itself assign (`y = (x = 1) + 1`).

      **The two premises and `envAfter` were forced by the obligation**, not chosen: the
      conformance lemma for a local write (`StateOk_setLocal`) needs both, and produces
      exactly `envAfter`'s environment. `hcap` says the written type does not mention `x` in a
      captured spine (writing `x` would make that spine stale); `halias` is §F29's, one rule
      over — `envSet` records the right-hand side's type verbatim, and an alias type there
      would claim `x` and `y` hold the same object, which the assignment does not establish. -/
  | vasgn {κ κ' : Ctx} {Γ Γ' : Env} {I I' τ : Ty} {e : Expr} {x : String} :
      DJudge Γ e τ Γ' κ I κ' I' → capStale x τ τ = false → isAliasTy τ = false →
      capStaleCtx x τ κ' = false →
      DJudge Γ (.vasgn .lvar x e) τ (envAfter Γ' x τ) κ I κ' (killClosOverSpine I' x τ)
  /-- A statement sequence, via `DJudgeSeq`. -/
  | seq {κ κ' : Ctx} {Γ Γ' : Env} {I I' : Ty} {es : List Expr} {τ : Ty} :
      DJudgeSeq Γ es τ Γ' κ I κ' I' → DJudge Γ (.seq es) τ Γ' κ I κ' I'
  /-- A send with an explicit receiver, resolved by the primitive table. Receiver first, then
      arguments left to right — Ruby's own evaluation order, which is what makes threading
      `Γ` through them in this order the right claim. -/
  | prim {κ κ₁ κ₂ : Ctx} {Γ Γ₁ Γ₂ : Env} {I I₁ I₂ : Ty}
      {recv : Expr} {m : String} {args : List Expr}
      {σ τ : Ty} {argTys : List Ty} :
      DJudge Γ recv σ Γ₁ κ I κ₁ I₁ → DJudgeAll Γ₁ args argTys Γ₂ κ₁ I₁ κ₂ I₂ →
      DPrim σ m argTys τ → nameFreeN κ₂ m = true →
      (σ = .cls "String" → isANoOk κ₂.wholeCls (["String", "Comparable"] ++ rootAncestors) = true) →
      DJudge Γ (.send (some recv) m args none) τ Γ₂ κ I κ₂ I₂
  /-- `if c then t else e end`. The type is the join of the branches; the outgoing
      environment is the **pointwise** join, which is a soundness requirement rather than a
      precision one (`Ratchet/Ty.lean`'s `joinEnv`: carrying the pre-`if` environment forward
      certifies a program that really raises `TypeError`).

      The condition's outgoing environment `Γc` is what *both* branches start from: Ruby
      evaluates the condition before either. No narrowing — a `nilable` or `union` condition
      refines nothing here, and the rule that would do the refining is a separate rule with a
      separate justification. -/
  | if' {κ κc κ' : Ctx} {Γ Γc Γ₁ Γ₂ : Env} {I Ic I' : Ty} {c t e : Expr} {σ τ₁ τ₂ : Ty} :
      DJudge Γ c σ Γc κ I κc Ic → DJudge Γc t τ₁ Γ₁ κc Ic κ' I' →
      DJudge Γc e τ₂ Γ₂ κc Ic κ' I' →
      DJudge Γ (.if' c t (some e)) (joinT τ₁ τ₂) (joinEnv Γ₁ Γ₂) κ I κ' I'
  /-- The absent else leaves `Γc` unchanged and returns nil. Join both paths. -/
  | ifNoElse {κ κc : Ctx} {Γ Γc Γt : Env} {I Ic : Ty} {c t : Expr} {σ τ : Ty} :
      DJudge Γ c σ Γc κ I κc Ic → DJudge Γc t τ Γt κc Ic →
      DJudge Γ (.if' c t none) (joinT τ .nilT) (joinEnv Γt Γc) κ I κc Ic
  /-- `BareNameFree` currently certifies absence only for `x`. Ordinary sends do not
      use this rule: a missing `x()` raises NoMethodError rather than NameError. -/
  | bareName {κ : Ctx} {Γ : Env} {I : Ty} : nameFreeN κ "x" = true →
      nameFreeN κ "method_missing" = true → κ.selfTy = none → DJudge Γ (.vcall "x") .any Γ κ I
  /-- Later elements preserve earlier first-order values. Closure types need stronger
      capture tracking before they can be retained across arbitrary element evaluation. -/
  | arrayLit {κ κ' : Ctx} {Γ Γ' : Env} {I I' : Ty} {es : List Expr} {tys : List Ty} :
      DJudgeAll Γ es tys Γ' κ I κ' I' → FirstOrder (elemTy tys) = true →
      DJudge Γ (.array es) (.arrayOf (elemTy tys)) Γ' κ I κ' I'
  /-- Pair evaluation is interleaved, not all keys followed by all values. -/
  | hashLit {κ κ' : Ctx} {Γ Γ' : Env} {I I' : Ty} {ps : List (Expr × Expr)} {ks vs : List Ty} :
      DJudgePairs Γ ps ks vs Γ' κ I κ' I' → FirstOrder (elemTy ks) = true →
      FirstOrder (elemTy vs) = true → DJudge Γ (.hash ps) (.hashOf (elemTy ks) (elemTy vs)) Γ' κ I κ' I'
  /-- The body is required at its annotations, including for uncalled definitions. -/
  | defDecl {κ : Ctx} {Γ Γb : Env} {I τ : Ty} {d : Defn} {ps : List SigParam} :
      d.params = ps.map (fun p => Param.req p.1) →
      (∀ p ∈ ps, FirstOrder p.2 = true ∧ isAliasTy p.2 = false) → FirstOrder τ = true →
      DJudge ps d.body τ Γb (topBodyCtx κ d) I (topBodyCtx κ d) I →
      κ.scope.runtimeMain = true → κ.classes = [] → κ.selfTy = none → κ.blockTy = none →
      κ.consts = [] → κ.asms = [] → FirstOrder I = true →
      (∀ p ∈ Γ, FirstOrder (stripAlias p.2) = true) →
      (∀ old ∈ κ.defs, old.name ≠ d.name) → "method_missing" ≠ d.name → "method_added" ≠ d.name →
      DJudge Γ (.def' d.name d.params d.body) .sym Γ κ I (topDeclCtx κ d) I
  /-- Calls consume an already checked body at its declared signature, not at a caller's
      inferred argument shape. The premise remains explicit for every registry backend. -/
  | callSig {κ κ' : Ctx} {Γ Γ' Γb : Env} {I I' τ : Ty} {decl : Defn}
      {ps : List SigParam} {args : List Expr} :
      decl.params = ps.map (fun p => Param.req p.1) →
      (∀ p ∈ ps, FirstOrder p.2 = true ∧ isAliasTy p.2 = false) → FirstOrder τ = true →
      DJudge ps decl.body τ Γb (κ'.withFrame (some ⟨"Object", "Object", decl.name⟩)) I'
        (κ'.withFrame (some ⟨"Object", "Object", decl.name⟩)) I' →
      DJudgeAll Γ args (ps.map (·.2)) Γ' κ I κ' I' → decl ∈ κ'.defs →
      κ.scope.runtimeMain = true → κ'.scope.runtimeMain = true → κ'.selfTy = none →
      κ'.blockTy = none → κ'.consts = [] → κ'.asms = [] → FirstOrder I' = true →
      (∀ p ∈ Γ', FirstOrder (stripAlias p.2) = true) →
      DJudge Γ (.send none decl.name args none) τ Γ' κ I κ' I'

inductive DJudgeAll : Env → List Expr → List Ty → Env → (κ : optParam Ctx ctx0) →
    (I : optParam Ty .ivar0) → optParam Ctx κ → optParam Ty I → Prop
  | nil {κ : Ctx} {Γ : Env} {I : Ty} : DJudgeAll Γ [] [] Γ κ I
  | cons {κ κ₁ κ₂ : Ctx} {Γ Γ₁ Γ₂ : Env} {I I₁ I₂ τ : Ty}
      {e : Expr} {es : List Expr} {τs : List Ty} :
      DJudge Γ e τ Γ₁ κ I κ₁ I₁ → DJudgeAll Γ₁ es τs Γ₂ κ₁ I₁ κ₂ I₂ → plainArgB e = true →
      DJudgeAll Γ (e :: es) (τ :: τs) Γ₂ κ I κ₂ I₂

inductive DJudgeSeq : Env → List Expr → Ty → Env → (κ : optParam Ctx ctx0) →
    (I : optParam Ty .ivar0) → optParam Ctx κ → optParam Ty I → Prop
  /-- The sequence's type is its **last** statement's. -/
  | last {κ κ' : Ctx} {Γ Γ' : Env} {I I' τ : Ty} {e : Expr} :
      DJudge Γ e τ Γ' κ I κ' I' → DJudgeSeq Γ [e] τ Γ' κ I κ' I'
  | cons {κ κ₁ κ₂ : Ctx} {Γ Γ₁ Γ₂ : Env} {I I₁ I₂ σ τ : Ty}
      {e e' : Expr} {es : List Expr} :
      DJudge Γ e σ Γ₁ κ I κ₁ I₁ → DJudgeSeq Γ₁ (e' :: es) τ Γ₂ κ₁ I₁ κ₂ I₂ →
      DJudgeSeq Γ (e :: e' :: es) τ Γ₂ κ I κ₂ I₂

inductive DJudgePairs : Env → List (Expr × Expr) → List Ty → List Ty → Env →
    (κ : optParam Ctx ctx0) → (I : optParam Ty .ivar0) → optParam Ctx κ → optParam Ty I → Prop
  | nil {κ : Ctx} {Γ : Env} {I : Ty} : DJudgePairs Γ [] [] [] Γ κ I
  | cons {κ κk κv κ' : Ctx} {Γ Γk Γv Γ' : Env} {I Ik Iv I' σ τ : Ty}
      {k v : Expr} {ps : List (Expr × Expr)} {ks vs : List Ty} :
      DJudge Γ k σ Γk κ I κk Ik → DJudge Γk v τ Γv κk Ik κv Iv →
      DJudgePairs Γv ps ks vs Γ' κv Iv κ' I' →
      DJudgePairs Γ ((k, v) :: ps) (σ :: ks) (τ :: vs) Γ' κ I κ' I'
end

theorem DJudge.plainArg {κ κ' : Ctx} {I I' : Ty} {Γ Γ' : Env} {e : Expr} {τ : Ty}
    (h : DJudge Γ e τ Γ' κ I κ' I') :
    plainArgB e = true := by cases h <;> rfl

/-! ## §3 The checker, which *builds* the derivation

`check` does not return a `Ty` and leave soundness to a separate induction — it returns the
`DJudge` term. So layer 3 is not a theorem about layer 2, it is layer 2's **type**, and the
oracle that judges a rung is the Lean typechecker: if `check` compiles, every answer it can
ever give carries a derivation.

That is the same move as `Denote/Clink/`'s `Clink.sem` one level down, and it was chosen over
`check : … → Option (Ty × Env)` plus `check_sound` for a reason worth recording: the latter is
one `induction fuel` with a `split` over a 23-arm match, and every arm of it is a place where
the proof can be *weaker* than the function (an arm whose `none` case is discharged by
`simp` proves nothing about the arm's real behaviour). Here there is no gap to be weaker
across.

**Everything is computed from the program and *compared* against the certificate.** The
program is the authority: `check` matches `e`, derives the type itself, and then asks whether
the certificate agrees. A certificate that names a different literal, a different method, or a
different join is rejected — not because soundness needs it (it does not; the derivation is
about `e` either way) but because a checker that ignores its certificate is not checking one,
and the whole pipeline downstream of `scripts/emit_deriv.py` would be unfalsifiable.
`Ratchet/DerivControls.lean` pins each of those rejections.

### Why fuel

`Deriv` is a nested inductive and `check` is mutual with three list companions; fuel makes the
recursion structural and obviously terminating. Exhaustion answers `none`, so it can only cost
completeness. -/

/-- A body checked once at its parameter/return annotations. Calls reuse this artifact. -/
structure CheckedBody (κ : Ctx) (I : Ty) (decl : Defn) where
  params : List SigParam
  ret : Ty
  out : Env
  paramShape : decl.params = params.map (fun p => Param.req p.1)
  paramsFO : ∀ p ∈ params, FirstOrder p.2 = true ∧ isAliasTy p.2 = false
  returnFO : FirstOrder ret = true
  judged : DJudge params decl.body ret out κ I κ I

/-- Checker data, not a new judgment premise. Exact context checks prevent stale proofs
from being reused after a definition, spine change, or incompatible branch. -/
structure CachedBody where
  ctx : Ctx
  spine : Ty
  decl : Defn
  body : CheckedBody ctx spine decl

abbrev BodyCache := List CachedBody

structure CallableBody (κ : Ctx) (I : Ty) (name : String) where
  decl : Defn
  nameOk : decl.name = name
  body : CheckedBody (κ.withFrame (some ⟨"Object", "Object", decl.name⟩)) I decl
  installed : decl ∈ κ.defs

def findBody (κ : Ctx) (I : Ty) (name : String) : BodyCache → Option (CallableBody κ I name)
  | [] => none
  | c :: cs =>
    let found : Option (CallableBody κ I name) := do
      if hn : c.decl.name = name then do
        let ⟨hc⟩ ← ctxEq? c.ctx (κ.withFrame (some ⟨"Object", "Object", c.decl.name⟩))
        if hi : c.spine = I then do
          let ⟨hd⟩ ← defnMem? c.decl κ.defs
          some ⟨c.decl, hn, by simpa only [hc, hi] using c.body, hd⟩
        else none
      else none
    found.orElse (fun _ => findBody κ I name cs)

/-- A checked answer: the type and every outgoing state index, with their derivation.
No outgoing declaration table is reconstructed separately from the expression proof. -/
structure Certified (Γ : Env) (e : Expr) (κ : Ctx := ctx0) (I : Ty := .ivar0) where
  ty : Ty
  out : Env
  ctx : Ctx
  spine : Ty
  judged : DJudge Γ e ty out κ I ctx spine
  cache : BodyCache := []

structure CertifiedAll (Γ : Env) (es : List Expr) (κ : Ctx := ctx0) (I : Ty := .ivar0) where
  tys : List Ty
  out : Env
  ctx : Ctx
  spine : Ty
  judged : DJudgeAll Γ es tys out κ I ctx spine
  cache : BodyCache := []

structure CertifiedSeq (Γ : Env) (es : List Expr) (κ : Ctx := ctx0) (I : Ty := .ivar0) where
  ty : Ty
  out : Env
  ctx : Ctx
  spine : Ty
  judged : DJudgeSeq Γ es ty out κ I ctx spine
  cache : BodyCache := []

structure CertifiedPairs (Γ : Env) (ps : List (Expr × Expr)) (κ : Ctx := ctx0) (I : Ty := .ivar0) where
  keys : List Ty
  vals : List Ty
  out : Env
  ctx : Ctx
  spine : Ty
  judged : DJudgePairs Γ ps keys vals out κ I ctx spine
  cache : BodyCache := []

mutual
/-- The program selects the rule; the certificate supplies sub-derivations and checked
claims. Every recursive result carries its actual outgoing context, locals, and spine. -/
def check (fuel : Nat) (Γ : Env) (e : Expr) (d : Deriv) (κ : Ctx := ctx0) (I : Ty := .ivar0) (cache : BodyCache := []) :
    Option (Certified Γ e κ I) :=
  match fuel with
  | 0 => none
  | n + 1 =>
    match e, d with
    | .int k, .intLit k' => if k == k' then some ⟨.int, Γ, κ, I, .intLit, cache⟩ else none
    | .flt b, .fltLit b' => if b == b' then some ⟨.float, Γ, κ, I, .fltLit, cache⟩ else none
    | .str s, .strLit s' => if s == s' then some ⟨.cls "String", Γ, κ, I, .strLit, cache⟩ else none
    | .sym s, .symLit s' => if s == s' then some ⟨.sym, Γ, κ, I, .symLit, cache⟩ else none
    | .tru, .truLit => some ⟨.bool, Γ, κ, I, .truLit, cache⟩
    | .fls, .flsLit => some ⟨.bool, Γ, κ, I, .flsLit, cache⟩
    | .nil, .nilLit => some ⟨.nilT, Γ, κ, I, .nilLit, cache⟩
    | .vcall "x", .bareName "x" =>
      if hx : nameFreeN κ "x" = true then
        if hm : nameFreeN κ "method_missing" = true then
          if hs : κ.selfTy = none then some ⟨.any, Γ, κ, I, .bareName hx hm hs, cache⟩ else none
        else none
      else none
    | .var .lvar x, .var .lvar x' =>
      if x == x' then
        match hg : envGet? Γ x with
        | some τ => if ha : isAliasTy τ = false then some ⟨τ, Γ, κ, I, .var hg ha, cache⟩ else none
        | none => none
      else none
    | .vasgn .lvar x ev, .vasgn .lvar x' dv =>
      if x == x' then
        match check n Γ ev dv κ I cache with
        | some ⟨τ, Γ₁, κ₁, I₁, hv, cv⟩ =>
          if hcap : capStale x τ τ = false then
            if ha : isAliasTy τ = false then
              if hk : capStaleCtx x τ κ₁ = false then
                some ⟨τ, envAfter Γ₁ x τ, κ₁, killClosOverSpine I₁ x τ, .vasgn hv hcap ha hk, cv⟩
              else none
            else none
          else none
        | none => none
      else none
    | .seq es, .seq ds =>
      match checkSeq n Γ es ds κ I cache with
      | some ⟨τ, Γ', κ', I', hs, cs⟩ => some ⟨τ, Γ', κ', I', .seq hs, cs⟩
      | none => none
    | .send (some recv) m args none, .prim dr dm dargs σc τc =>
      if dm == m then
        match check n Γ recv dr κ I cache with
        | some ⟨σ, Γ₁, κ₁, I₁, hr, cr⟩ =>
          if σ == σc then
            match checkAll n Γ₁ args dargs κ₁ I₁ cr with
            | some ⟨argTys, Γ₂, κ₂, I₂, ha, ca⟩ =>
              match hp : dprim? σ m argTys with
              | some τ =>
                if τ == τc then
                  if hf : nameFreeN κ₂ m = true then
                    if hs : σ = .cls "String" →
                        isANoOk κ₂.wholeCls (["String", "Comparable"] ++ rootAncestors) = true then
                      some ⟨τ, Γ₂, κ₂, I₂, .prim hr ha (dprim?_sound hp) hf hs, ca⟩
                    else none
                  else none
                else none
              | none => none
            | none => none
          else none
        | none => none
      else none
    | .if' c t (some el), .ifD dc dt (some de) j =>
      match check n Γ c dc κ I cache with
      | some ⟨_, Γc, κc, Ic, hc, cc⟩ =>
        match check n Γc t dt κc Ic cc, check n Γc el de κc Ic cc with
        | some ⟨τ₁, Γ₁, κ₁, I₁, ht, ct⟩, some ⟨τ₂, Γ₂, κ₂, I₂, he, _⟩ =>
          if joinT τ₁ τ₂ == j then
            match ctxEq? κ₁ κ₂ with
            | some ⟨hctx⟩ =>
              if hi : I₁ = I₂ then
                some ⟨joinT τ₁ τ₂, joinEnv Γ₁ Γ₂, κ₁, I₁,
                  .if' hc ht (by cases hctx; cases hi; exact he), ct⟩
              else none
            | none => none
          else none
        | _, _ => none
      | none => none
    | .if' c t none, .ifD dc dt none j =>
      match check n Γ c dc κ I cache with
      | some ⟨_, Γc, κc, Ic, hc, cc⟩ =>
        match check n Γc t dt κc Ic cc with
        | some ⟨τ, Γt, κt, It, ht, _⟩ =>
          if joinT τ .nilT == j then
            match ctxEq? κt κc with
            | some ⟨hctx⟩ =>
              if hi : It = Ic then
                some ⟨joinT τ .nilT, joinEnv Γt Γc, κc, Ic,
                  .ifNoElse hc (by cases hctx; cases hi; exact ht), cc⟩
              else none
            | none => none
          else none
        | none => none
      | none => none
    | .array es, .arrayLit ds elem =>
      match checkAll n Γ es ds κ I cache with
      | some ⟨tys, Γ', κ', I', hs, cs⟩ =>
        if elemTy tys == elem then
          if hf : FirstOrder (elemTy tys) = true then
            some ⟨.arrayOf (elemTy tys), Γ', κ', I', .arrayLit hs hf, cs⟩
          else none
        else none
      | none => none
    | .hash ps, .hashLit dks dvs key val =>
      match checkPairs n Γ ps dks dvs κ I cache with
      | some ⟨ks, vs, Γ', κ', I', hs, cs⟩ =>
        if elemTy ks == key && elemTy vs == val then
          if hk : FirstOrder (elemTy ks) = true then
            if hv : FirstOrder (elemTy vs) = true then
              some ⟨.hashOf (elemTy ks) (elemTy vs), Γ', κ', I', .hashLit hs hk hv, cs⟩
            else none
          else none
        else none
      | none => none
    | .def' name formals body, .defDecl name' ps ret db => do
      if name != name' then none else do
      if hm : κ.scope.runtimeMain = true then do
      if hc : κ.classes.isEmpty = true then do
      if hs : κ.selfTy = none then do
      if hb : κ.blockTy = none then do
      if hco : κ.consts = [] then do
      if ha : κ.asms = [] then do
      if hi : FirstOrder I = true then do
      if hg : Γ.all (fun p => FirstOrder (stripAlias p.2)) = true then do
      if hf : κ.defs.all (fun old => old.name != name) = true then do
      if hmiss : "method_missing" ≠ name then do
      if hquiet : "method_added" ≠ name then do
        let decl : Defn := ⟨name, formals, body⟩
        let c ← checkMethodBody n (topBodyCtx κ decl) I decl (.defDecl name' ps ret db) cache
        some ⟨.sym, Γ, topDeclCtx κ decl, I,
          .defDecl c.paramShape c.paramsFO c.returnFO c.judged hm
            (List.isEmpty_iff.mp hc) hs hb hco ha hi (List.all_eq_true.mp hg)
            (by simpa only [List.all_eq_true, bne_iff_ne] using hf) hmiss hquiet,
          ⟨topBodyCtx κ decl, I, decl, c⟩ :: cache⟩
      else none
      else none
      else none
      else none
      else none
      else none
      else none
      else none
      else none
      else none
      else none
    | .send none name args none, .callSig name' ds ret => do
      if name != name' then none else do
      let a ← checkAll n Γ args ds κ I cache
      let c ← findBody a.ctx a.spine name a.cache
      if ht : a.tys = c.body.params.map (·.2) then do
      if hr : c.body.ret = ret then do
      if hstart : κ.scope.runtimeMain = true then do
      if hm : a.ctx.scope.runtimeMain = true then do
      if hs : a.ctx.selfTy = none then do
      if hb : a.ctx.blockTy = none then do
      if hco : a.ctx.consts = [] then do
      if ha : a.ctx.asms = [] then do
      if hi : FirstOrder a.spine = true then do
      if hg : a.out.all (fun p => FirstOrder (stripAlias p.2)) = true then
        some ⟨c.body.ret, a.out, a.ctx, a.spine, by
          simpa only [c.nameOk] using
            (DJudge.callSig c.body.paramShape c.body.paramsFO c.body.returnFO c.body.judged
              (by simpa only [ht] using a.judged) c.installed hstart hm hs hb hco ha hi
              (List.all_eq_true.mp hg)), a.cache⟩
      else none
      else none
      else none
      else none
      else none
      else none
      else none
      else none
      else none
      else none
    | _, _ => none

def checkAll (fuel : Nat) (Γ : Env) (es : List Expr) (ds : List Deriv)
    (κ : Ctx := ctx0) (I : Ty := .ivar0) (cache : BodyCache := []) : Option (CertifiedAll Γ es κ I) :=
  match fuel with
  | 0 => none
  | n + 1 =>
    match es, ds with
    | [], [] => some ⟨[], Γ, κ, I, .nil, cache⟩
    | e :: es', d :: ds' =>
      match check n Γ e d κ I cache with
      | some ⟨τ, Γ₁, κ₁, I₁, he, ce⟩ =>
        match checkAll n Γ₁ es' ds' κ₁ I₁ ce with
        | some ⟨τs, Γ₂, κ₂, I₂, hr, cr⟩ => some ⟨τ :: τs, Γ₂, κ₂, I₂, .cons he hr he.plainArg, cr⟩
        | none => none
      | none => none
    | _, _ => none

def checkPairs (fuel : Nat) (Γ : Env) (ps : List (Expr × Expr)) (dks dvs : List Deriv)
    (κ : Ctx := ctx0) (I : Ty := .ivar0) (cache : BodyCache := []) : Option (CertifiedPairs Γ ps κ I) :=
  match fuel with
  | 0 => none
  | n + 1 =>
    match ps, dks, dvs with
    | [], [], [] => some ⟨[], [], Γ, κ, I, .nil, cache⟩
    | (k, v) :: ps', dk :: dks', dv :: dvs' =>
      match check n Γ k dk κ I cache with
      | some ⟨σ, Γk, κk, Ik, hk, ck⟩ =>
        match check n Γk v dv κk Ik ck with
        | some ⟨τ, Γv, κv, Iv, hv, cv⟩ =>
          match checkPairs n Γv ps' dks' dvs' κv Iv cv with
          | some ⟨ks, vs, Γ', κ', I', hs, cs⟩ => some ⟨σ :: ks, τ :: vs, Γ', κ', I', .cons hk hv hs, cs⟩
          | none => none
        | none => none
      | none => none
    | _, _, _ => none

def checkSeq (fuel : Nat) (Γ : Env) (es : List Expr) (ds : List Deriv)
    (κ : Ctx := ctx0) (I : Ty := .ivar0) (cache : BodyCache := []) : Option (CertifiedSeq Γ es κ I) :=
  match fuel with
  | 0 => none
  | n + 1 =>
    match es, ds with
    | [e], [d] =>
      match check n Γ e d κ I cache with
      | some ⟨τ, Γ', κ', I', he, ce⟩ => some ⟨τ, Γ', κ', I', .last he, ce⟩
      | none => none
    | e :: e' :: es', d :: d' :: ds' =>
      match check n Γ e d κ I cache with
      | some ⟨_, Γ₁, κ₁, I₁, he, ce⟩ =>
        match checkSeq n Γ₁ (e' :: es') (d' :: ds') κ₁ I₁ ce with
        | some ⟨τ, Γ₂, κ₂, I₂, hr, cr⟩ => some ⟨τ, Γ₂, κ₂, I₂, .cons he hr, cr⟩
        | none => none
      | none => none
    | _, _ => none

/-- Check the declaration's body once in its annotation environment. Caller locals and
argument values are deliberately not inputs. Return compatibility is exact for now;
subtyping needs a proved denotation-inclusion rule, not the legacy unchecked `subTy`. -/
def checkMethodBody (fuel : Nat) (κ : Ctx) (I : Ty) (decl : Defn) (d : Deriv)
    (cache : BodyCache := []) : Option (CheckedBody κ I decl) :=
  match fuel with
  | 0 => none
  | n + 1 => match d with
  | .defDecl name ps ret db => do
    if name != decl.name then none else do
    if hp : paramEqAll decl.params (ps.map (fun p => Param.req p.1)) = true then do
      if ht : ps.all (fun p => FirstOrder p.2 && !isAliasTy p.2) = true then do
        if hr : FirstOrder ret = true then do
          let c ← check n ps decl.body db κ I cache
          if hret : c.ty = ret then do
            let ⟨hctx⟩ ← ctxEq? c.ctx κ
            if hspine : c.spine = I then
              some ⟨ps, ret, c.out, paramEqAll_sound hp,
                by simpa only [List.all_eq_true, Bool.and_eq_true, Bool.not_eq_true'] using ht,
                hr, by simpa only [hret, hctx, hspine] using c.judged⟩
            else none
          else none
        else none
      else none
    else none
  | _ => none

end

/-! ## §4 The entry point

`validate` in the sense the ladder means it: a program, a certificate, a `Bool`. The `Bool`
is `isSome` of a value whose type contains the derivation, so `true` *is* "there is a
`DJudge` derivation of this program", with no theorem in between.

Fuel: 200 is far beyond anything in the corpus (the deepest rung nests ~12 levels) and is not
a soundness parameter -- running out answers `false`. -/

def fuelD : Nat := 200

/-- The certified judgment, as a proposition about a program: it types at *some* type in the
empty environment. -/
def DTyped (p : Expr) : Prop := ∃ τ Γ' κ' I', DJudge [] p τ Γ' ctx0 .ivar0 κ' I'

/-- **The ladder's verdict.** `true` iff the certificate checks. -/
def validateD (p : Expr) (d : Deriv) : Bool := (check fuelD [] p d).isSome

/-- …and the verdict means what it says, by construction rather than by induction: this is
one `match`, because the `Certified` the checker returned carries the derivation. -/
theorem validateD_typed {p : Expr} {d : Deriv} (h : validateD p d = true) : DTyped p := by
  unfold validateD at h
  match hc : check fuelD [] p d with
  | some c => exact ⟨c.ty, c.out, c.ctx, c.spine, c.judged⟩
  | none => rw [hc] at h; exact absurd h (by simp)

/-! ## §5 Semantic status

`validateD p d = true` means the checker returned a `DJudge` derivation of `p`.
All eighteen expression rules and six list companions have answer-typed semantic proofs
registered in `Denote/Typed/Clink.lean`. The semantic target includes safety under a typed
continuation, so escapes and halts are covered as well as returned values.

`Denote/Typed/Bridge.lean` proves `validateD_safe_boot` for every accepted certificate.
`CorpusSafety.lean` additionally carries worked derivations exercising every registered rule;
`RuleAudit.lean` checks their proof terms, and `SemLadder.lean` cross-checks their programs.

`Ratchet/Judge.lean` is the retained type/context substrate. The older judgment and checker
were deleted in clink 68; the current proof boundary is the answer-typed registry. -/

end Ratchet
