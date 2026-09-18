import Ratchet.Check.Deriv
import Ratchet.Static.CtxEq
import Ratchet.Guards.MethodCtx
import Ratchet.Judgment.InitJudge
import Ratchet.Guards.ClassGuards
import Ratchet.Guards.SubclassRule
import Ratchet.Guards.MemberRoute
import Ratchet.Static.NativeInstanceNames

/-!
# `Ratchet/Judgment/DJudge.lean` — the answer-typed judgment

The syntax/type substrate is independent of `Denote/`. `Deriv` holds untrusted hints;
`Check.lean` returns a `DJudge` proof after checking those hints against the program.
This file owns sixteen primitive rows and six mutual judgment families. Scoped recursive
bodies reuse ordinary proofs for closed subtrees; their self-call hypothesis is discharged
by the semantic `recursive` rule, never installed as an unchecked body.

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

Each row is proved against the executable semantics in `Denote/Rules/Primitive/PrimitiveBuiltin.lean`,
under the heap conformance facts in `Denote/Sem/Heap/PrimHeap.lean`. -/

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
environment, and both are `Ratchet/Lang/Ty.lean`'s functions rather than anything new here:

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

/-- A recursive body's annotation scope, not an installed callable assumption. -/
structure RecScope where
  decl : Defn
  params : Env
  ret : Ty

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
      precision one (`Ratchet/Lang/Ty.lean`'s `joinEnv`: carrying the pre-`if` environment forward
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

  /-- Close a scoped body derivation; the semantic rule discharges its guarded hypothesis. -/
  | recursive {κ : Ctx} {I : Ty} {s : RecScope} {Γb : Env} :
      plainArgB s.decl.body = true →
      DJudgeRec κ I s s.params s.decl.body s.ret Γb →
      DJudge s.params s.decl.body s.ret Γb κ I κ I

  | ivarRead {κ : Ctx} {Γ : Env} {I : Ty} {x : String} :
      DJudge Γ (.var .ivar x) (κ.ivarReadTy I x) Γ κ I
  | constClass {κ : Ctx} {Γ : Env} {I : Ty} {c : Cls} :
      c ∈ κ.classes → DJudge Γ (.const c.name) (.clsOf c.name) Γ κ I
  | classDecl {κ κb : Ctx} {Γ Γb : Env} {I Ib τ : Ty} {name : String} {body : Expr} :
      DJudge [] body τ Γb (classHeaderCtx (classBodyCtx κ name) name) .ivar0 κb Ib →
      classRuleB κ κb Γ I τ name = true →
      DJudge Γ (.class' name none body) τ Γ κ I (returnScopeCtx κ κb) I
  /-- Every member body is checked at its parameter/return annotations, even if uncalled. -/
  | memberDef {κ : Ctx} {Γ Γb : Env} {I Ib τ : Ty} {c : Cls} {d : Defn} {ps : List SigParam} :
      d.params = ps.map (fun p => Param.req p.1) →
      (∀ p ∈ ps, FirstOrder p.2 = true ∧ isAliasTy p.2 = false) →
      FirstOrder τ = true → FirstOrder Ib = true →
      DJudge ps d.body τ Γb (instanceBodyCtx (instanceDeclCtx κ c d) ⟨c.name, c.name, d.name⟩ Ib) Ib
        (instanceBodyCtx (instanceDeclCtx κ c d) ⟨c.name, c.name, d.name⟩ Ib) Ib →
      d.name ≠ "initialize" → c ∈ κ.classes → memberRuleB κ Γ I c d = true →
      DJudge Γ (.def' d.name d.params d.body) .sym Γ κ I (instanceDeclCtx κ c d) I
  | initDef {κ : Ctx} {Γ Γb : Env} {I Ib τ : Ty} {c : Cls} {d : Defn} {ps : List SigParam} :
      d.name = "initialize" → d.params = ps.map (fun p => Param.req p.1) →
      (∀ p ∈ ps, FirstOrder p.2 = true ∧ isAliasTy p.2 = false) →
      FirstOrder τ = true → FirstOrder Ib = true →
      InitJudge (initializerBodyCtx (instanceDeclCtx κ c d) c.name) ps .ivar0 d.body τ
        (initializerBodyCtx (instanceDeclCtx κ c d) c.name) Γb Ib →
      c ∈ κ.classes → memberRuleB κ Γ I c d = true →
      DJudge Γ (.def' d.name d.params d.body) .sym Γ κ I (instanceDeclCtx κ c d) I
  | newInst {κ κ₁ κ₂ : Ctx} {Γ Γ₁ Γ₂ Γb : Env} {I I₁ I₂ Ib τ : Ty}
      {c : Cls} {d : Defn} {ps : List SigParam} {recv : Expr} {args : List Expr} :
      DJudge Γ recv (.clsOf c.name) Γ₁ κ I κ₁ I₁ →
      DJudgeAll Γ₁ args (ps.map (·.2)) Γ₂ κ₁ I₁ κ₂ I₂ →
      explicitReceiverB recv = true → c ∈ κ₂.classes → d ∈ c.methods → d.name = "initialize" →
      smroGet? κ₂.classes c.name "new" = none → c.name ∈ κ₂.pos.plainAlloc →
      d.params = ps.map (fun p => Param.req p.1) →
      (∀ p ∈ ps, FirstOrder p.2 = true ∧ isAliasTy p.2 = false) →
      FirstOrder τ = true → FirstOrder Ib = true →
      InitJudge (initializerBodyCtx κ₂ c.name) ps .ivar0 d.body τ (initializerBodyCtx κ₂ c.name) Γb Ib →
      mainCallB κ₂ Γ₂ I₂ = true →
      DJudge Γ (.send (some recv) "new" args none) (.inst c.name Ib) Γ₂ κ I κ₂ I₂
  | callMethodSig {κ κ₁ κ₂ : Ctx} {Γ Γ₁ Γ₂ Γb : Env} {I I₁ I₂ Ib τ : Ty}
      {c : Cls} {d : Defn} {ps : List SigParam} {recv : Expr} {args : List Expr} :
      DJudge Γ recv (.inst c.name Ib) Γ₁ κ I κ₁ I₁ →
      DJudgeAll Γ₁ args (ps.map (·.2)) Γ₂ κ₁ I₁ κ₂ I₂ →
      explicitReceiverB recv = true → c ∈ κ₂.classes → d ∈ c.methods → d.name ≠ "initialize" →
      directCallNameB d.name = true → d.params = ps.map (fun p => Param.req p.1) →
      (∀ p ∈ ps, FirstOrder p.2 = true ∧ isAliasTy p.2 = false) →
      FirstOrder τ = true → FirstOrder Ib = true →
      DJudge ps d.body τ Γb (instanceBodyCtx κ₂ ⟨c.name, c.name, d.name⟩ Ib) Ib
        (instanceBodyCtx κ₂ ⟨c.name, c.name, d.name⟩ Ib) Ib →
      instanceCallB κ₂ Γ₂ I₂ = true → DJudge Γ (.send (some recv) d.name args none) τ Γ₂ κ I κ₂ I₂
  | vcallMethodSig {κ : Ctx} {Γ Γb : Env} {I Ib τ : Ty} {c : Cls} {d : Defn} :
      κ.selfTy = some (.inst c.name Ib) → c ∈ κ.classes → d ∈ c.methods →
      d.name ≠ "initialize" → directCallNameB d.name = true → d.params = [] →
      FirstOrder τ = true → FirstOrder Ib = true →
      DJudge [] d.body τ Γb (instanceBodyCtx κ ⟨c.name, c.name, d.name⟩ Ib) Ib
        (instanceBodyCtx κ ⟨c.name, c.name, d.name⟩ Ib) Ib →
      instanceCallB κ Γ I = true → DJudge Γ (.vcall d.name) τ Γ κ I

  | subclassDecl {κ κ₁ κb : Ctx} {Γ Γ₁ Γb : Env} {I I₁ Ib τ : Ty}
      {c : Cls} {name : String} {super body : Expr} :
      DJudge Γ super (.clsOf c.name) Γ₁ κ I κ₁ I₁ → c ∈ κ₁.classes →
      DJudge [] body τ Γb (subclassHeaderCtx (classBodyCtx κ₁ name) name c.name) .ivar0 κb Ib →
      subclassRuleB κ₁ κb Γ₁ I₁ τ name c.name = true →
      DJudge Γ (.class' name (some super) body) τ Γ₁ κ I (returnScopeCtx κ₁ κb) I₁
  | newInherited {κ κ₁ κ₂ : Ctx} {Γ Γ₁ Γ₂ Γb : Env} {I I₁ I₂ Ib τ : Ty}
      {c : Cls} {owner : String} {d : Defn} {ps : List SigParam} {recv : Expr} {args : List Expr} :
      DJudge Γ recv (.clsOf c.name) Γ₁ κ I κ₁ I₁ →
      DJudgeAll Γ₁ args (ps.map (·.2)) Γ₂ κ₁ I₁ κ₂ I₂ →
      explicitReceiverB recv = true → c ∈ κ₂.classes → MemberRoute κ₂.classes c.name owner d →
      d.name = "initialize" → smroGet? κ₂.classes c.name "new" = none → c.name ∈ κ₂.pos.plainAlloc →
      d.params = ps.map (fun p => Param.req p.1) →
      (∀ p ∈ ps, FirstOrder p.2 = true ∧ isAliasTy p.2 = false) →
      FirstOrder τ = true → FirstOrder Ib = true →
      InitJudge (initializerBodyCtxAt κ₂ c.name owner) ps .ivar0 d.body τ
        (initializerBodyCtxAt κ₂ c.name owner) Γb Ib → mainCallB κ₂ Γ₂ I₂ = true →
      DJudge Γ (.send (some recv) "new" args none) (.inst c.name Ib) Γ₂ κ I κ₂ I₂
  | callInherited {κ κ₁ κ₂ : Ctx} {Γ Γ₁ Γ₂ Γb : Env} {I I₁ I₂ Ib τ : Ty}
      {c : Cls} {owner : String} {d : Defn} {ps : List SigParam} {recv : Expr} {args : List Expr} :
      DJudge Γ recv (.inst c.name Ib) Γ₁ κ I κ₁ I₁ →
      DJudgeAll Γ₁ args (ps.map (·.2)) Γ₂ κ₁ I₁ κ₂ I₂ →
      explicitReceiverB recv = true → c ∈ κ₂.classes → MemberRoute κ₂.classes c.name owner d →
      d.name ≠ "initialize" → directCallNameB d.name = true → nativeInstanceFreeB d.name = true →
      d.params = ps.map (fun p => Param.req p.1) →
      (∀ p ∈ ps, FirstOrder p.2 = true ∧ isAliasTy p.2 = false) →
      FirstOrder τ = true → FirstOrder Ib = true →
      DJudge ps d.body τ Γb (instanceBodyCtx κ₂ ⟨c.name, owner, d.name⟩ Ib) Ib
        (instanceBodyCtx κ₂ ⟨c.name, owner, d.name⟩ Ib) Ib → instanceCallB κ₂ Γ₂ I₂ = true →
      DJudge Γ (.send (some recv) d.name args none) τ Γ₂ κ I κ₂ I₂

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

/-- Closed subexpressions reuse the ordinary judgment. Only nodes around a scoped
recursive call need their own composition; no uncalled body can bypass these rules. -/
inductive DJudgeRec : Ctx → Ty → RecScope → Env → Expr → Ty → Env → Prop
  | embed {κ : Ctx} {I : Ty} {s : RecScope} {Γ Γ' : Env} {e : Expr} {τ : Ty} :
      DJudge Γ e τ Γ' κ I κ I → DJudgeRec κ I s Γ e τ Γ'
  | prim {κ : Ctx} {I : Ty} {s : RecScope} {Γ Γ₁ Γ₂ : Env}
      {recv : Expr} {name : String} {args : List Expr} {σ τ : Ty} {tys : List Ty} :
      DJudgeRec κ I s Γ recv σ Γ₁ → DJudgeRecAll κ I s Γ₁ args tys Γ₂ →
      DPrim σ name tys τ → nameFreeN κ name = true →
      (σ = .cls "String" → isANoOk κ.wholeCls (["String", "Comparable"] ++ rootAncestors) = true) →
      DJudgeRec κ I s Γ (.send (some recv) name args none) τ Γ₂
  | if' {κ : Ctx} {I : Ty} {s : RecScope} {Γ Γc Γ₁ Γ₂ : Env}
      {c t e : Expr} {σ τ₁ τ₂ : Ty} :
      DJudgeRec κ I s Γ c σ Γc → DJudgeRec κ I s Γc t τ₁ Γ₁ →
      DJudgeRec κ I s Γc e τ₂ Γ₂ →
      DJudgeRec κ I s Γ (.if' c t (some e)) (joinT τ₁ τ₂) (joinEnv Γ₁ Γ₂)
  | selfCall {κ : Ctx} {I : Ty} {s : RecScope} {Γ Γ' : Env} {args : List Expr} :
      DJudgeRecAll κ I s Γ args (s.params.map (·.2)) Γ' →
      s.decl.params = s.params.map (fun p => Param.req p.1) →
      (∀ p ∈ s.params, FirstOrder p.2 = true ∧ isAliasTy p.2 = false) →
      FirstOrder s.ret = true → s.decl ∈ κ.defs →
      κ.withFrame (some ⟨"Object", "Object", s.decl.name⟩) = κ →
      κ.scope.runtimeMain = true → κ.selfTy = none → κ.blockTy = none →
      κ.consts = [] → κ.asms = [] → FirstOrder I = true →
      (∀ p ∈ Γ', FirstOrder (stripAlias p.2) = true) →
      DJudgeRec κ I s Γ (.send none s.decl.name args none) s.ret Γ'

inductive DJudgeRecAll : Ctx → Ty → RecScope → Env → List Expr → List Ty → Env → Prop
  | nil {κ : Ctx} {I : Ty} {s : RecScope} {Γ : Env} : DJudgeRecAll κ I s Γ [] [] Γ
  | cons {κ : Ctx} {I : Ty} {s : RecScope} {Γ Γ₁ Γ₂ : Env}
      {e : Expr} {es : List Expr} {τ : Ty} {tys : List Ty} :
      DJudgeRec κ I s Γ e τ Γ₁ → DJudgeRecAll κ I s Γ₁ es tys Γ₂ → plainArgB e = true →
      DJudgeRecAll κ I s Γ (e :: es) (τ :: tys) Γ₂
end

theorem DJudge.plainArg {κ κ' : Ctx} {I I' : Ty} {Γ Γ' : Env} {e : Expr} {τ : Ty}
    (h : DJudge Γ e τ Γ' κ I κ' I') :
    plainArgB e = true := by cases h <;> first | rfl | assumption

end Ratchet
