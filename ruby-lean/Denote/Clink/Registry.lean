import Denote.Clink.ActiveProofs
import Denote.Clink.Registration
import Denote.Clink.Target

/-! Active certified clinks under the source-controlled rebuild profile. A disabled
clink is omitted before its proof is required; an enabled clink must still carry
its constructor-derived proof. The full safety bridge requires complete coverage. -/
set_option autoImplicit false
open Lean Meta Elab Command
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

build_dclink_target

/-- Every `DJudge` constructor with an answer-typed proof on file, registered; the rest
reported. Live in both directions, exactly as `registerAll` is. -/
elab "build_dclink_registry" : command => do
  let env ← getEnv
  let mut reg : List Name := []
  let mut unreg : List Name := []
  let mut gated : List Name := []
  let mut census : List Name := []
  for ind in dJudgmentInductives do
    let some (.inductInfo vi) := env.find? ind
      | throwError m!"{ind} is not an inductive"
    for c in vi.ctors do
      census := census ++ [c]
      if !clinkEnabled (toString (dRuleSuffix c)) then
        gated := gated ++ [c]
      else if (env.find? (dsemName c)).isSome then
        registerDClink c
        reg := reg ++ [c]
      else
        unreg := unreg ++ [c]
  let errors := clinkPolicyErrors (census.map (toString ∘ dRuleSuffix)) clinkProfile
  unless errors.isEmpty do
    throwError m!"build_dclink_registry: {errors}"
  unless unreg.isEmpty do
    throwError m!"build_dclink_registry: enabled clinks lack proofs: {unreg.map dRuleSuffix}"
  let listExpr : Lean.Expr :=
    reg.foldr
      (fun c acc =>
        mkApp3 (mkConst ``List.cons [levelZero]) (dclinkTy) (mkConst (dclinkName c)) acc)
      (mkApp (mkConst ``List.nil [levelZero]) (dclinkTy))
  liftCoreM <| addAndCompile (.defnDecl
    { name := `Ratchet.Denote.Typed.dclinks, levelParams := [],
      type := mkApp (mkConst ``List [levelZero]) (dclinkTy),
      value := listExpr, hints := .abbrev, safety := .safe })
  let mkStr (nm : Name) (xs : List Name) : CommandElabM Unit :=
    liftCoreM <| addAndCompile (.defnDecl
      { name := nm, levelParams := [], type := mkConst ``String,
        value := mkStrLit (String.intercalate " " (xs.map toString)),
        hints := .opaque, safety := .safe })
  mkStr `Ratchet.Denote.Typed.dclinkCensus (census.map dRuleSuffix)
  mkStr `Ratchet.Denote.Typed.dclinkGated (gated.map dRuleSuffix)
  mkStr `Ratchet.Denote.Typed.dclinkRegistered (reg.map dRuleSuffix)
  mkStr `Ratchet.Denote.Typed.dclinkUnregistered (unreg.map dRuleSuffix)
  -- Of the unregistered, the ones that need **DFam extended** before a proof would even be
  -- the right statement. Without this the owed column reads as three units of the same kind
  -- of work; two of them are not.
  let famBlocked := unreg.filter fun c =>
    match env.find? c with
    | some (.ctorInfo ci) => (dUncarriedJudgments.filter (ci.type.getUsedConstants.contains ·)) != []
    | _ => false
  mkStr `Ratchet.Denote.Typed.dclinkFamBlocked (famBlocked.map dRuleSuffix)
  -- Also report the companion families separately; all are already scanned above.
  let mut companions : List Name := []
  for ind in dJudgmentInductives.tail do
    if let some (.inductInfo vi) := env.find? ind then
      companions := companions ++ vi.ctors.map dRuleSuffix
  mkStr `Ratchet.Denote.Typed.dclinkCompanionRules companions

build_dclink_registry

/-! ## §3 The certified judgment and its soundness

Each family projection quantifies over closed interpretations. Soundness instantiates the
family at `dsemFam` and discharges closure from the clinks' own `sem` fields. -/

def DJudgeC (R : List (Clink dsynFam dsemFam)) : DFam where
  judge Γ e τ Γ' κ I κ' I' := ∀ F : DFam, Closed R F → F.judge Γ e τ Γ' κ I κ' I'
  all Γ es tys Γ' κ I κ' I' := ∀ F : DFam, Closed R F → F.all Γ es tys Γ' κ I κ' I'
  seq Γ es τ Γ' κ I κ' I' := ∀ F : DFam, Closed R F → F.seq Γ es τ Γ' κ I κ' I'
  pairs Γ ps ks vs Γ' κ I κ' I' := ∀ F : DFam, Closed R F → F.pairs Γ ps ks vs Γ' κ I κ' I'
  recBody κ I s Γ e τ Γ' := ∀ F : DFam, Closed R F → F.recBody κ I s Γ e τ Γ'
  recArgs κ I s Γ es tys Γ' := ∀ F : DFam, Closed R F → F.recArgs κ I s Γ es tys Γ'
  init κ Γ I e τ κ' Γ' I' := ∀ F : DFam, Closed R F → F.init κ Γ I e τ κ' Γ' I'
  initSeq κ Γ I es τ κ' Γ' I' := ∀ F : DFam, Closed R F → F.initSeq κ Γ I es τ κ' Γ' I'
  initAll κ Γ I es tys κ' Γ' I' := ∀ F : DFam, Closed R F → F.initAll κ Γ I es tys κ' Γ' I'
  flow κ Γ I facts e τ current κ' Γ' I' out :=
    ∀ F : DFam, Closed R F → F.flow κ Γ I facts e τ current κ' Γ' I' out
  flowSeq κ Γ I facts es τ current κ' Γ' I' out :=
    ∀ F : DFam, Closed R F → F.flowSeq κ Γ I facts es τ current κ' Γ' I' out
  flowAll κ Γ I facts es tys κ' Γ' I' out :=
    ∀ F : DFam, Closed R F → F.flowAll κ Γ I facts es tys κ' Γ' I' out
  method κ I fr ps ret Γ e τ Γ' := ∀ F : DFam, Closed R F → F.method κ I fr ps ret Γ e τ Γ'
  methodAll κ I fr ps ret Γ es tys Γ' := ∀ F : DFam, Closed R F → F.methodAll κ I fr ps ret Γ es tys Γ'
  methodSeq κ I fr ps ret Γ es τ Γ' := ∀ F : DFam, Closed R F → F.methodSeq κ I fr ps ret Γ es τ Γ'

  methodFlow κ I fr ps ret Γ facts e τ c Γ' out :=
    ∀ F : DFam, Closed R F → F.methodFlow κ I fr ps ret Γ facts e τ c Γ' out
  methodFlowSeq κ I fr ps ret Γ facts es τ c Γ' out :=
    ∀ F : DFam, Closed R F → F.methodFlowSeq κ I fr ps ret Γ facts es τ c Γ' out

/-- A derivation in the certified judgment, built the way `Denote/Clink/Spec.lean` §4
describes: you are *handed* the rules (`hF c hc`) and never mention closure. Premise-free,
so it is also the shortest one there is. -/
theorem djudgeC_intLit {κ : Ctx} {Γ : Env} {I : Ty} {n : Int} :
    (DJudgeC dclinks).judge Γ (.int n) .int Γ κ I :=
  fun _F hF => hF DClink.intLit (by unfold dclinks; exact List.Mem.head _)

/-- **The certified judgment is inhabited**, so §3's soundness theorems are about a nonempty
set of programs. `#guard dclinks.length > 0` in §4 only rules out an empty *registry*;
because `DJudgeC` is Church-encoded, a nonempty registry does not by itself produce a single
derivation, and an uninhabited judgment would make `dregistry_sound` and `dregistry_safe`
vacuously true. This is the witness that they are not.

Not to be confused with `Closed dclinks F` holding of an arbitrary `F` — that is **false**
(instantiate at the family where every judgment is `False`: `DJudge.intLit` has no premises,
so its form becomes `∀ κ Γ I n, False`). `Denote/Clink/Spec.lean` §2 says why there is no
generic closure lemma, and this is the concrete reason. -/
theorem closed_not_vacuous :
    ∃ (Γ Γ' : Env) (e : Ratchet.Expr) (τ : Ty), (DJudgeC dclinks).judge Γ e τ Γ' :=
  ⟨[], [], .int 0, .int, djudgeC_intLit⟩

/-- The registry's principal contract carries distinct incoming/outgoing state indices. -/
theorem dregistry_context {κ κ' : Ctx} {Γ Γ' : Env} {I I' : Ty} {e : Ratchet.Expr} {τ : Ty}
    (h : (DJudgeC dclinks).judge Γ e τ Γ' κ I κ' I') : SemSafeCtxA κ Γ I e τ κ' Γ' I' :=
  h dsemFam (closed_target dclinks)

/-- **Every derivation in the certified typed judgment is semantically true and safe.**
Unconditional at every registry size: the hypothesis is discharged from the clinks' own `sem`
fields, so this theorem was green when the registry had one rule in it and cannot stop being
green as it grows. -/
theorem dregistry_sound {Γ : Env} {e : Ratchet.Expr} {τ : Ty} {Γ' : Env}
    (h : (DJudgeC dclinks).judge Γ e τ Γ') : SemSafeA Γ e τ Γ' :=
  semSafeA_iff_context.mpr (dregistry_context h)

/-- …and it lands on `closed_not_vacuous`'s witness, which is what makes the pair of them
more than a tautology. -/
example : SemSafeA [] (.int 0) .int [] := dregistry_sound djudgeC_intLit

/-- The answer-typed half: for every run that reaches an answer, the value is in the type or
the escape is not type-stuck. -/
theorem dregistry_semJudge {Γ : Env} {e : Ratchet.Expr} {τ : Ty} {Γ' : Env}
    (h : (DJudgeC dclinks).judge Γ e τ Γ') : SemJudgeA Γ e τ Γ' := (dregistry_sound h).1

/-- **The invariant half**, as the clinks state it: a machine evaluating a certified
expression under a continuation that accepts its type is safe. Quantified over the
continuation and the answer type, which is what makes it usable at a machine part-way through
a larger program. -/
theorem dregistry_safeUnder {Γ : Env} {e : Ratchet.Expr} {τ : Ty} {Γ' : Env}
    (h : (DJudgeC dclinks).judge Γ e τ Γ') : SafeUnder Γ e τ Γ' := (dregistry_sound h).2

/-- **Safety of every program the fragment types**, which is the theorem the ladder exists to
produce: from any conformant machine, a certified program never reaches a type-stuck outcome —
at any fuel, whether it returns, escapes, diverges or gates.

This closes the context-indexed run contract. At top level it also follows from
`dregistry_safeUnder` at the empty continuation. `Denote/Safety.lean` lands it on the
corpus's own rungs at the real prelude-booted machine. -/
theorem dregistry_safe {κ κ' : Ctx} {I I' : Ty} {Γ : Env} {e : Ratchet.Expr} {τ : Ty} {Γ' : Env}
    (h : (DJudgeC dclinks).judge Γ e τ Γ' κ I κ' I')
    {m : Machine} (hm : StateOk κ Γ I m) : StuckFree m e := (dregistry_context h).closed hm

/-- …and it is a `DJudge` derivation, so `Ratchet/Check/Check.lean`'s checker and this judgment are
about the same rules. -/
theorem dregistry_syn {κ κ' : Ctx} {I I' : Ty} {Γ : Env} {e : Ratchet.Expr} {τ : Ty} {Γ' : Env}
    (h : (DJudgeC dclinks).judge Γ e τ Γ' κ I κ' I') : DJudge Γ e τ Γ' κ I κ' I' :=
  h dsynFam (closed_source dclinks)

/-! ## §3a The invariant, as a predicate on machines

`SafeUnder` is the invariant *per expression*, which is the shape a clink field has to have.
This is the same content as a predicate on **machines** — the object
`Denote/Sem/Core/Invariant.lean` is written against, and the one a reader looking for "the
inductive invariant" expects to find.

Two arms today, one per `Ctl` the fragment can be in. There is no `jump` arm because no
registered rule produces a jump: `DJudge` has no `ret`, `throw`, `brk` or `next`. It gains one
with the first rule that does, and that arm is where §F27's `retJ`/`throwJ` class-table
question comes due. -/

def DInv (τa : Ty) (m : Machine) : Prop :=
  (∃ (Γ Γ' : Env) (e : Ratchet.Expr) (τ : Ty),
      m.ctl = .eval (toRuby e) ∧ StateOk Ratchet.ctx0 Γ .ivar0 m ∧
      (DJudgeC dclinks).judge Γ e τ Γ' ∧ DKontOk τa m.kont Γ' τ) ∨
  (∃ (Γ : Env) (τ : Ty) (v : Value),
      m.ctl = .value v ∧ StateOk Ratchet.ctx0 Γ .ivar0 m ∧ denM τ m v ∧
      DKontOk τa m.kont Γ τ)

/-- **An `Inv` machine is safe.** The eval arm is the registry's own obligation
(`dregistry_safeUnder`); the value arm is the invariant's value clause, one case per frame. -/
theorem dInv_safe {τa : Ty} {m : Machine} (h : DInv τa m) : SafeA m := by
  rcases h with ⟨Γ, Γ', e, τ, hc, hm, hj, hk⟩ | ⟨Γ, τ, v, hc, hm, hd, hk⟩
  · exact dregistry_safeUnder hj τa m hm hc hk
  · exact safeA_value_kontOk hk hc rfl hm hd

/-- **A certified program starts at an `Inv` machine.** `InvInit`'s content, with
`DKontOk.nil` supplying the continuation half — and the answer type pinned to the program's
own, which is the index that makes the value clause recoverable. -/
theorem dInv_init {Γ Γ' : Env} {p : Ratchet.Expr} {τ : Ty}
    (hj : (DJudgeC dclinks).judge Γ p τ Γ') {m : Machine}
    (hm : StateOk Ratchet.ctx0 Γ .ivar0 m) : DInv τ (evalFrom m p) :=
  Or.inl ⟨Γ, Γ', p, τ, rfl, StateOk_reCtl hm _ _, hj, DKontOk.nil⟩

/-- **Safety, through the invariant.** The same theorem as `dregistry_safe`, factored the way
`Denote/Sem/Core/Invariant.lean` factors it: a certified program starts `Inv`, and `Inv` machines
are safe.

`example` rather than a second theorem, because it is `dregistry_safe` with the steps named
(Norm B — one statement, not two). What it is *for* is the shape: when a jump arm and more
frames arrive, this is the composition that does not change. -/
example {Γ Γ' : Env} {p : Ratchet.Expr} {τ : Ty}
    (hj : (DJudgeC dclinks).judge Γ p τ Γ') {m : Machine}
    (hm : StateOk Ratchet.ctx0 Γ .ivar0 m) : StuckFree m p :=
  dInv_safe (dInv_init hj hm)

/-! ### What is **not** proved about `DInv`, and why it is not needed

`preserved` — *an `Inv` machine steps to an `Inv` machine* — is the obligation
`Denote/Sem/Core/Invariant.lean`'s `safety_of_invariant` consumes, and it is **not proved here**.
It cannot be, by the route that file anticipates: the eval arm carries a `DJudgeC` derivation,
`DJudgeC` is Church-encoded, and proving that the *successor* is judged would need to take
that derivation apart. There is no `cases` on a Π-type. (`Denote/Proto/Safety.lean` did
exactly this by `cases` on an inductive `PJudge`, before both were deleted.)

`dInv_safe` does not need it, and the reason is the design rather than luck: the eval arm's
obligation is `SafeUnder`, which already speaks about the **whole future** of the machine, not
about one step. The induction that `preserved` + `safety_of_invariant` would perform over the
run has already been performed — once per rule, at registration, by choosing the family to be
the invariant. `preserved` would be a second, redundant pass over the same ground.

What is genuinely lost: `safety_of_invariant`'s reduction is stated for an abstract `Inv` and
proved once, so a *different* judgment could reuse it. This one cannot, and that is the price
of generating the judgment from the registry. It is recorded rather than papered over. -/

/-! ## §4 The report and the gate -/

def dGatedRules : List String :=
  if dclinkGated.isEmpty then [] else dclinkGated.splitOn " "

def dAllRules : List String :=
  if dclinkCensus.isEmpty then [] else dclinkCensus.splitOn " "

def dRegisteredRules : List String :=
  if dclinkRegistered.isEmpty then [] else dclinkRegistered.splitOn " "

def dUnregisteredRules : List String :=
  if dclinkUnregistered.isEmpty then [] else dclinkUnregistered.splitOn " "

/-- Unregistered rules that need **`DFam` extended** before a proof would even be the right
statement: their premises reach a list companion the family does not carry, so `ruleForm`
would hand them a raw-inductive premise and `registerDClink` refuses them. Strictly harder
than the rules that merely lack a proof. -/
def dFamBlockedRules : List String :=
  if dclinkFamBlocked.isEmpty then [] else dclinkFamBlocked.splitOn " "

/-- Constructors of all companion families, also included in the registered rule count. -/
def dCompanionRules : List String :=
  if dclinkCompanionRules.isEmpty then [] else dclinkCompanionRules.splitOn " "

-- Non-empty, so `dregistry_sound` is not vacuously about nothing.
#guard dclinks.length > 0

-- The registry and its report agree about its size.
#guard dclinks.length == dRegisteredRules.length

-- Keep the complete authoring census frozen; disabled rules are visible, not lost.
#guard dAllRules.length == 99
#guard dRegisteredRules.length + dGatedRules.length == dAllRules.length
#guard dRegisteredRules.all clinkEnabled
#guard dGatedRules.all (!clinkEnabled ·)
#guard dUnregisteredRules == []

-- Every judgment premise is represented in the semantic family.
#guard dFamBlockedRules == []

-- The companions, frozen. Another constructor here is a new obligation that would otherwise
-- arrive unannounced, because nothing else in the ladder counts these.
#guard dCompanionRules == ["DJudgeAll.nil", "DJudgeAll.cons", "DJudgeSeq.last", "DJudgeSeq.cons",
  "DJudgePairs.nil", "DJudgePairs.cons", "DJudgeRec.embed", "DJudgeRec.prim", "DJudgeRec.if'",
  "DJudgeRec.selfCall", "DJudgeRecAll.nil", "DJudgeRecAll.cons",
  "InitJudge.intLit", "InitJudge.var", "InitJudge.ivarAsgn", "InitJudge.seq", "InitJudge.ignoreResult",
  "InitJudge.superInit", "InitJudgeSeq.last", "InitJudgeSeq.cons", "InitJudgeAll.nil", "InitJudgeAll.cons",
  "DFlow.embed", "DFlow.intLit", "DFlow.nilLit", "DFlow.var", "DFlow.closureLiteral", "DFlow.vasgn",
  "DFlow.sequence", "DFlow.call", "DFlow.requiredCall", "DFlow.each", "DFlow.map", "DFlow.callBlock", "DFlow.callBoundBlock", "DFlowSeq.last", "DFlowSeq.cons",
  "DFlowAll.nil", "DFlowAll.cons", "DMethod.ordinary", "DMethod.vasgn", "DMethod.sequence",
  "DMethod.prim", "DMethod.yieldOne", "DMethodAll.nil", "DMethodAll.cons", "DMethodSeq.last", "DMethodSeq.cons",
  "DMethodFlow.embed", "DMethodFlow.intLit", "DMethodFlow.nilLit", "DMethodFlow.var", "DMethodFlow.vasgn", "DMethodFlow.sequence", "DMethodFlow.call", "DMethodFlowSeq.last", "DMethodFlowSeq.cons"]

-- Every family-blocked rule is unregistered, which `registerDClink` enforces and this states.
#guard dFamBlockedRules.all (fun r => dUnregisteredRules.contains r)

#print axioms closed_not_vacuous
#print axioms dregistry_sound
#print axioms dregistry_context
#print axioms dInv_safe
#print axioms dInv_init
#print axioms dregistry_syn

end Ratchet.Denote.Typed
