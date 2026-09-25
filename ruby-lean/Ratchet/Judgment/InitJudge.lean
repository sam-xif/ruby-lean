import Ratchet.Guards.WriteTypes
import Ratchet.Guards.SuperInit
import Ratchet.Guards.Args

/-! Scoped initializer derivations: the fresh receiver's field shape may change. This is
distinct from ordinary preservation; the registry carries all three initializer families.
No class, annotation, arity, or field name is fixed by these rules. -/
set_option autoImplicit false
namespace Ratchet

mutual
inductive InitJudge : Ctx → Env → Ty → Expr → Ty → Ctx → Env → Ty → Prop
  /-- Sorbet 0.6.13405 accepts the Integer literal in 067's initialize/super(3). -/
  | intLit {κ : Ctx} {Γ : Env} {I : Ty} {n : Int} :
      InitJudge κ Γ I (.int n) .int κ Γ I
  | var {κ : Ctx} {Γ : Env} {I τ : Ty} {x : String} :
      envGet? Γ x = some τ → isAliasTy τ = false →
      InitJudge κ Γ I (.var .lvar x) τ κ Γ I
  | ivarAsgn {κ κ' : Ctx} {Γ Γ' : Env} {I I' τ : Ty} {x : String} {e : Expr} :
      InitJudge κ Γ I e τ κ' Γ' I' → writeTypesB κ' Γ' I' x τ = true →
      InitJudge κ Γ I (.vasgn .ivar x e) τ κ' Γ' (ivarSet I' x τ)
  | seq {κ κ' : Ctx} {Γ Γ' : Env} {I I' τ : Ty} {es : List Expr} :
      InitJudgeSeq κ Γ I es τ κ' Γ' I' → InitJudge κ Γ I (.seq es) τ κ' Γ' I'
  /-- Forget only the value type (void/untyped return), never the body or its effects. -/
  | ignoreResult {κ κ' : Ctx} {Γ Γ' : Env} {I I' τ : Ty} {e : Expr} :
      InitJudge κ Γ I e τ κ' Γ' I' → InitJudge κ Γ I e .any κ' Γ' I'
  /-- Sorbet 0.6.13405 accepts 067's explicit super(3), rejecting super("three") and
  super() against Shape#initialize(Integer). Check the full parent annotation domain,
  in the actual receiver/parent-owner context, and retain its output fields. -/
  | superInit {κ : Ctx} {Γ Γa Γb : Env} {I Ia Ib τ : Ty} {es : List Expr}
      {c : Cls} {current owner : String} {d : Defn} {ps : List (String × Ty)} :
      InitJudgeAll κ Γ I es (ps.map (·.2)) κ Γa Ia →
      InitJudge (initializerBodyCtxAt κ c.name owner) ps Ia d.body τ
        (initializerBodyCtxAt κ c.name owner) Γb Ib →
      c ∈ κ.classes → SuperRoute κ.classes c.name current owner d →
      superInitB κ Γa Ia Ib c current d ps τ = true →
      InitJudge κ Γ I (.super' es none) τ κ Γa Ib

inductive InitJudgeSeq : Ctx → Env → Ty → List Expr → Ty → Ctx → Env → Ty → Prop
  | last {κ κ' : Ctx} {Γ Γ' : Env} {I I' τ : Ty} {e : Expr} :
      InitJudge κ Γ I e τ κ' Γ' I' → InitJudgeSeq κ Γ I [e] τ κ' Γ' I'
  | cons {κ κ₁ κ₂ : Ctx} {Γ Γ₁ Γ₂ : Env} {I I₁ I₂ σ τ : Ty}
      {e e' : Expr} {es : List Expr} :
      InitJudge κ Γ I e σ κ₁ Γ₁ I₁ → InitJudgeSeq κ₁ Γ₁ I₁ (e' :: es) τ κ₂ Γ₂ I₂ →
      InitJudgeSeq κ Γ I (e :: e' :: es) τ κ₂ Γ₂ I₂

/-- Required positional super arguments follow Sorbet's arity and annotated-type checks.
Earlier values use IvarStable types so later initializer writes preserve their denotations. -/
inductive InitJudgeAll : Ctx → Env → Ty → List Expr → List Ty → Ctx → Env → Ty → Prop
  | nil {κ : Ctx} {Γ : Env} {I : Ty} : InitJudgeAll κ Γ I [] [] κ Γ I
  | cons {κ κ₁ κ₂ : Ctx} {Γ Γ₁ Γ₂ : Env} {I I₁ I₂ σ : Ty}
      {e : Expr} {es : List Expr} {tys : List Ty} :
      InitJudge κ Γ I e σ κ₁ Γ₁ I₁ → InitJudgeAll κ₁ Γ₁ I₁ es tys κ₂ Γ₂ I₂ →
      plainArgB e = true → IvarStable σ = true →
      InitJudgeAll κ Γ I (e :: es) (σ :: tys) κ₂ Γ₂ I₂
end

end Ratchet
