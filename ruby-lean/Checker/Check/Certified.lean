import Checker.Check.SingletonCache

set_option autoImplicit false
namespace Checker

/-- A checked answer: the type and every outgoing state index, with their derivation.
No outgoing declaration table is reconstructed separately from the expression proof. -/
structure Certified (Γ : Env) (e : Expr) (κ : Ctx := ctx0) (I : Ty := .ivar0) where
  ty : Ty
  out : Env
  ctx : Ctx
  spine : Ty
  judged : DJudge Γ e ty out κ I ctx spine
  cache : CheckedCache := {}

/-- Only a proved same-class instance-to-nominal conversion supplements exact returns.
No field information is invented from a nominal annotation. -/
def checkResult {Γ : Env} {e : Expr} {κ : Ctx} {I : Ty}
    (c : Certified Γ e κ I) (ret : Ty) : Option (Certified Γ e κ I) := do
  if c.ty == ret then some c else
  match ht : c.ty, ret with
  | .inst cn fields, .cls name => do
    if cn != name then none else do
    let f ← findClass cn c.ctx.classes
    some ⟨.cls cn, c.out, c.ctx, c.spine, by
      simpa only [f.nameOk] using
        (DJudge.instanceType (c := f.cls) (fields := fields)
          (by simpa only [ht, f.nameOk] using c.judged) f.member), c.cache⟩
  | _, _ => none

structure CertifiedAll (Γ : Env) (es : List Expr) (κ : Ctx := ctx0) (I : Ty := .ivar0) where
  tys : List Ty
  out : Env
  ctx : Ctx
  spine : Ty
  judged : DJudgeAll Γ es tys out κ I ctx spine
  cache : CheckedCache := {}

structure CertifiedSeq (Γ : Env) (es : List Expr) (κ : Ctx := ctx0) (I : Ty := .ivar0) where
  ty : Ty
  out : Env
  ctx : Ctx
  spine : Ty
  judged : DJudgeSeq Γ es ty out κ I ctx spine
  cache : CheckedCache := {}

structure CertifiedPairs (Γ : Env) (ps : List (Expr × Expr)) (κ : Ctx := ctx0) (I : Ty := .ivar0) where
  keys : List Ty
  vals : List Ty
  out : Env
  ctx : Ctx
  spine : Ty
  judged : DJudgePairs Γ ps keys vals out κ I ctx spine
  cache : CheckedCache := {}

structure CertifiedRec (κ : Ctx) (I : Ty) (s : RecScope) (Γ : Env) (e : Expr) where
  ty : Ty
  out : Env
  judged : DJudgeRec κ I s Γ e ty out

structure CertifiedRecAll (κ : Ctx) (I : Ty) (s : RecScope) (Γ : Env) (es : List Expr) where
  tys : List Ty
  out : Env
  judged : DJudgeRecAll κ I s Γ es tys out


end Checker
