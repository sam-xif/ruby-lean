-- Generated from Checker/Check/Certified.lean by scripts/generate_audited_checker.py.
-- Edit the raw source and regenerate; Lean checks the indexed proof and trace.
import Books.TypeSoundness.Checker.Audit.Erase
import Books.TypeSoundness.Checker.Audit.SingletonCache

set_option autoImplicit false
namespace Checker.Audit
open Checker

/-- A checked answer: the type and every outgoing state index, with their derivation.
No outgoing declaration table is reconstructed separately from the expression proof. -/
structure Certified (Γ : Env) (e : Expr) (κ : Ctx := ctx0) (I : Ty := .ivar0) where
  ty : Ty
  out : Env
  ctx : Ctx
  spine : Ty
  {rulesUsed : List String}
  judged : DJudge (used := rulesUsed) Γ e ty out κ I ctx spine
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
  {rulesUsed : List String}
  judged : DJudgeAll (used := rulesUsed) Γ es tys out κ I ctx spine
  cache : CheckedCache := {}

structure CertifiedSeq (Γ : Env) (es : List Expr) (κ : Ctx := ctx0) (I : Ty := .ivar0) where
  ty : Ty
  out : Env
  ctx : Ctx
  spine : Ty
  {rulesUsed : List String}
  judged : DJudgeSeq (used := rulesUsed) Γ es ty out κ I ctx spine
  cache : CheckedCache := {}

structure CertifiedPairs (Γ : Env) (ps : List (Expr × Expr)) (κ : Ctx := ctx0) (I : Ty := .ivar0) where
  keys : List Ty
  vals : List Ty
  out : Env
  ctx : Ctx
  spine : Ty
  {rulesUsed : List String}
  judged : DJudgePairs (used := rulesUsed) Γ ps keys vals out κ I ctx spine
  cache : CheckedCache := {}

structure CertifiedRec (κ : Ctx) (I : Ty) (s : RecScope) (Γ : Env) (e : Expr) where
  ty : Ty
  out : Env
  {rulesUsed : List String}
  judged : DJudgeRec (used := rulesUsed) κ I s Γ e ty out

structure CertifiedRecAll (κ : Ctx) (I : Ty) (s : RecScope) (Γ : Env) (es : List Expr) where
  tys : List Ty
  out : Env
  {rulesUsed : List String}
  judged : DJudgeRecAll (used := rulesUsed) κ I s Γ es tys out


end Checker.Audit
