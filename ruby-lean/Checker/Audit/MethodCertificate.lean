-- Generated from Checker/Check/MethodCertificate.lean by scripts/generate_audited_checker.py.
-- Edit the raw source and regenerate; Lean checks the indexed proof and trace.
import Checker.Audit.Erase
import Checker.Judgment.DMethod

/-! Certificates for the callback-capable body checker. An optional ordinary
proof permits reuse of existing expression rules, but only when every child has one. -/
set_option autoImplicit false
namespace Checker.Audit
open Checker

structure CertifiedMethod (κ : Ctx) (I : Ty) (fr : Frame) (ps : List Ty) (ret : Ty) (Γ : Env) (e : Expr) where
  ty : Ty
  out : Env
  {rulesUsed : List String}
  judged : DMethod (used := rulesUsed) κ I fr ps ret Γ e ty out
  ordinary : Option (TraceLift (fun used => ∀ code, DJudge (used := used) Γ e ty out (callbackMethodCtx κ fr code) I)) := none

def CertifiedMethod.ofOrdinary {used : List String} {κ : Ctx} {I : Ty} {fr : Frame} {ps : List Ty} {ret τ : Ty}
    {Γ Γ' : Env} {e : Expr}
    (h : ∀ code, DJudge (used := used) Γ e τ Γ' (callbackMethodCtx κ fr code) I) :
    CertifiedMethod κ I fr ps ret Γ e := ⟨τ, Γ', .ordinary h, some ⟨h⟩⟩

structure CertifiedMethodAll (κ : Ctx) (I : Ty) (fr : Frame) (ps : List Ty) (ret : Ty)
    (Γ : Env) (es : List Expr) where
  tys : List Ty
  out : Env
  {rulesUsed : List String}
  judged : DMethodAll (used := rulesUsed) κ I fr ps ret Γ es tys out
  ordinary : Option (TraceLift (fun used => ∀ code, DJudgeAll (used := used) Γ es tys out (callbackMethodCtx κ fr code) I)) := none

structure CertifiedMethodSeq (κ : Ctx) (I : Ty) (fr : Frame) (ps : List Ty) (ret : Ty)
    (Γ : Env) (es : List Expr) where
  ty : Ty
  out : Env
  {rulesUsed : List String}
  judged : DMethodSeq (used := rulesUsed) κ I fr ps ret Γ es ty out
  ordinary : Option (TraceLift (fun used => ∀ code, DJudgeSeq (used := used) Γ es ty out (callbackMethodCtx κ fr code) I)) := none

/-- Code-only block typing has no capture spine. The assignment guard still checks self
and constants, uniformly for every actual block. The default code is only a decision input. -/
theorem callback_capStale (κ : Ctx) (fr : Frame) (x : String) (τ : Ty) (code : ClosureCode) :
    capStaleCtx x τ (callbackMethodCtx κ fr code) =
      capStaleCtx x τ (callbackMethodCtx κ fr default) := rfl

/-- A complete body checked at declared domains, with no caller-local or call-value input.
Required positional parameters are supported here; explicit &b binding remains separate. -/
structure CheckedCallbackBody (κ : Ctx) (I : Ty) (decl : Defn) where
  params : List SigParam
  blockArgs : List Ty
  blockRet : Ty
  ret : Ty
  out : Env
  paramShape : decl.params = params.map (fun p => Param.req p.1)
  paramsFO : params.all (fun p => FirstOrder p.2 && !isAliasTy p.2) = true
  blockArgsFO : blockArgs.all (fun τ => FirstOrder τ && !isAliasTy τ) = true
  blockReturnFO : FirstOrder blockRet = true
  returnFO : FirstOrder ret = true
  {rulesUsed : List String}
  judged : DMethod (used := rulesUsed) κ I ⟨"Object", "Object", decl.name, false⟩ blockArgs blockRet params decl.body ret out

end Checker.Audit
