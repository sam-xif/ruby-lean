import Ratchet.Judgment.DMethod

/-! Certificates for the callback-capable body checker. An optional ordinary
proof permits reuse of existing expression rules, but only when every child has one. -/
set_option autoImplicit false
namespace Ratchet

structure CertifiedMethod (κ : Ctx) (I : Ty) (fr : Frame) (ps : List Ty) (ret : Ty) (Γ : Env) (e : Expr) where
  ty : Ty
  out : Env
  judged : DMethod κ I fr ps ret Γ e ty out
  ordinary : Option (PLift (∀ code, DJudge Γ e ty out (callbackMethodCtx κ fr code) I)) := none

def CertifiedMethod.ofOrdinary {κ : Ctx} {I : Ty} {fr : Frame} {ps : List Ty} {ret τ : Ty}
    {Γ Γ' : Env} {e : Expr}
    (h : ∀ code, DJudge Γ e τ Γ' (callbackMethodCtx κ fr code) I) :
    CertifiedMethod κ I fr ps ret Γ e := ⟨τ, Γ', .ordinary h, some ⟨h⟩⟩

structure CertifiedMethodAll (κ : Ctx) (I : Ty) (fr : Frame) (ps : List Ty) (ret : Ty)
    (Γ : Env) (es : List Expr) where
  tys : List Ty
  out : Env
  judged : DMethodAll κ I fr ps ret Γ es tys out
  ordinary : Option (PLift (∀ code, DJudgeAll Γ es tys out (callbackMethodCtx κ fr code) I)) := none

structure CertifiedMethodSeq (κ : Ctx) (I : Ty) (fr : Frame) (ps : List Ty) (ret : Ty)
    (Γ : Env) (es : List Expr) where
  ty : Ty
  out : Env
  judged : DMethodSeq κ I fr ps ret Γ es ty out
  ordinary : Option (PLift (∀ code, DJudgeSeq Γ es ty out (callbackMethodCtx κ fr code) I)) := none

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
  judged : DMethod κ I ⟨"Object", "Object", decl.name, false⟩ blockArgs blockRet params decl.body ret out

end Ratchet
