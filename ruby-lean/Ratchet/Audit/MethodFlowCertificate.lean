-- Generated from Ratchet/Check/MethodFlowCertificate.lean by scripts/generate_audited_checker.py.
-- Edit the raw source and regenerate; Lean checks the indexed proof and trace.
import Ratchet.Audit.Erase
import Ratchet.Check.MethodLocalTy

/-! Code-polymorphic certificates: every stored derivation works for all callback
codes, while the local type records the opaque code until actual method entry. -/
set_option autoImplicit false
namespace Ratchet.Audit
open Ratchet

structure CertifiedMethodFlow (κ : Ctx) (I : Ty) (fr : Frame) (ps : List Ty) (ret : Ty)
    (Γ : MethodLocalEnv) (facts : CallbackFacts) (e : Expr) where
  ty : MethodLocalTy
  out : MethodLocalEnv
  callback : Bool
  outFacts : CallbackFacts
  typeValid : ty.validB = true
  envValid : out.validB = true
  {rulesUsed : List String}
  judged : ∀ code, DMethodFlow (used := rulesUsed) κ I fr ps ret (Γ.instantiate code) facts e
    (ty.instantiate code) callback (out.instantiate code) outFacts

structure CertifiedMethodFlowSeq (κ : Ctx) (I : Ty) (fr : Frame) (ps : List Ty) (ret : Ty)
    (Γ : MethodLocalEnv) (facts : CallbackFacts) (es : List Expr) where
  ty : MethodLocalTy
  out : MethodLocalEnv
  callback : Bool
  outFacts : CallbackFacts
  typeValid : ty.validB = true
  envValid : out.validB = true
  {rulesUsed : List String}
  judged : ∀ code, DMethodFlowSeq (used := rulesUsed) κ I fr ps ret (Γ.instantiate code) facts es
    (ty.instantiate code) callback (out.instantiate code) outFacts

/-- A complete lone-&b definition checked before any callback or call values are known.
Sorbet 0.6.13405 checks the declared Proc domain even in uncalled methods (clink 242). -/
structure CheckedBoundCallbackBody (κ : Ctx) (I : Ty) (decl : Defn) where
  localName : String
  blockArgs : List Ty
  blockRet : Ty
  ret : Ty
  out : MethodLocalEnv
  callback : Bool
  outFacts : CallbackFacts
  paramShape : decl.params = [.block (some localName)]
  blockArgsFO : blockArgs.all (fun τ => FirstOrder τ && !isAliasTy τ) = true
  blockReturnFO : FirstOrder blockRet = true
  returnFO : FirstOrder ret = true
  {rulesUsed : List String}
  judged : ∀ code, DMethodFlow (used := rulesUsed) κ I ⟨"Object", "Object", decl.name, false⟩ blockArgs blockRet
    [(localName, .clos code .ivar0 .never)] ⟨[localName]⟩ decl.body ret callback
    (out.instantiate code) outFacts

end Ratchet.Audit
