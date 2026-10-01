import Denote.Rules.Method.MethodEntry
import Denote.Sem.Core.Boot
import Ratchet.Check.Check

/-! Ordinary metadata must establish the actual defining module of its activation. -/
namespace Ratchet.Denote.Typed
open RubyCore Ratchet.Denote

private def retargetOwner : MethodDef :=
  { params := [], owner := Boot.objectId, definee := some Boot.nilClassId,
    body := .seq [.def' "inner" [] (.int 1), .send none "inner" [] .none] }

private def legacyCodeB (md : MethodDef) : Bool :=
  decide (md.owner = Boot.objectId ∧ md.cref = [] ∧ md.superName = none ∧
    md.builtin = none ∧ md.capturedFrame = none ∧ md.declared = [] ∧
    md.fromPrelude = false ∧ md.visibilityOnly = false ∧
    md.fromBlock = false ∧ md.forTargets = none)

#guard legacyCodeB retargetOwner
#guard !ordinaryMethodCodeB Boot.objectId [] retargetOwner
#guard ordinaryMethodCodeB Boot.objectId [] { retargetOwner with definee := none }
#guard ordinaryMethodCodeB Boot.objectId [] { retargetOwner with definee := some Boot.objectId }
#guard match Interp.enterUserMethod bootMachine bootMachine.currentFrame.self
    "outer" retargetOwner [] none with
  | .next n => Semantics.typeStuck (Interp.run 100 n)
  | _ => false
#guard Ratchet.validateDWith (fun _ => true)
  (.seq [.def' "inner" [] (.int 1), .send none "inner" [] none])
  (.seq [.defDecl "inner" [] .int (.intLit 1), .callSig "inner" [] .int])
end Ratchet.Denote.Typed
