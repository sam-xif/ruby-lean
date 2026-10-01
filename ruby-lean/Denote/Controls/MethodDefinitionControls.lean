import Denote.Rules.Method.MethodDispatch
import Denote.Sem.Core.Boot

/-! Source definitions install first, then dispatch and resume their edit marker. -/
namespace Ratchet.Denote.Typed
open RubyCore Ratchet.Denote

private def definitionStart : Machine :=
  { bootMachine with ctl := .eval (.def' "bump" [] (.int 1)), kont := [] }

#guard match Interp.stepFn definitionStart with
  | .next n =>
    (match n.ctl with
      | .send (.ref k) .reflective "method_added" [.sym "bump"] none [] => k == Boot.objectId
      | _ => false) &&
    (match n.kont with | [.methodEditsK [] (.sym "bump")] => true | _ => false) &&
    ((n.heap.classPayload? Boot.objectId).bind fun cp =>
      (cp.methods.find? (·.1 == "bump")).map (·.2)).any fun md =>
      md.definee == some Boot.objectId && md.cref.isEmpty && !md.fromPrelude
  | _ => false

#guard match Interp.stepFn definitionStart with
  | .next n => match Interp.stepFn n with
    | .next n' => match n'.ctl, n'.kont with
      | .value .nil, [.methodEditsK [] (.sym "bump")] => true
      | _, _ => false
    | _ => false
  | _ => false

#guard match Interp.run 4 definitionStart with
  | .value (.sym "bump") n => n.kont.isEmpty
  | _ => false

-- Initialization-copy names share the runtime's privacy normalization.
#guard (definedMethod bootMachine "initialize_copy" [] .nil).visibility == .priv

#print axioms step_def_install
#print axioms definition_hook_runSpec
end Ratchet.Denote.Typed
