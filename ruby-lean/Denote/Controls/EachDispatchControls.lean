import Denote.Rules.Iterator.Dispatch
import Denote.Sem.Core.Boot

/-! Array payloads remain typed when each is overridden or undefined. Native readiness
must independently reject both, including an inherited override. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed.EachDispatchControls
open RubyCore Ratchet Ratchet.Denote

private def arrayId : ObjId := bootMachine.heap.objs.size
private def caller : Machine := (Builtins.allocArr bootMachine #[.int 1]).2
private def allocated : Machine := reifiedMachine caller [.req "x"] [] (.var .lvar "x") false
private def blockId : ObjId := caller.heap.objs.size
private def replacement : MethodDef := { owner := Boot.arrayId, params := [], body := .int 7 }
private def changed (owner : ObjId) (md : MethodDef) : Machine :=
  { allocated with heap := defineMethod allocated.heap owner "each" { md with owner } }

#guard eachDispatchB allocated.heap (nameFreeN ctx0)
#guard !eachDispatchB (changed Boot.arrayId replacement).heap (nameFreeN ctx0)
#guard !eachDispatchB (changed Boot.objectId replacement).heap (nameFreeN ctx0)
#guard !eachDispatchB (changed Boot.arrayId { replacement with undefined := true }).heap (nameFreeN ctx0)
#guard primitiveDispatchB (changed Boot.arrayId replacement).heap
  (fun name => name != "each" && nameFreeN ctx0 name)
#guard arrayPayloadB (changed Boot.arrayId replacement).heap

-- Dispatch really uses the override; entering the native loop would return the array.
#guard match Interp.invoke (changed Boot.arrayId replacement) (.ref arrayId) .explicit "each"
    [] (some (.ref blockId)) [] with
  | .next n => match Interp.run 20 n with
    | .value v _ => v.identEq (.int 7)
    | _ => false
  | _ => false

theorem state_excludes_override (κ : Ctx) (Γ : Env) (I : Ty)
    (hf : nameFreeN κ "each" = true) {m : Machine}
    (hm : StateOk κ Γ I m) : Interp.methodOn m.heap Boot.arrayId "each" = none :=
  each_lookup_miss hm.primitiveDispatch hf

#print axioms state_excludes_override
end Ratchet.Denote.Typed.EachDispatchControls
