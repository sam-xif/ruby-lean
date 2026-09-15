import Denote.Sem.ClassMethods
import Denote.Sem.ClassCore
import Denote.Typed.ClassEntry
import Denote.Sanity

/-! Core and installed-code conformance through actual class entry. This is not full
class-body conformance or admission: the frame and remaining context fields still matter. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem class_entry_core {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine}
    {name : String} {body : Ratchet.Expr} (hm : StateOk κ Γ I m)
    (hr : κ.scope.runtimeMain = true)
    (hn : constOwn m.heap Boot.objectId name = none) (hne : name.isEmpty = false) :
    ∃ n, Interp.stepFn (evalFrom m (.class' name none body)) = .next n ∧
      CoreOk n.heap ∧ primitiveDispatchB n.heap (nameFreeN κ) = true ∧
      primitiveErrorsB n.heap = true ∧ StringPayloadOk n.heap ∧
      ArrayPayloadOk n.heap ∧ HashPayloadOk n.heap ∧ ClassesOk κ.classes n ∧
      DefsOk κ.defs n ∧ MethodsExact κ n := by
  obtain ⟨e, he, hstep⟩ := stepFn_class_fresh hm hr hn hne
  have hc := hm.core.classReady.chains
  have ho := hc.boot.2.2.2.2
  refine ⟨_, hstep, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact FreshClass.core hm.core hm.sat (hm.runtime hr).classLive hn he
  · exact (FreshClass.primitiveDispatch hc hm.sat _).trans hm.primitiveDispatch
  · exact (FreshClass.primitiveErrors hc hm.sat).trans hm.primitiveErrors
  · exact FreshClass.stringPayload hc hm.stringPayload
  · exact FreshClass.arrayPayload hm.arrayPayload
  · exact FreshClass.hashPayload hm.hashPayload
  · exact FreshClass.classes ho hn rfl hm.classes
  · exact FreshClass.defs ho rfl hm.defs
  · exact FreshClass.methodsExact ho rfl hm.exact

private def entryCoreB (name : String) : Bool :=
  match Interp.enterClassBody bootMachine name false none .nil with
  | .next n => coreOkB n.heap && primitiveDispatchB n.heap (nameFreeN ctx0) &&
      primitiveErrorsB n.heap && stringPayloadB n.heap && arrayPayloadB n.heap && hashPayloadB n.heap
  | _ => false

#guard entryCoreB "Point"
-- CoreOk's implication also permits defining a previously absent core name as a class.
-- Do not turn preservation into an arbitrary blacklist of all core names.
#guard (constOwn bootMachine.heap Boot.objectId "IOError").isNone
#guard entryCoreB "IOError"

-- A pre-existing user method stays installed with its parameters, body, and metadata.
-- No assertion here types the new class or substitutes a signature for a body proof.
private def kept : MethodDef :=
  { owner := Boot.objectId, params := [.req "x"], body := .var .lvar "x",
    cref := [Boot.objectId] }
#guard
  let m := { bootMachine with heap := defineMethod bootMachine.heap Boot.objectId "kept" kept }
  match Interp.enterClassBody m "Point" false none .nil with
  | .next n =>
      match Interp.methodOn n.heap Boot.objectId "kept" with
      | some (_, md) => md.params.length == 1 && md.builtin.isNone && !md.undefined &&
          md.owner == Boot.objectId && md.cref == [Boot.objectId] && md.capturedFrame.isNone &&
          (match md.body with | .var .lvar "x" => true | _ => false)
      | _ => false
  | _ => false

#print axioms class_entry_core
end Ratchet.Denote.Typed
