import Denote.Sem.ClassFrame
import Denote.Sem.ClassDispatch

/-! Establish the requested scope at the actual fresh-class transition. -/
set_option autoImplicit false
namespace Ratchet.Denote.FreshClass
open RubyCore Ratchet
open RubyCore.Proof.Judgment (freshClsHeap freshClsMachine freshModFrame)

variable {m : Machine} {cn : String} {e : ObjId} {body : RubyCore.Expr}
local notation "entry" => freshClsMachine m Boot.objectId m.currentFrame.cref cn cn e body

theorem hook_quiet (hc : Proof.ChainsIn m.heap) (hs : Proof.Saturated m.heap)
    (he : (m.heap.get Boot.objectId).eigen = some e) (hh : objectHookQuietB m.heap = true) :
    definitionHookQuietB (entry).heap m.heap.objs.size = true := by
  unfold definitionHookQuietB
  change (match lookup (freshClsHeap m.heap Boot.objectId cn cn e)
      (.ref m.heap.objs.size) "method_added" with
    | none => true
    | some (owner, md) => md.undefined || owner == Boot.objectId || owner == Boot.kernelId ||
        owner == Boot.basicObjectId) = true
  rw [lookup_eq_methodOn, Proof.Judgment.classOf_freshC_k,
    method_eigen hc hs (hc.eigen Boot.objectId hc.boot.2.2.2.2 e he)]
  simp only [objectHookQuietB, definitionHookQuietB, lookup_eq_methodOn, classOf, he] at hh
  cases hl : Interp.methodOn m.heap e "method_added" with
  | none => rfl
  | some pair => obtain ⟨owner, md⟩ := pair; rw [hl] at hh; exact hh

theorem scope_ready (hc : Proof.ChainsIn m.heap) (hs : Proof.Saturated m.heap)
    (he : (m.heap.get Boot.objectId).eigen = some e) (hm : MainReady m) :
    ClassScopeReady cn entry := by
  refine ⟨m.heap.objs.size, ?_, ?_, ?_, ?_, ?_, hm.phase, ?_, hook_quiet hc hs he hm.hook⟩
  · exact classNamed_freshClass hm.classLive (lt_size_of_classPayload hm.classLive)
  · change m.heap.objs.size < (freshClsHeap m.heap Boot.objectId cn cn e).objs.size
    rw [Proof.Judgment.freshClsHeap_size]; omega
  · rw [current_frame]; rfl
  · rw [current_frame]; simpa only [freshModFrame] using congrArg (m.heap.objs.size :: ·) hm.cref
  · rw [current_frame]; rfl
  · simp only [defaultDefVis, current_frame, freshModFrame]; rfl

#print axioms scope_ready
end Ratchet.Denote.FreshClass
