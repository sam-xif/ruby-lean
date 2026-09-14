import Denote.Typed.MethodDispatch
import Denote.Sem.ClassFrame
import Denote.Sem.ClassDispatch

/-! Ordinary instance-method metadata and the real definition step in a fresh class.
This is installation, not body admission: annotated body checking is a separate obligation. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote
open RubyCore.Proof.Judgment (freshClsHeap freshClsMachine freshModFrame)

theorem definedMethod_instanceCode {m : Machine} {k : ObjId} {name : String}
    {ps : List RubyCore.Param} {body : RubyCore.Expr}
    (ho : m.currentFrame.defmod = k) (hc : m.currentFrame.cref = [k, Boot.objectId])
    (hk : m.currentFrame.kind = .classBody) (hv : m.currentFrame.defVis = .pub)
    (hp : m.preludeMode = false) : InstanceMethodCode k name (definedMethod m name ps body) := by
  refine ⟨⟨ho, hc, rfl, rfl, rfl, rfl, hp⟩, ?_⟩
  simp only [definedMethod, hk, hv]
  split <;> rfl

variable {m : Machine} {cn : String} {e : ObjId} {body : RubyCore.Expr}
local notation "entry" => freshClsMachine m Boot.objectId m.currentFrame.cref cn cn e body

theorem fresh_class_hook (hc : Proof.ChainsIn m.heap) (hs : Proof.Saturated m.heap)
    (he : (m.heap.get Boot.objectId).eigen = some e) (hh : objectHookQuietB m.heap = true) :
    DefHookQuiet entry := by
  apply defHookQuietB_sound
  unfold defHookQuietB
  rw [FreshClass.current_frame]
  change (match lookup (freshClsHeap m.heap Boot.objectId cn cn e)
      (.ref m.heap.objs.size) "method_added" with
    | none => true
    | some (owner, md) => md.undefined || owner == Boot.objectId || owner == Boot.kernelId ||
        owner == Boot.basicObjectId) = true
  rw [lookup_eq_methodOn, Proof.Judgment.classOf_freshC_k,
    FreshClass.method_eigen hc hs (hc.eigen Boot.objectId hc.boot.2.2.2.2 e he)]
  simp only [objectHookQuietB, lookup_eq_methodOn, classOf, he] at hh
  cases hl : Interp.methodOn m.heap e "method_added" with
  | none => rfl
  | some pair =>
    obtain ⟨owner, md⟩ := pair
    rw [hl] at hh
    exact hh

theorem fresh_defined_instanceCode {name : String} {ps : List RubyCore.Param}
    {code : RubyCore.Expr} (hc : m.currentFrame.cref = [Boot.objectId])
    (hp : m.preludeMode = false) :
    InstanceMethodCode m.heap.objs.size name (definedMethod entry name ps code) := by
  apply definedMethod_instanceCode
  · rw [FreshClass.current_frame]; rfl
  · rw [FreshClass.current_frame]; simpa only [freshModFrame] using congrArg (m.heap.objs.size :: ·) hc
  · rw [FreshClass.current_frame]; rfl
  · rw [FreshClass.current_frame]; rfl
  · exact hp

theorem fresh_class_def_step {name : String} {ps : List RubyCore.Param} {code : RubyCore.Expr}
    (hc : Proof.ChainsIn m.heap) (hs : Proof.Saturated m.heap)
    (he : (m.heap.get Boot.objectId).eigen = some e) (hh : objectHookQuietB m.heap = true)
    (hn : "method_added" ≠ name) (hb : body = .def' name ps code)
    (hcref : m.currentFrame.cref = [Boot.objectId]) (hp : m.preludeMode = false) :
    Interp.stepFn entry = .next (Interp.withCtl (installMethod entry name ps code) (.value (.sym name))) ∧
      InstanceMethodCode m.heap.objs.size name (definedMethod entry name ps code) := by
  refine ⟨step_def_install ?_ (defHookQuiet_install hn (fresh_class_hook hc hs he hh)),
    fresh_defined_instanceCode hcref hp⟩
  change Ctl.eval body = .eval (.def' name ps code)
  rw [hb]

#print axioms definedMethod_instanceCode
#print axioms fresh_class_hook
#print axioms fresh_class_def_step
end Ratchet.Denote.Typed
