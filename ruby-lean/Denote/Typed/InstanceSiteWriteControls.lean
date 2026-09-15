import Denote.Typed.InstanceSitePublish
import Denote.Sem.InstanceSiteEntry
import Denote.Sem.IvarMutation
import Denote.Sanity

/-! A name reservation is necessary, not just a convenient induction premise.
These tests exercise actual method calls and hook interception; no class rule is admitted. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote
open RubyCore.Proof.Judgment (freshClsMachine freshClsHeap)

theorem unreserved_method_breaks_site {κ : Ctx} {cn name : String} {k : ObjId}
    {h : Heap} {md : MethodDef} (site : InstanceSite κ cn k h)
    (hs : name ∈ shadowableNames) (hf : nameFreeN κ name = true)
    (hb : md.builtin = none) (hu : md.undefined = false) :
    ¬ InstanceSite κ cn k (defineMethod h k name md) := by
  intro bad
  obtain ⟨rest, ha⟩ := classFrontB_sound site.front
  have hm : Interp.methodOn (defineMethod h k name md) k name = some (k, md) := by
    rw [methodOn_eq_go, Proof.ancestors_defineMethod, ha,
      Proof.lookup_go_defineMethod_self _ _ _ _ (namedClass_payload site.named)]
  rcases bad.names name hs k md hm with hm | hm | hm
  · simp [hb] at hm
  · rw [hu] at hm; cases hm
  · rw [hf] at hm; cases hm

-- Actual fresh class -> def -> site preservation, not a measured postcondition.
theorem fresh_def_site {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine} {cn name : String}
    {e : ObjId} {ps : List RubyCore.Param} {body : RubyCore.Expr}
    (hm : StateOk κ Γ I m) (hr : κ.scope.runtimeMain = true)
    (he : (m.heap.get Boot.objectId).eigen = some e) (hq : "method_added" ≠ name) :
    let entry := freshClsMachine m Boot.objectId m.currentFrame.cref cn cn e (.def' name ps body)
    ∃ n, Interp.stepFn entry = .next n ∧
      InstanceSite (reserveNameCtx κ name) cn m.heap.objs.size n.heap := by
  dsimp only
  have ready := hm.runtime hr
  obtain ⟨hs, _⟩ := fresh_class_def_step (cn := cn) (body := .def' name ps body)
    hm.core.classReady.chains hm.sat he ready.hook hq rfl ready.cref ready.phase
  refine ⟨_, hs, ?_⟩
  exact ((FreshClass.instanceSite (body := .def' name ps body) hm hr he).reserveName name).methodWrite
    (by simp [nameFreeN, reserveNameCtx, Ctx.declared]) hq

-- Field writes do not disturb a method's lexical/dispatch site, even at a class object.
example {κ : Ctx} {cn : String} {k : ObjId} {m : Machine}
    (site : InstanceSite κ cn k m.heap) (x : String) (v : Value) :
    InstanceSite κ cn k (Interp.bindIvar m x v).heap := site.ivarOnly (bindIvar_ivarOnly m x v)

-- An ordinary explicit x call executes the installed body.
#guard match Interp.run 150 (evalFrom bootMachine (.seq [
    .class' "Point" none (.def' "x" [] (.int 1)),
    .send (some (.send (some (.send (some (.const "Point")) "new" [] none)) "x" [] none))
      "+" [.int 1] none])) with
  | .value (.int 2) _ => true
  | _ => false

-- Heap countermodel: adding a singleton hook is not an ordinary quiet definition.
#guard match Interp.enterClassBody bootMachine "Point" false none .nil with
  | .next m =>
      let k := m.currentFrame.defmod
      let e := classOf m.heap (.ref k)
      let h := defineMethod m.heap e "method_added"
        { owner := e, params := [.req "name"],
          body := .send (some .fls) "+" [.int 1] none }
      definitionHookQuietB m.heap k && !definitionHookQuietB h k &&
        Semantics.typeStuck (Interp.run 150
          (evalFrom { m with heap := h } (.def' "answer" [] (.int 1))))
  | _ => false

#print axioms unreserved_method_breaks_site
#print axioms fresh_def_site
end Ratchet.Denote.Typed
