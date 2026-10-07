import Books.TypeSoundness.Conformance.Subclass.SubclassActualParent

/-! The actual `classDefK` step: an inheritable parent value enters the same
registration as a plain class, with the parent's metadata and cached metaclass. -/
set_option autoImplicit false
namespace Checker.Soundness.FreshClassActual
open RubyCore RubyCore.Interp RubyCore.Proof RubyCore.Proof.Judgment

theorem stepFn_subclass {m : Machine} {name : String} {body : RubyCore.Expr} {e p : ObjId}
    {cp : ClassPayload} (hm : MainReady m) (hn : constOwn m.heap Boot.objectId name = none)
    (hcp : m.heap.classPayload? p = some cp) (hmod : cp.isModule = false)
    (hat : cp.attached = none) (hcls : p ≠ Boot.classId)
    (hpl : p < m.heap.objs.size) (he : (m.heap.get p).eigen = some e) :
    stepFn (deliverA (.val (.ref p)) m [.classDefK name body]) =
      .next { m with
        heap := heap m name e p,
        ctl := .send (.ref Boot.objectId) .reflective "const_added" [.sym name] none [],
        kont := [.constClassK m.heap.objs.size (some p) name body] } := by
  have ho : Boot.objectId < m.heap.objs.size :=
    Nat.lt_trans (by decide : Boot.objectId < Boot.mainId) hm.live
  have hl : m.lexicalNamespace = Boot.objectId := by
    simp only [Machine.lexicalNamespace, hm.cref, List.headD_nil]
  have hd : m.lexicalNamespace < m.heap.objs.size := hl ▸ ho
  let start : Machine := { m with ctl := .value (.ref p), kont := [] }
  have hinh : inheritableClass start (.ref p) false = .ok p := by
    have hb : (p == Boot.classId) = false := beq_eq_false_iff_ne.mpr hcls
    simp [inheritableClass, start, hcp, hmod, hat, hb]
  have hr := eigenclassOf_realized (m := start) (name := name) (p := p) hd hpl he
  have hnamed := freshClassRegistered_named (m := start) (name := name) (p := p) hm.cref ho
  have hentry := enterClassBody_fresh (m := start) (body := body) p
    (by change constOwn m.heap m.lexicalNamespace name = none; rw [hl]; exact hn)
    (by change (m.heap.get m.lexicalNamespace).frozen = false; rw [hl]; exact hm.unfrozen) hnamed
  change (match inheritableClass start (.ref p) false with
    | .error result => result
    | .ok k => enterClassBody start name false (some k) body) = _
  rw [hinh]
  dsimp only
  rw [hentry]
  have hls : start.lexicalNamespace = Boot.objectId := hl
  simp only [hls, beq_self_eq_true, ↓reduceIte]
  change callConstAdded _ Boot.objectId name = _
  rw [hr]
  simp only [callConstAdded, start, hm.phase, Bool.false_eq_true, ↓reduceIte]
  rfl

#print axioms stepFn_subclass
end Checker.Soundness.FreshClassActual
