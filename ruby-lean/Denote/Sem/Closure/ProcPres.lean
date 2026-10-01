import Denote.Ty.Den

/-! Existing Procs retain their complete descriptors and dispatch classes. Captured frame
contents are separate: preserving the descriptor does not freeze locals. -/
set_option autoImplicit false
namespace Ratchet.Denote
open RubyCore

structure ProcPres (h h' : Heap) : Prop where
  payload : ∀ v cl, procClosure? h v = some cl → procClosure? h' v = some cl
  dispatch : ∀ v cl, procClosure? h v = some cl → classOf h' v = classOf h v

theorem ProcPres.refl (h : Heap) : ProcPres h h := ⟨fun _ _ hp => hp, fun _ _ _ => rfl⟩

theorem ProcPres.trans {h h' h'' : Heap} (ha : ProcPres h h') (hb : ProcPres h' h'') :
    ProcPres h h'' :=
  ⟨fun v cl hp => hb.payload v cl (ha.payload v cl hp),
    fun v cl hp => (hb.dispatch v cl (ha.payload v cl hp)).trans (ha.dispatch v cl hp)⟩

theorem ProcPres.of_payload {h h' : Heap}
    (hp : ∀ o, o < h.objs.size → (h'.get o).payload = (h.get o).payload)
    (hk : ∀ v, classOf h' v = classOf h v) : ProcPres h h' := by
  refine ⟨?_, fun v _ _ => hk v⟩
  intro v cl hv
  cases v with
  | ref o => rw [procClosure?, hp o (lt_of_procClosure? hv)]; exact hv
  | _ => cases hv

theorem ProcPres.of_nonclass {h h' : Heap}
    (hp : ∀ o, o < h.objs.size → h.classPayload? o = none → h'.get o = h.get o) :
    ProcPres h h' := by
  have he {o : ObjId} {cl : Closure} (hv : procClosure? h (.ref o) = some cl) :
      h'.get o = h.get o := by
    have hn : h.classPayload? o = none := by
      unfold Heap.classPayload?
      cases he : (h.get o).payload <;> simp_all [procClosure?]
    exact hp o (lt_of_procClosure? hv) hn
  constructor
  · intro v cl hv
    cases v with
    | ref o => rw [procClosure?, he hv]; exact hv
    | _ => cases hv
  · intro v cl hv
    cases v with
    | ref o => simp only [classOf, he hv]
    | _ => cases hv

theorem ProcPres.of_get {h h' : Heap}
    (hp : ∀ o, o < h.objs.size → h'.get o = h.get o) : ProcPres h h' :=
  .of_nonclass (fun o ho _ => hp o ho)

#print axioms ProcPres.of_nonclass
end Ratchet.Denote
