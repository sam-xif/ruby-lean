import Denote.Ty.Den

/-! Existing Proc payloads retain their complete code and capture descriptors.
Captured frame contents are separate: preserving the descriptor does not freeze locals. -/
set_option autoImplicit false
namespace Ratchet.Denote
open RubyCore

def ProcPres (h h' : Heap) : Prop :=
  ∀ v cl, procClosure? h v = some cl → procClosure? h' v = some cl

theorem ProcPres.refl (h : Heap) : ProcPres h h := fun _ _ hp => hp

theorem ProcPres.trans {h h' h'' : Heap} (ha : ProcPres h h') (hb : ProcPres h' h'') :
    ProcPres h h'' := fun v cl hp => hb v cl (ha v cl hp)

theorem ProcPres.of_payload {h h' : Heap}
    (hp : ∀ o, o < h.objs.size → (h'.get o).payload = (h.get o).payload) : ProcPres h h' := by
  intro v cl hv
  cases v with
  | ref o => rw [procClosure?, hp o (lt_of_procClosure? hv)]; exact hv
  | _ => cases hv

theorem ProcPres.of_nonclass {h h' : Heap}
    (hp : ∀ o, o < h.objs.size → h.classPayload? o = none → h'.get o = h.get o) :
    ProcPres h h' := by
  intro v cl hv
  cases v with
  | ref o =>
    have hn : h.classPayload? o = none := by
      unfold Heap.classPayload?
      cases he : (h.get o).payload <;> simp_all [procClosure?]
    rw [procClosure?, hp o (lt_of_procClosure? hv) hn]
    exact hv
  | _ => cases hv

#print axioms ProcPres.of_nonclass
end Ratchet.Denote
