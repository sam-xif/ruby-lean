import Denote.Sem.Core.Ready

/-! Physical interpretation of a requested lexical class scope. A class-valued receiver
does not imply these facts. Method entry may change frame kind but retains the owner. -/
set_option autoImplicit false
namespace Ratchet.Denote
open RubyCore Ratchet

structure ClassScopeAt (cn : String) (k : ObjId) (m : Machine) : Prop where
  named : classNamed? m.heap cn = some k
  live : k < m.heap.objs.size
  owner : m.currentFrame.defmod = k
  cref : m.currentFrame.cref = [k]
  captured : m.currentFrame.captured = none
  phase : m.preludeMode = false
  visibility : defaultDefVis m = .pub
  hook : definitionHookQuietB m.heap k = true
  origin : m.currentFrame.libraryOrigin = false
  defFrame : m.currentFrame.definitionFrame = none
  detached : (m.heap.classPayload? k).bind (·.attached) = none
  unfrozen : (m.heap.get k).frozen = false
  mainLive : Boot.mainId < m.heap.objs.size
  notMain : k ≠ classOf m.heap (.ref Boot.mainId)

def ClassScopeReady (cn : String) (m : Machine) : Prop := ∃ k, ClassScopeAt cn k m
def ClassRuntimeOk (κ : Ctx) (m : Machine) : Prop :=
  ∀ cn, κ.scope.runtimeClass = some cn → ClassScopeReady cn m

theorem ClassRuntimeOk.visibility {κ : Ctx} {m : Machine} (h : ClassRuntimeOk κ m)
    (hr : κ.scope.runtimeClass ≠ none) : defaultDefVis m = .pub := by
  cases hc : κ.scope.runtimeClass with
  | none => exact False.elim (hr hc)
  | some cn => obtain ⟨k, hk⟩ := h cn hc; exact hk.visibility

theorem ClassScopeAt.reframe {cn : String} {k : ObjId} {m n : Machine}
    (h : ClassScopeAt cn k m) (hh : n.heap = m.heap)
    (ho : n.currentFrame.defmod = m.currentFrame.defmod)
    (hc : n.currentFrame.cref = m.currentFrame.cref)
    (hcap : n.currentFrame.captured = m.currentFrame.captured)
    (hp : n.preludeMode = m.preludeMode) (hv : defaultDefVis n = defaultDefVis m)
    (hl : n.currentFrame.libraryOrigin = m.currentFrame.libraryOrigin)
    (hd : n.currentFrame.definitionFrame = m.currentFrame.definitionFrame) :
    ClassScopeAt cn k n :=
  ⟨by simpa only [hh] using h.named, by simpa only [hh] using h.live,
    ho.trans h.owner, hc.trans h.cref, hcap.trans h.captured,
    hp.trans h.phase, hv.trans h.visibility, by simpa only [hh] using h.hook,
    hl.trans h.origin, hd.trans h.defFrame, by simpa only [hh] using h.detached,
    by simpa only [hh] using h.unfrozen, by simpa only [hh] using h.mainLive,
    by simpa only [hh] using h.notMain⟩

theorem ClassScopeReady.setLocal {cn : String} {m : Machine}
    (h : ClassScopeReady cn m) (x : String) (v : Value) :
    ClassScopeReady cn (m.setLocal x v) := by
  obtain ⟨k, h⟩ := h
  exact ⟨k, h.reframe (setLocal_heap ..) (currentFrame_setLocal_defmod ..)
    (currentFrame_setLocal_cref ..) (currentFrame_setLocal_captured ..) rfl
    (by simp only [defaultDefVis, currentFrame_setLocal_kind, currentFrame_setLocal_defVis])
    (currentFrame_setLocal_libraryOrigin ..) (currentFrame_setLocal_definitionFrame ..)⟩

theorem ClassScopeReady.ext {cn : String} {m n : Machine}
    (h : ClassScopeReady cn m) (he : Ext m n) (hp : n.preludeMode = m.preludeMode)
    (hch : Proof.ChainsIn m.heap) :
    ClassScopeReady cn n := by
  obtain ⟨k, h⟩ := h
  have hobj := he.get k h.live
  have hl : lookup n.heap (.ref k) "method_added" = lookup m.heap (.ref k) "method_added" := by
    change Interp.methodOn n.heap (classOf n.heap (.ref k)) "method_added" =
      Interp.methodOn m.heap (classOf m.heap (.ref k)) "method_added"
    simp only [classOf, hobj, he.methodOn_eq hch]
  exact ⟨k, by
    refine ⟨?_, Nat.lt_of_lt_of_le h.live he.size, ?_, ?_, ?_, hp.trans h.phase, ?_, ?_, ?_, ?_,
      by rw [he.payload]; exact h.detached, by rw [hobj]; exact h.unfrozen,
      Nat.lt_of_lt_of_le h.mainLive he.size,
      by simp only [classOf, he.get Boot.mainId h.mainLive]; exact h.notMain⟩
    · simpa only [he.classNamed?_eq] using h.named
    · simpa only [he.currentFrame_eq] using h.owner
    · simpa only [he.currentFrame_eq] using h.cref
    · simpa only [he.currentFrame_eq] using h.captured
    · simpa only [defaultDefVis, he.currentFrame_eq] using h.visibility
    · simpa only [definitionHookQuietB, hl] using h.hook
    · simpa only [he.currentFrame_eq] using h.origin
    · simpa only [he.currentFrame_eq] using h.defFrame⟩

theorem ClassScopeAt.writable {cn : String} {k : ObjId} {m : Machine} (h : ClassScopeAt cn k m) :
    frozenMethodReceiver? m.heap k = none := by
  simp only [frozenMethodReceiver?, h.detached, Option.getD_none, h.unfrozen,
    Bool.false_or, Bool.false_eq_true, ↓reduceIte]

#print axioms ClassScopeReady.ext
end Ratchet.Denote
