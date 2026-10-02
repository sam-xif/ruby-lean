import Denote.Sem.Core.Framed

/-! Proc payload transport retains exact code. A full callable denotation additionally
needs captured reads and self to retain their meanings; these are separate obligations. -/
set_option autoImplicit false
namespace Ratchet.Denote
open RubyCore Ratchet

theorem Framed.closureCode {m n : Machine} {code : ClosureCode} {cap selfT : Ty} {v : Value}
    (h : Framed m n) (hv : denM (.clos code cap selfT) m v) :
    ∃ cl, procClosure? m.heap v = some cl ∧ procClosure? n.heap v = some cl ∧
      ClosureMatches code cl := by
  rw [denM] at hv
  obtain ⟨cl, hp, hc, _⟩ := hv
  exact ⟨cl, hp, h.procs.payload v cl hp, hc⟩

/-- Frame metadata preservation keeps live capture chains live. -/
theorem FramePres.captureLive {m n : Machine} (h : FramePres m n) (hs : n.stack = m.stack)
    {c : Option FrameId} (hl : CaptureLive m c) : CaptureLive n c := by
  induction hl with
  | none => exact .none
  | @frame fid hi _ ha ih =>
    exact .frame (Nat.lt_of_lt_of_le hi h.size) (by rw [h.captured hs fid hi]; exact ih)
      (by rw [h.localAlias hs fid hi]; exact ha)

/-- Unchanged captured values may still require heap transport for their types.
Neither equality here follows merely from retaining the Proc payload. -/
theorem Framed.closureDen {m n : Machine} {code : ClosureCode} {cap selfT : Ty} {v : Value}
    (h : Framed m n) (hv : denM (.clos code cap selfT) m v)
    (ht : FirstOrder cap = true) (hs : FirstOrder selfT = true)
    (hcap : ∀ cl, procClosure? m.heap v = some cl → closLocal n cl = closLocal m cl)
    (hself : ∀ cl, procClosure? m.heap v = some cl → closSelf n cl = closSelf m cl) :
    denM (.clos code cap selfT) n v := by
  rw [denM] at hv ⊢
  obtain ⟨cl, hp, hc, hd, hv, hl⟩ := hv
  refine ⟨cl, h.procs.payload v cl hp, hc, ?_, ?_, hl.imp_right (h.frames.captureLive h.stack)⟩
  · rw [hcap cl hp]
    exact denSpineFrom_mono (fun _ τ ht hv => h.firstOrder τ ht _ hv) ht hd
  · rcases hv with he | hv
    · exact Or.inl he
    · right
      rw [hself cl hp]
      exact h.firstOrder selfT hs _ hv

/-- With no recorded capture/self type claims, the denotation asks only for exact code.
This retains the value's type; it does not assert that invoking its body is safe. -/
theorem ProcPres.empty_capture_den {m n : Machine} {code : ClosureCode} {v : Value}
    (h : ProcPres m.heap n.heap) (hv : denM (.clos code .ivar0 .never) m v) :
    denM (.clos code .ivar0 .never) n v := by
  rw [denM] at hv ⊢
  obtain ⟨cl, hp, hc, _⟩ := hv
  exact ⟨cl, h.payload v cl hp, hc, by simp [denSpineFrom], Or.inl rfl, Or.inl ⟨rfl, rfl⟩⟩

#print axioms Framed.closureDen
#print axioms ProcPres.empty_capture_den
end Ratchet.Denote
