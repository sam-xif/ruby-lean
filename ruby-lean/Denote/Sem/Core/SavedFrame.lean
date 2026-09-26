import Denote.Sem.Core.Framed

/-! Conformance reads the saved activation's metadata independently of its mutable locals. -/
set_option autoImplicit false
namespace Ratchet.Denote
open RubyCore

theorem Framed.frameOk_saved {m n : Machine} {fr : Option Ratchet.Frame} (h : Framed m n)
    (hf : FrameOk fr m) (hc : savedFrame n.currentFrame = savedFrame m.currentFrame) :
    FrameOk fr n := by
  have hs := congrArg RubyCore.Frame.self hc
  have hm := congrArg RubyCore.Frame.meth hc
  have hk := congrArg RubyCore.Frame.kind hc
  change n.currentFrame.self = m.currentFrame.self at hs
  change n.currentFrame.meth = m.currentFrame.meth at hm
  change n.currentFrame.kind = m.currentFrame.kind at hk
  cases fr with
  | none => simpa only [FrameOk, hk] using hf
  | some f =>
    exact ⟨hm.trans hf.1, by
      rw [hs]
      exact h.firstOrder f.recvTy (by unfold Ratchet.Frame.recvTy; split <;> rfl) _ hf.2.1,
      hk.trans hf.2.2⟩

#print axioms Framed.frameOk_saved

/-- At an uncaptured activation, equal current frames give equal local reads. Types
still require transport; this supports closure-valued locals without erasing their type. -/
theorem EnvOk.reframe_uncaptured {Γ : Ratchet.Env} {m n : Machine} (he : EnvOk Γ m)
    (hm : FrameInRange m) (hn : FrameInRange n) (hu : RootUncaptured m)
    (hc : n.currentFrame = m.currentFrame)
    (hmove : ∀ p ∈ Γ, ∀ v, denM (Ratchet.stripAlias p.2) m v →
      denM (Ratchet.stripAlias p.2) n v) : EnvOk Γ n := by
  have hread (x : String) : n.getLocal x = m.getLocal x := by
    simp only [Machine.getLocal, Machine.getLocal.go, ← currentFrame_headD hn.1,
      ← currentFrame_headD hm.1, hc]
    have hcap : m.currentFrame.captured = none := by
      rw [currentFrame_headD hm.1]; exact hu
    cases m.currentFrame.locals.find? (·.1 == x) <;> simp [hcap]
  refine ⟨?_, fun x hx => by rw [hread]; exact he.2 x hx⟩
  intro x τ hx
  obtain ⟨z, hz⟩ := envGet?_mem hx
  obtain ⟨hv, ha⟩ := he.1 x τ hx
  exact ⟨by rw [hread]; exact hmove (z, τ) hz _ hv,
    fun y σ hy => by rw [hread, hread]; exact ha y σ hy⟩

#print axioms EnvOk.reframe_uncaptured
end Ratchet.Denote
