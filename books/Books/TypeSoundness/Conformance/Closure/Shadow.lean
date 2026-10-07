import Books.TypeSoundness.Conformance.Closure.Bindings

/-! A local already bound in the active frame shadows every saved frame's same-named
slot. This preserves values, not just slot presence, including hidden nil caller slots. -/
set_option autoImplicit false
namespace Checker.Soundness
open RubyCore

def ShadowPres (m n : Machine) : Prop :=
  ∀ x, frameBinds m (m.stack.headD 0) x = true → ∀ i, i < m.frames.size →
    i ≠ m.stack.headD 0 →
      (n.frames.getD i default).locals.find? (·.1 == x) =
        (m.frames.getD i default).locals.find? (·.1 == x)

theorem ShadowPres.of_frames {m n : Machine}
    (hf : ∀ i, i < m.frames.size → i ≠ m.stack.headD 0 →
      n.frames.getD i default = m.frames.getD i default) : ShadowPres m n := by
  intro _ _ i hi hn
  rw [hf i hi hn]

theorem ShadowPres.trans {m n p : Machine} (h : ShadowPres m n) (h' : ShadowPres n p)
    (hb : BindingsPres m n) (hs : n.stack = m.stack) (hz : m.frames.size ≤ n.frames.size) :
    ShadowPres m p := by
  intro x hx i hi hn
  have hr : m.stack.headD 0 < m.frames.size := by
    by_cases hr : m.stack.headD 0 < m.frames.size
    · exact hr
    · simp only [frameBinds, Array.getD, dif_neg hr] at hx
      cases hx
  have hx' : frameBinds n (n.stack.headD 0) x = true := by
    rw [hs]
    exact hb.bound _ hr x hx
  exact (h' x hx' i (Nat.lt_of_lt_of_le hi hz) (by simpa only [hs] using hn)).trans
    (h x hx i hi hn)

theorem ShadowPres.setLocal (m : Machine) (x : String) (v : Value)
    (ha : (m.frames.getD (m.stack.headD 0) default).localAlias = none) :
    ShadowPres m (m.setLocal x v) := by
  intro y hy i _ hn
  rw [setLocal_eq_setAt, localFrameId_of_noAlias ha]
  by_cases he : y = x
  · subst y
    have ho : Machine.setLocal.owner m x (m.stack.headD 0) (m.stack.headD 0)
        (m.frames.size + 1) = m.stack.headD 0 := by
      simp only [Machine.setLocal.owner, localFrameId_of_noAlias ha]
      exact if_pos hy
    rw [ho, setAt, framesD_set!_ne _ _ _ _ hn]
  · exact setAt_find_ne m x v _ i he

#print axioms ShadowPres.setLocal
end Checker.Soundness
