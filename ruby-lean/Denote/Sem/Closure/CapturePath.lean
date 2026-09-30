import Denote.Sem.Closure.Capture
import Denote.Ty.Local

/-! The frames a local write can reach. A live chain lets this set survive frame growth;
without liveness a newly allocated frame may extend a previously dangling path. -/
set_option autoImplicit false
namespace Ratchet.Denote
open RubyCore

inductive CapturePath (m : Machine) : Option FrameId → FrameId → Prop
  | here (i : FrameId) : CapturePath m (some i) i
  | next {i j : FrameId} : CapturePath m (m.frames.getD i default).captured j →
      CapturePath m (some i) j

theorem CapturePath.root {m : Machine} {cap : Option FrameId} {i : FrameId}
    (h : CapturePath m cap i) : cap ≠ none := by cases h <;> simp

theorem CapturePath.uncaptured {m : Machine} {root i : FrameId}
    (hc : (m.frames.getD root default).captured = none)
    (h : CapturePath m (some root) i) : i = root := by
  cases h with
  | here => rfl
  | next h => exact False.elim (h.root hc)

theorem CaptureLive.capture_preserved {m n : Machine}
    (hsize : m.frames.size ≤ n.frames.size)
    (hc : ∀ i, i < m.frames.size →
      (n.frames.getD i default).captured = (m.frames.getD i default).captured)
    (ha : ∀ i, i < m.frames.size →
      (n.frames.getD i default).localAlias = (m.frames.getD i default).localAlias)
    {cap : Option FrameId} (h : CaptureLive m cap) : CaptureLive n cap := by
  induction h with
  | none => exact .none
  | @frame i hi _ hal ih =>
    exact .frame (Nat.lt_of_lt_of_le hi hsize) (by rw [hc i hi]; exact ih)
      (by rw [ha i hi]; exact hal)

theorem CapturePath.preserved {m n : Machine}
    (hc : ∀ i, i < m.frames.size →
      (n.frames.getD i default).captured = (m.frames.getD i default).captured)
    {cap : Option FrameId} (hl : CaptureLive m cap) (j : FrameId) :
    CapturePath n cap j ↔ CapturePath m cap j := by
  induction hl with
  | none => exact ⟨fun h => False.elim (h.root rfl), fun h => False.elim (h.root rfl)⟩
  | @frame i hi _ _ ih =>
    constructor
    · intro h
      cases h with
      | here => exact .here _
      | next h => exact .next (ih.mp (by rw [← hc i hi]; exact h))
    · intro h
      cases h with
      | here => exact .here _
      | next h => exact .next (by rw [hc i hi]; exact ih.mpr h)

theorem setLocal_owner_path (m : Machine) (x : String) (start : FrameId) :
    ∀ fuel fid, CaptureLive m (some fid) →
      Machine.setLocal.owner m x start fid fuel = start ∨
      CapturePath m (some fid) (Machine.setLocal.owner m x start fid fuel) := by
  intro fuel
  induction fuel with
  | zero => intro _ _; exact Or.inl rfl
  | succ fuel ih =>
    intro fid hl
    cases hl with
    | frame hi hcap hal =>
      by_cases hb : (m.frames.getD fid default).locals.any (·.1 == x) = true
      · simp only [Machine.setLocal.owner, localFrameId_of_noAlias hal, hb, if_true]
        exact Or.inr (.here _)
      · simp only [Machine.setLocal.owner, localFrameId_of_noAlias hal, hb, Bool.false_eq_true, if_false]
        cases hp : (m.frames.getD fid default).captured with
        | none => exact Or.inl rfl
        | some p =>
          rcases ih p (hp ▸ hcap) with he | hr
          · exact Or.inl he
          · exact Or.inr (.next (by simpa only [hp] using hr))

#print axioms CapturePath.preserved
#print axioms setLocal_owner_path
end Ratchet.Denote
