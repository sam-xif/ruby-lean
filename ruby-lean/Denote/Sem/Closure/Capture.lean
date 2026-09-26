import Denote.Ty.Apply

/-! A live captured chain consists of existing frames and terminates. This is an explicit
activation obligation: a closure's code and lower-bound value spine do not imply it. -/
set_option autoImplicit false
namespace Ratchet.Denote
open RubyCore

inductive CaptureLive (m : Machine) : Option FrameId → Prop
  | none : CaptureLive m none
  | frame {fid : FrameId} : fid < m.frames.size →
      CaptureLive m (m.frames.getD fid default).captured → CaptureLive m (some fid)

theorem getLocal_go_eq_frameLocal_go (m : Machine) (x : String) :
    ∀ fuel fid, Machine.getLocal.go m x fid fuel = frameLocal.go m x fid fuel := by
  intro fuel
  induction fuel with
  | zero => intro fid; rfl
  | succ fuel ih =>
    intro fid
    simp only [Machine.getLocal.go, frameLocal.go]
    cases hf : (m.frames.getD fid default).locals.find? (·.1 == x) with
    | some p => rfl
    | none =>
      cases hc : (m.frames.getD fid default).captured with
      | none => rfl
      | some p => exact ih p

theorem closLocal_current {m : Machine} {cl : Closure}
    (hc : cl.captured = some (m.stack.headD 0)) : closLocal m cl = m.getLocal := by
  funext x
  simp only [closLocal, hc, frameLocal?, frameLocal, Machine.getLocal]
  exact (getLocal_go_eq_frameLocal_go m x _ _).symm

/-- Only frames on the captured chain matter; stack and heap may differ. The fuel is
kept explicit because a pushed activation consumes one unit before reading its capture. -/
theorem frameLocal_go_preserved {m n : Machine}
    (hf : ∀ i, i < m.frames.size → n.frames.getD i default = m.frames.getD i default)
    (x : String) : ∀ fuel fid, CaptureLive m (some fid) →
      frameLocal.go n x fid fuel = frameLocal.go m x fid fuel := by
  intro fuel
  induction fuel with
  | zero => intro fid _; rfl
  | succ fuel ih =>
    intro fid hl
    cases hl with
    | frame hi hc =>
      simp only [frameLocal.go, hf fid hi]
      cases hb : (m.frames.getD fid default).locals.find? (·.1 == x) with
      | some p => rfl
      | none =>
        cases hp : (m.frames.getD fid default).captured with
        | none => rfl
        | some p => exact ih p (hp ▸ hc)

theorem CaptureLive.frames_preserved {m n : Machine}
    (hsize : m.frames.size ≤ n.frames.size)
    (hf : ∀ i, i < m.frames.size → n.frames.getD i default = m.frames.getD i default)
    {cap : Option FrameId} (h : CaptureLive m cap) : CaptureLive n cap := by
  induction h with
  | none => exact .none
  | @frame fid hi hc ih =>
    exact .frame (Nat.lt_of_lt_of_le hi hsize) (by rw [hf fid hi]; exact ih)

#print axioms frameLocal_go_preserved
end Ratchet.Denote
