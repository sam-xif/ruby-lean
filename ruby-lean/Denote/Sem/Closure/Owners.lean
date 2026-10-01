import Denote.Sem.Closure.Bindings
import Denote.Sem.Closure.Capture

/-! Local writes retain lookup ownership within the source machine's fuel budget.
Liveness makes this compositional across frame growth without validating dangling captures. -/
set_option autoImplicit false
namespace Ratchet.Denote
open RubyCore

def OwnersPres (m n : Machine) : Prop :=
  CaptureLive m (some (m.stack.headD 0)) → ∀ x fuel, fuel ≤ m.frames.size + 1 →
    Machine.setLocal.owner n x (n.stack.headD 0) (n.stack.headD 0) fuel =
      Machine.setLocal.owner m x (m.stack.headD 0) (m.stack.headD 0) fuel

theorem setLocal_owner_congr {m n : Machine} (x : String) (start : FrameId)
    (hb : ∀ i, i < m.frames.size → frameBinds n i x = frameBinds m i x)
    (hc : ∀ i, i < m.frames.size →
      (n.frames.getD i default).captured = (m.frames.getD i default).captured)
    (ha : ∀ i, i < m.frames.size →
      (n.frames.getD i default).localAlias = (m.frames.getD i default).localAlias) :
    ∀ fuel fid, CaptureLive m (some fid) →
      Machine.setLocal.owner n x start fid fuel = Machine.setLocal.owner m x start fid fuel := by
  intro fuel
  induction fuel with
  | zero => intro _ _; rfl
  | succ fuel ih =>
    intro fid hl
    cases hl with
    | frame hi hp hal =>
      have haln : (n.frames.getD fid default).localAlias = none := (ha fid hi).trans hal
      have he : (n.frames.getD fid default).locals.any (·.1 == x) =
          (m.frames.getD fid default).locals.any (·.1 == x) := hb fid hi
      by_cases hbm : (m.frames.getD fid default).locals.any (·.1 == x) = true
      · simp only [Machine.setLocal.owner, localFrameId_of_noAlias hal, localFrameId_of_noAlias haln, he, hbm, if_true]
      · simp only [Machine.setLocal.owner, localFrameId_of_noAlias hal, localFrameId_of_noAlias haln, he, hbm, if_false, hc fid hi]
        cases he : (m.frames.getD fid default).captured with
        | none => rfl
        | some p => exact ih p (he ▸ hp)

theorem OwnersPres.of_frames {m n : Machine} (hs : n.stack = m.stack)
    (hf : ∀ i, i < m.frames.size → n.frames.getD i default = m.frames.getD i default) :
    OwnersPres m n := by
  intro hl x fuel _
  rw [hs]
  exact setLocal_owner_congr x _ (fun i hi => by simp only [frameBinds, hf i hi])
    (fun i hi => by rw [hf i hi]) (fun i hi => by rw [hf i hi]) fuel _ hl

theorem OwnersPres.trans {m n p : Machine} (h : OwnersPres m n) (h' : OwnersPres n p)
    (hz : m.frames.size ≤ n.frames.size)
    (hl : CaptureLive m (some (m.stack.headD 0)) → CaptureLive n (some (n.stack.headD 0))) :
    OwnersPres m p := by
  intro hm x fuel hf
  exact (h' (hl hm) x fuel (Nat.le_trans hf (Nat.add_le_add_right hz 1))).trans (h hm x fuel hf)

theorem setLocal_owner_uncaptured {m : Machine} {root : FrameId}
    (hc : (m.frames.getD root default).captured = none)
    (ha : (m.frames.getD root default).localAlias = none) (x : String) (fuel : Nat) :
    Machine.setLocal.owner m x root root fuel = root := by
  cases fuel with
  | zero => rfl
  | succ fuel => simp only [Machine.setLocal.owner, localFrameId_of_noAlias ha, hc]; split <;> rfl

theorem OwnersPres.uncaptured {m n : Machine} (hs : n.stack = m.stack)
    (hm : (m.frames.getD (m.stack.headD 0) default).captured = none)
    (hn : (n.frames.getD (n.stack.headD 0) default).captured = none)
    (han : (n.frames.getD (n.stack.headD 0) default).localAlias = none) : OwnersPres m n := by
  intro hl x fuel _
  have ham : (m.frames.getD (m.stack.headD 0) default).localAlias = none := by
    cases hl with | frame _ _ ha => exact ha
  rw [setLocal_owner_uncaptured hn han, setLocal_owner_uncaptured hm ham, hs]

theorem setLocal_owner_mono (m : Machine) (x : String) (start : FrameId) :
    ∀ fuel fid extra, Machine.setLocal.owner m x start fid fuel ≠ start →
      Machine.setLocal.owner m x start fid (fuel + extra) =
        Machine.setLocal.owner m x start fid fuel := by
  intro fuel
  induction fuel with
  | zero => intro _ _ h; exact False.elim (h rfl)
  | succ fuel ih =>
    intro fid extra hn
    by_cases hb : (m.frames.getD (m.localFrameId fid) default).locals.any (·.1 == x) = true
    · simp only [Nat.succ_add, Machine.setLocal.owner, hb, if_true]
    · simp only [Nat.succ_add, Machine.setLocal.owner, hb] at hn ⊢
      cases hc : (m.frames.getD (m.localFrameId fid) default).captured with
      | some p => simp only [hc] at hn ⊢; exact ih p extra hn
      | none => simp only [hc] at hn; exact False.elim (hn rfl)

theorem OwnersPres.setLocal (m : Machine) (x : String) (v : Value) :
    OwnersPres m (m.setLocal x v) := by
  intro hl y fuel hf
  have hal : (m.frames.getD (m.stack.headD 0) default).localAlias = none := by
    cases hl with | frame _ _ ha => exact ha
  rw [setLocal_eq_setAt, localFrameId_of_noAlias hal]
  let target := Machine.setLocal.owner m x (m.stack.headD 0) (m.stack.headD 0) (m.frames.size + 1)
  change Machine.setLocal.owner (setAt m x v target) y (m.stack.headD 0) (m.stack.headD 0) fuel = _
  by_cases hy : y = x
  · subst y
    by_cases hb : frameBinds m target x = true
    · apply setLocal_owner_congr x _ (fun i _ => ?_)
        (fun i _ => setAt_captured m x v target i)
        (fun i _ => setAt_localAlias m x v target i) fuel _ hl
      by_cases hi : i = target
      · subst i
        exact (frameBinds_setAt_mono m x v target target x hb).trans hb.symm
      · simp only [frameBinds, setAt, framesD_set!_ne _ _ _ _ hi]
    · have ht : target = m.stack.headD 0 :=
        (setLocal_owner_bound_or_start m x _ (m.frames.size + 1) _).resolve_right hb
      have ho : Machine.setLocal.owner m x (m.stack.headD 0) (m.stack.headD 0) fuel =
          m.stack.headD 0 := by
        by_cases hn : Machine.setLocal.owner m x (m.stack.headD 0) (m.stack.headD 0) fuel =
            m.stack.headD 0
        · exact hn
        · have hm := setLocal_owner_mono m x (m.stack.headD 0) fuel (m.stack.headD 0)
            (m.frames.size + 1 - fuel) hn
          rw [Nat.add_sub_of_le hf] at hm
          exact False.elim (hn (hm.symm.trans ht))
      rw [ho, ht]
      cases fuel with
      | zero => rfl
      | succ fuel =>
        have hi : m.stack.headD 0 < m.frames.size := by cases hl with | frame hi _ _ => exact hi
        have hf := setAt_find_self m x v (m.stack.headD 0) hi
        have hb : frameBinds (setAt m x v (m.stack.headD 0)) (m.stack.headD 0) x = true := by
          simp only [frameBinds, ← List.isSome_find?, hf, Option.isSome_some]
        change ((setAt m x v (m.stack.headD 0)).frames.getD (m.stack.headD 0) default).locals.any
          (·.1 == x) = true at hb
        simp only [Machine.setLocal.owner, localFrameId_setAt, localFrameId_of_noAlias hal, hb, if_true]
  · exact setLocal_owner_congr y _ (fun i _ => frameBinds_setAt_ne m x v target i hy)
      (fun i _ => setAt_captured m x v target i)
      (fun i _ => setAt_localAlias m x v target i) fuel _ hl

theorem OwnersPres.unshadowed {m n : Machine} (h : OwnersPres m n)
    (hl : CaptureLive m (some (m.stack.headD 0))) (hs : n.stack = m.stack)
    (han : (n.frames.getD (n.stack.headD 0) default).localAlias = none)
    (x : String) {fuel : Nat} (hf : fuel + 1 ≤ m.frames.size + 1)
    (ho : Machine.setLocal.owner m x (m.stack.headD 0) (m.stack.headD 0) (fuel + 1) ≠
      m.stack.headD 0) : frameBinds n (n.stack.headD 0) x = false := by
  have he := h hl x (fuel + 1) hf
  cases hb : frameBinds n (n.stack.headD 0) x with
  | false => rfl
  | true =>
    change (n.frames.getD (n.stack.headD 0) default).locals.any (·.1 == x) = true at hb
    simp only [Machine.setLocal.owner, localFrameId_of_noAlias han, hb, if_true] at he
    exact False.elim (ho (he.symm.trans (congrArg (fun s => s.headD 0) hs)))

#print axioms OwnersPres.setLocal
#print axioms OwnersPres.unshadowed
end Ratchet.Denote
