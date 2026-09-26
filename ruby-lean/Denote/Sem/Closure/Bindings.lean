import Denote.Ty.Local

/-! Binding presence differs from reading nil. Local writes retain existing slots and
can introduce a slot only in the active frame, never in an inactive captured frame. -/
set_option autoImplicit false
namespace Ratchet.Denote
open RubyCore

def frameBinds (m : Machine) (i : FrameId) (x : String) : Bool :=
  (m.frames.getD i default).locals.any (·.1 == x)

/-- Exact physical slot names, including slots whose current value is nil. EnvOk's
absence clause supplies nil reads and does not imply this domain. -/
def FrameSlots (names : List String) (m : Machine) : Prop :=
  ∀ x, frameBinds m (m.stack.headD 0) x = names.contains x

structure BindingsPres (m n : Machine) : Prop where
  bound : ∀ i, i < m.frames.size → ∀ x, frameBinds m i x = true → frameBinds n i x = true
  saved : ∀ i, i < m.frames.size → i ≠ m.stack.headD 0 → ∀ x,
    frameBinds n i x = frameBinds m i x

theorem BindingsPres.of_frames {m n : Machine}
    (hf : ∀ i, i < m.frames.size → n.frames.getD i default = m.frames.getD i default) :
    BindingsPres m n :=
  ⟨fun i hi x hx => by simpa only [frameBinds, hf i hi] using hx,
    fun i hi _ x => by simp only [frameBinds, hf i hi]⟩

theorem BindingsPres.trans {m n p : Machine} (h : BindingsPres m n) (h' : BindingsPres n p)
    (hs : n.stack = m.stack) (hz : m.frames.size ≤ n.frames.size) : BindingsPres m p :=
  ⟨fun i hi x hx => h'.bound i (Nat.lt_of_lt_of_le hi hz) x (h.bound i hi x hx),
    fun i hi hn x => (h'.saved i (Nat.lt_of_lt_of_le hi hz) (by simpa only [hs] using hn) x).trans
      (h.saved i hi hn x)⟩

theorem setLocal_owner_bound_or_start (m : Machine) (x : String) (start : FrameId) :
    ∀ fuel fid, Machine.setLocal.owner m x start fid fuel = start ∨
      frameBinds m (Machine.setLocal.owner m x start fid fuel) x = true := by
  intro fuel
  induction fuel with
  | zero => intro _; exact Or.inl rfl
  | succ fuel ih =>
    intro fid
    rw [Machine.setLocal.owner]
    split
    · rename_i hb
      exact Or.inr hb
    · split
      · exact ih _
      · exact Or.inl rfl

theorem frameBinds_setAt_ne (m : Machine) (x : String) (v : Value) (target i : FrameId)
    {y : String} (hy : y ≠ x) : frameBinds (setAt m x v target) i y = frameBinds m i y := by
  simp only [frameBinds, ← List.isSome_find?, setAt_find_ne m x v target i hy]

theorem frameBinds_setAt_mono (m : Machine) (x : String) (v : Value) (target i : FrameId)
    (y : String) (hy : frameBinds m i y = true) : frameBinds (setAt m x v target) i y = true := by
  by_cases he : y = x
  · subst y
    rcases setAt_frame_or m x v target i with hn | hn
    · simp only [frameBinds, ← List.isSome_find?, hn, Option.isSome_some]
    · simpa only [frameBinds, ← List.isSome_find?, hn] using hy
  · rw [frameBinds_setAt_ne m x v target i he]
    exact hy

theorem BindingsPres.setLocal (m : Machine) (x : String) (v : Value) :
    BindingsPres m (m.setLocal x v) := by
  have hbound (i : FrameId) (y : String) (hy : frameBinds m i y = true) :
      frameBinds (m.setLocal x v) i y = true := by
    rw [setLocal_eq_setAt]
    exact frameBinds_setAt_mono m x v _ i y hy
  refine ⟨fun i _ y hy => hbound i y hy, ?_⟩
  intro i _ hn y
  by_cases hy : y = x
  · subst y
    let target := Machine.setLocal.owner m x (m.stack.headD 0) (m.stack.headD 0) (m.frames.size + 1)
    by_cases hi : i = target
    · have hb : frameBinds m i x = true := by
        rcases setLocal_owner_bound_or_start m x (m.stack.headD 0) (m.frames.size + 1)
          (m.stack.headD 0) with he | he
        · exact False.elim (hn (hi.trans he))
        · simpa only [hi] using he
      exact (hbound i x hb).trans hb.symm
    · dsimp only [target] at hi
      simp only [setLocal_eq_setAt, frameBinds, setAt, framesD_set!_ne _ _ _ _ hi]
  · rw [setLocal_eq_setAt, frameBinds_setAt_ne m x v _ i hy]

theorem FrameSlots.setLocal {m : Machine} {names : List String} (hd : FrameSlots names m)
    (hl : m.stack.headD 0 < m.frames.size)
    (hc : (m.frames.getD (m.stack.headD 0) default).captured = none) (x : String) (v : Value) :
    FrameSlots (x :: names) (m.setLocal x v) := by
  have ho : Machine.setLocal.owner m x (m.stack.headD 0) (m.stack.headD 0) (m.frames.size + 1) =
      m.stack.headD 0 := by simp only [Machine.setLocal.owner, hc, ite_self]
  intro y
  change frameBinds (m.setLocal x v) (m.stack.headD 0) y = _
  rw [setLocal_eq_setAt, ho]
  by_cases hy : y = x
  · subst y
    simp only [frameBinds, ← List.isSome_find?, setAt_find_self m x v _ hl,
      Option.isSome_some, List.contains_cons, beq_self_eq_true, Bool.true_or]
  · rw [frameBinds_setAt_ne m x v _ _ hy, hd y]
    simp [hy]

theorem frameBinds_setLocal_self (m : Machine) (x : String) (v : Value)
    (hl : m.stack.headD 0 < m.frames.size)
    (hc : (m.frames.getD (m.stack.headD 0) default).captured = none) :
    frameBinds (m.setLocal x v) (m.stack.headD 0) x = true := by
  rw [setLocal_eq_setAt]
  have ho : Machine.setLocal.owner m x (m.stack.headD 0) (m.stack.headD 0) (m.frames.size + 1) =
      m.stack.headD 0 := by simp only [Machine.setLocal.owner, hc, ite_self]
  simp only [ho, frameBinds, ← List.isSome_find?, setAt_find_self m x v _ hl, Option.isSome_some]

#print axioms setLocal_owner_bound_or_start
#print axioms BindingsPres.setLocal
#print axioms FrameSlots.setLocal
end Ratchet.Denote
