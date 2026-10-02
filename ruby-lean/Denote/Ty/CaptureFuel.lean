import Denote.Ty.Apply

/-! A live capture chain visits distinct frames, so it ends within `frames.size` steps.
Consequently `frameLocal` does not depend on extra fuel, which a growing frame store adds. -/
set_option autoImplicit false
namespace Ratchet.Denote
open RubyCore

def capStep (m : Machine) : Option FrameId → Option FrameId
  | none => none
  | some fid => (m.frames.getD fid default).captured

def chainAt (m : Machine) (c : Option FrameId) : Nat → Option FrameId
  | 0 => c
  | k + 1 => chainAt m (capStep m c) k

theorem chainAt_none (m : Machine) : ∀ k, chainAt m none k = none
  | 0 => rfl
  | k + 1 => chainAt_none m k

theorem chainAt_succ (m : Machine) : ∀ k c, chainAt m c (k + 1) = capStep m (chainAt m c k)
  | 0, _ => rfl
  | k + 1, c => chainAt_succ m k (capStep m c)

theorem chainAt_add (m : Machine) (c : Option FrameId) : ∀ i j,
    chainAt m c (i + j) = chainAt m (chainAt m c i) j := by
  intro i
  induction i generalizing c with
  | zero => intro j; simp [chainAt]
  | succ i ih => intro j; rw [Nat.succ_add]; exact ih _ j

theorem CaptureLive.step {m : Machine} {c : Option FrameId} (h : CaptureLive m c) :
    CaptureLive m (capStep m c) := by
  cases h with
  | none => exact .none
  | frame _ hc _ => exact hc

theorem CaptureLive.chain {m : Machine} {c : Option FrameId} (h : CaptureLive m c) :
    ∀ k, CaptureLive m (Ratchet.Denote.chainAt m c k) := by
  intro k
  induction k generalizing c with
  | zero => exact h
  | succ k ih => exact ih h.step

theorem CaptureLive.lt {m : Machine} {fid : FrameId} (h : CaptureLive m (some fid)) :
    fid < m.frames.size := by
  cases h with | frame hi _ _ => exact hi

/-- A live chain never returns to a frame it has left. -/
theorem CaptureLive.no_return {m : Machine} {c : Option FrameId} (h : CaptureLive m c) :
    ∀ k, c ≠ Option.none → Ratchet.Denote.chainAt m c (k + 1) ≠ c := by
  induction h with
  | none => intro _ h; exact absurd rfl h
  | @frame fid _ hc _ ih =>
    intro k _ heq
    change Ratchet.Denote.chainAt m (m.frames.getD fid default).captured k = some fid at heq
    cases hcp : (m.frames.getD fid default).captured with
    | none => rw [hcp, chainAt_none] at heq; cases heq
    | some p =>
      have h1 : Ratchet.Denote.chainAt m (m.frames.getD fid default).captured (k + 1) =
          (m.frames.getD fid default).captured := by
        rw [chainAt_succ, heq]; rfl
      exact ih k (by rw [hcp]; simp) h1

/-- Distinct naturals below `n` number at most `n`. -/
theorem nodup_bound : ∀ (n : Nat) (l : List Nat), l.Nodup → (∀ x ∈ l, x < n) → l.length ≤ n := by
  intro n
  induction n with
  | zero => intro l _ h; cases l with
    | nil => exact Nat.le_refl _
    | cons x _ => exact absurd (h x (List.mem_cons_self ..)) (Nat.not_lt_zero _)
  | succ n ih =>
    intro l hl h
    by_cases hn : n ∈ l
    · have hle := ih (l.erase n) (hl.erase n) (by
        intro x hx
        have hne : x ≠ n := fun he => by
          subst he; exact (List.Nodup.not_mem_erase hl) hx
        have := h x (List.mem_of_mem_erase hx)
        omega)
      rw [List.length_erase_of_mem hn] at hle
      omega
    · have hle := ih l hl (by
        intro x hx
        have := h x hx
        have hne : x ≠ n := fun he => hn (he ▸ hx)
        omega)
      omega

/-- A live chain ends within `frames.size` steps. -/
theorem CaptureLive.ends {m : Machine} {c : Option FrameId} (h : CaptureLive m c) :
    Ratchet.Denote.chainAt m c m.frames.size = Option.none := by
  apply Classical.byContradiction
  intro hne
  have hsome : ∀ i, i ≤ m.frames.size → chainAt m c i ≠ Option.none := by
    intro i hi he
    apply hne
    have := chainAt_add m c i (m.frames.size - i)
    rw [Nat.add_sub_cancel' hi, he, chainAt_none] at this
    exact this
  let l := (List.range (m.frames.size + 1)).map fun i => (chainAt m c i).getD 0
  have hmem : ∀ x ∈ l, x < m.frames.size := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    have hi' := List.mem_range.mp hi
    cases hci : chainAt m c i with
    | none => exact absurd hci (hsome i (by omega))
    | some p =>
      have := h.chain i
      rw [hci] at this
      exact this.lt
  have hnd : l.Nodup := by
    unfold List.Nodup
    rw [List.pairwise_map]
    refine List.Pairwise.imp_of_mem ?_ List.nodup_range
    intro i j hi hj hij0 heq
    apply hij0
    have hi' := List.mem_range.mp hi
    have hj' := List.mem_range.mp hj
    have hsi := hsome i (by omega)
    have hsj := hsome j (by omega)
    have hij : chainAt m c i = chainAt m c j := by
      cases hci : chainAt m c i with
      | none => exact absurd hci hsi
      | some p => cases hcj : chainAt m c j with
        | none => exact absurd hcj hsj
        | some q => simp only [hci, hcj, Option.getD_some] at heq; rw [heq]
    rcases Nat.lt_trichotomy i j with hlt | heq' | hgt
    · exfalso
      have hk := chainAt_add m c i (j - i)
      rw [Nat.add_sub_cancel' (Nat.le_of_lt hlt)] at hk
      obtain ⟨k, hk'⟩ : ∃ k, j - i = k + 1 := ⟨j - i - 1, by omega⟩
      rw [hk'] at hk
      exact (h.chain i).no_return k hsi (hk.symm.trans hij.symm)
    · exact heq'
    · exfalso
      have hk := chainAt_add m c j (i - j)
      rw [Nat.add_sub_cancel' (Nat.le_of_lt hgt)] at hk
      obtain ⟨k, hk'⟩ : ∃ k, i - j = k + 1 := ⟨i - j - 1, by omega⟩
      rw [hk'] at hk
      exact (h.chain j).no_return k hsj (hk.symm.trans hij)
  have := nodup_bound _ l hnd hmem
  simp [l] at this
  omega

/-- Fuel beyond the chain's end is irrelevant to `frameLocal.go`. -/
theorem frameLocal_go_stable {m : Machine} (x : String) :
    ∀ n fid, chainAt m (some fid) n = none → ∀ k, n ≤ k →
      frameLocal.go m x fid k = frameLocal.go m x fid n := by
  intro n
  induction n with
  | zero => intro fid h; cases h
  | succ n ih =>
    intro fid h k hk
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    simp only [frameLocal.go]
    split
    · rfl
    · cases hc : (m.frames.getD fid default).captured with
      | none => rfl
      | some p =>
        simp only []
        apply ih p _ k (by omega)
        change chainAt m (capStep m (some fid)) n = Option.none at h
        simpa only [capStep, hc] using h

theorem frameLocal_go_fuel {m : Machine} {fid : FrameId} (h : CaptureLive m (some fid))
    (x : String) (k : Nat) (hk : m.frames.size ≤ k) :
    frameLocal.go m x fid k = frameLocal.go m x fid m.frames.size :=
  frameLocal_go_stable x _ fid h.ends k hk

#print axioms CaptureLive.ends
#print axioms frameLocal_go_fuel
end Ratchet.Denote
