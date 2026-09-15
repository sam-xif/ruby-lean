import Denote.Den

/-! The heap observations sufficient to preserve first-order types. Allocation,
registration, and initialization prove these facts differently; the type induction is shared.
This is a preservation contract, not a typing judgment or a certificate admission route. -/
set_option autoImplicit false
namespace Ratchet.Denote
open RubyCore Ratchet

structure DataPres (h h' : Heap) : Prop where
  nominal : ∀ v cn, isAName h v cn = true → isAName h' v cn = true
  named : ∀ cn k, classNamed? h cn = some k → classNamed? h' cn = some k
  exactInst : ∀ v cn, isExactInst h v cn = true →
    isExactInst h' v cn = true ∧ ivarOf h' v = ivarOf h v
  array : ∀ v xs, arrElems? h v = some xs → arrElems? h' v = some xs
  hash : ∀ v es, hshEntries? h v = some es → hshEntries? h' v = some es

theorem DataPres.denM_aux {m n : Machine} (hp : DataPres m.heap n.heap) :
    ∀ τ : Ty, FirstOrder τ = true →
    (∀ v, denM τ m v → denM τ n v) ∧
    (∀ seen g, denSpineFrom seen τ m g → denSpineFrom seen τ n g) := by
  intro τ
  induction τ with
  | int | bool | nilT | sym | float | any | never =>
    intro _
    exact ⟨fun _ hv => by rwa [denM] at hv ⊢,
      fun _ _ hv => absurd hv (by simp [denSpineFrom])⟩
  | ivar0 =>
    intro _
    exact ⟨fun _ hv => absurd hv (by simp [denM]), fun _ _ _ => by simp [denSpineFrom]⟩
  | cls cn =>
    intro _
    exact ⟨fun v hv => by rw [denM] at hv ⊢; exact hp.nominal v cn hv,
      fun _ _ hv => absurd hv (by simp [denSpineFrom])⟩
  | clsOf cn =>
    intro _
    refine ⟨fun v hv => ?_, fun _ _ hv => absurd hv (by simp [denSpineFrom])⟩
    simp only [denM, isClassRefNamed] at hv ⊢
    cases hn : classNamed? m.heap cn with
    | none => rw [hn] at hv; cases v <;> simp_all
    | some k => rw [hp.named cn k hn]; simpa only [hn] using hv
  | nilable τ ih =>
    intro hf
    exact ⟨fun _ hv => by rw [denM] at hv ⊢; exact hv.imp id ((ih hf).1 _),
      fun _ _ hv => absurd hv (by simp [denSpineFrom])⟩
  | union σ τ ihσ ihτ =>
    intro hf
    simp only [FirstOrder, Bool.and_eq_true] at hf
    exact ⟨fun _ hv => by rw [denM] at hv ⊢; exact hv.imp ((ihσ hf.1).1 _) ((ihτ hf.2).1 _),
      fun _ _ hv => absurd hv (by simp [denSpineFrom])⟩
  | sameAs x τ ih =>
    intro hf
    exact ⟨fun _ hv => by rw [denM] at hv ⊢; exact (ih hf).1 _ hv,
      fun _ _ hv => absurd hv (by simp [denSpineFrom])⟩
  | arrayOf τ ih =>
    intro hf
    refine ⟨fun v hv => ?_, fun _ _ hv => absurd hv (by simp [denSpineFrom])⟩
    rw [denM] at hv ⊢
    obtain ⟨xs, hx, hall⟩ := hv
    exact ⟨xs, hp.array v xs hx, fun x hxs => (ih hf).1 x (hall x hxs)⟩
  | hashOf k w ihk ihw =>
    intro hf
    simp only [FirstOrder, Bool.and_eq_true] at hf
    refine ⟨fun v hv => ?_, fun _ _ hv => absurd hv (by simp [denSpineFrom])⟩
    rw [denM] at hv ⊢
    obtain ⟨es, hx, hall⟩ := hv
    exact ⟨es, hp.hash v es hx,
      fun p hp => ⟨(ihk hf.1).1 _ (hall p hp).1, (ihw hf.2).1 _ (hall p hp).2⟩⟩
  | inst cn I ih =>
    intro hf
    refine ⟨fun v hv => ?_, fun _ _ hv => absurd hv (by simp [denSpineFrom])⟩
    rw [denM] at hv ⊢
    obtain ⟨hc, hi⟩ := hp.exactInst v cn hv.1
    refine ⟨hc, ?_⟩
    rw [hi]
    exact (ih hf).2 [] _ hv.2
  | ivarCons x σ rest ihσ ihrest =>
    intro hf
    simp only [FirstOrder, Bool.and_eq_true] at hf
    refine ⟨fun _ hv => by rwa [denM] at hv ⊢, fun seen g hv => ?_⟩
    rw [denSpineFrom] at hv ⊢
    exact ⟨hv.1.imp id ((ihσ hf.1).1 _), (ihrest hf.2).2 _ g hv.2⟩
  | arrow0 _ _ | arrowCons _ _ _ _ | clos _ _ _ _ _ =>
    intro hf; cases hf

theorem DataPres.denM {m n : Machine} (hp : DataPres m.heap n.heap) {τ : Ty}
    (hf : FirstOrder τ = true) {v : Value} (hv : denM τ m v) : denM τ n v :=
  (hp.denM_aux τ hf).1 v hv

#print axioms DataPres.denM
end Ratchet.Denote
