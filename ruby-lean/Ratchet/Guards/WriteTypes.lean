import Ratchet.Static.All

/-! Checkable sufficient conditions for preserving typed data through an ivar write.
Instance snapshots with fields are deliberately not stable; nominal instances with an
empty spine are. These are type predicates, not expression-typing judgments.
-/
set_option autoImplicit false
namespace Ratchet

def IvarStable : Ty → Bool
  | .arrow0 _ | .arrowCons .. | .clos .. => false
  | .inst _ .ivar0 => true
  | .inst .. => false
  | .nilable τ | .arrayOf τ | .sameAs _ τ => IvarStable τ
  | .union σ τ | .hashOf σ τ | .ivarCons _ σ τ => IvarStable σ && IvarStable τ
  | _ => true

/-- Read through first-visible lookup, so hidden duplicate field types impose nothing. -/
def writeFieldsB (I : Ty) (x : String) : Bool :=
  (spineKeys I).all fun y => y == x || ((ivarGet? I y).map IvarStable).getD false

def writeTypesB (κ : Ctx) (Γ : Env) (I : Ty) (x : String) (ρ : Ty) : Bool :=
  IvarStable ρ && Γ.all (fun p => IvarStable (stripAlias p.2)) && writeFieldsB I x &&
    κ.selfTy.all IvarStable && κ.blockTy.all IvarStable && κ.consts.all (fun p => IvarStable p.2)

theorem ivarGet?_key {I τ : Ty} {x : String} (h : ivarGet? I x = some τ) : x ∈ spineKeys I := by
  induction I with
  | ivarCons y σ rest _ ih =>
    simp only [ivarGet?] at h
    split at h
    · rename_i he
      have he : y = x := beq_iff_eq.mp he
      simp [spineKeys, he]
    · exact List.mem_cons_of_mem _ (ih h)
  | _ => simp [ivarGet?] at h

theorem writeFieldsB_get {I τ : Ty} {x y : String} (h : writeFieldsB I x = true)
    (hne : y ≠ x) (hg : ivarGet? I y = some τ) : IvarStable τ = true := by
  have ht := List.all_eq_true.mp h y (ivarGet?_key hg)
  simpa only [beq_eq_false_iff_ne.mpr hne, Bool.false_or, hg, Option.map_some, Option.getD_some] using ht

structure WriteTypes (κ : Ctx) (Γ : Env) (I : Ty) (x : String) (ρ : Ty) : Prop where
  value : IvarStable ρ = true
  locals : ∀ p ∈ Γ, IvarStable (stripAlias p.2) = true
  fields : ∀ y τ, y ≠ x → ivarGet? I y = some τ → IvarStable τ = true
  self : ∀ τ, κ.selfTy = some τ → IvarStable τ = true
  block : ∀ τ, κ.blockTy = some τ → IvarStable τ = true
  consts : ∀ p ∈ κ.consts, IvarStable p.2 = true

theorem writeTypesB_sound {κ : Ctx} {Γ : Env} {I ρ : Ty} {x : String}
    (h : writeTypesB κ Γ I x ρ = true) : WriteTypes κ Γ I x ρ := by
  simp only [writeTypesB, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hv, he⟩, hi⟩, hs⟩, hb⟩, hc⟩ := h
  refine ⟨hv, he, fun y τ hne hg => writeFieldsB_get hi hne hg, ?_, ?_, hc⟩
  · intro τ ht; simpa only [ht, Option.all_some] using hs
  · intro τ ht; simpa only [ht, Option.all_some] using hb

end Ratchet
