import Ratchet.MemberFrame
import Denote.Sem.MethodHeap

/-! Discharge definition freshness by actual heap owner, using named ancestry conformance. -/
set_option autoImplicit false
namespace Ratchet.Denote
open RubyCore Ratchet

theorem classApartB_ne {κ : Ctx} {m : Machine} {c : Cls} {dn : String} {k j : ObjId}
    (hd : DeclClassOk κ m) (hc : c ∈ κ.classes) (hk : classNamed? m.heap c.name = some k)
    (hj : classNamed? m.heap dn = some j) (hfront : classFrontB m.heap k = true)
    (ha : classApartB κ.classes κ.wholeCls c.name dn = true) : k ≠ j := by
  intro he
  subst j
  simp only [classApartB, Bool.and_eq_true] at ha
  obtain ⟨hmix, ha⟩ := ha
  cases hch : Ratchet.ancestors? κ.classes c.name with
  | none => simp [hch] at ha
  | some ch =>
    have hnot : dn ∉ ch ++ rootAncestors := by simpa [hch] using ha
    obtain ⟨rest, hrest⟩ := classFrontB_sound hfront
    have hm := (hd c hc k hk).2.2.2.2.2 ch hch hmix
    exact hnot (hm.2 dn k hj (by simp [hrest]))

theorem memberFreshB_sound {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine}
    {c : Cls} {d : Defn} {k : ObjId} (hm : StateOk κ Γ I m)
    (hc : c ∈ κ.classes) (hk : classNamed? m.heap c.name = some k)
    (hf : memberFreshB κ c d = true) :
    ∀ old ∈ κ.classes, classNamed? m.heap old.name = some k →
      ∀ prev ∈ old.methods, prev.name ≠ d.name := by
  intro old hold holdk prev hp
  simp only [memberFreshB, Bool.and_eq_true] at hf
  have hrow := List.all_eq_true.mp hf.1 old hold
  simp only [Bool.or_eq_true] at hrow
  rcases hrow with (hf | ha) | ha
  · have h := List.all_eq_true.mp hf prev hp
    simpa using h
  · obtain ⟨j, site⟩ := hm.classSites.of_class hc
    have he := Option.some.inj (site.named.symm.trans hk)
    subst j
    exact False.elim ((classApartB_ne hm.declCls hc hk holdk site.front ha) rfl)
  · obtain ⟨j, site⟩ := hm.classSites.of_class hold
    have he := Option.some.inj (site.named.symm.trans holdk)
    subst j
    exact False.elim ((classApartB_ne hm.declCls hold holdk hk site.front ha) rfl)

theorem declared_not_object {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine}
    {cn : String} {k : ObjId} (hm : StateOk κ Γ I m)
    (hk : classNamed? m.heap cn = some k) (hn : cn ∉ rootAncestors) : k ≠ Boot.objectId := by
  intro he
  subst k
  exact hn (hm.core.rootNames.only cn Boot.objectId hk (by decide))

#print axioms memberFreshB_sound
end Ratchet.Denote
