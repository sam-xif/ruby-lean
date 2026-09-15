import Ratchet.MemberFrame

/-! Bounds on a declared class's own selectors. Retained records are history, so the
bound is their union, not merely the most recent record or the global name reservation. -/
set_option autoImplicit false
namespace Ratchet

def ownNames (C : CTable) (cn : String) : List String :=
  C.flatMap fun c => if c.name = cn then c.methods.map (·.name) else []

@[simp] theorem mem_ownNames {C : CTable} {cn name : String} :
    name ∈ ownNames C cn ↔ ∃ c ∈ C, c.name = cn ∧ ∃ d ∈ c.methods, d.name = name := by
  simp only [ownNames, List.mem_flatMap]
  constructor
  · rintro ⟨c, hc, hn⟩
    split at hn
    · exact ⟨c, hc, ‹c.name = cn›, List.mem_map.mp hn⟩
    · cases hn
  · rintro ⟨c, hc, he, hd⟩
    exact ⟨c, hc, by rw [if_pos he]; exact List.mem_map.mpr hd⟩

theorem ownNames_cons_mono (c : Cls) {C : CTable} {cn name : String}
    (h : name ∈ ownNames C cn) : name ∈ ownNames (c :: C) cn := by
  obtain ⟨old, ho, he, hd⟩ := mem_ownNames.mp h
  exact mem_ownNames.mpr ⟨old, List.mem_cons_of_mem c ho, he, hd⟩

theorem ownNames_publish (C : CTable) (c : Cls) (d : Defn) :
    d.name ∈ ownNames (classWithMethod c d :: C) c.name :=
  mem_ownNames.mpr ⟨classWithMethod c d, List.mem_cons_self, rfl,
    d, List.mem_cons_self, rfl⟩

/-- Updating one name's bound must cover every alias to that heap owner. This sufficient
guard proves that any declared alias has the same name, using ancestry in either direction. -/
def memberOwnersB (κ : Ctx) (c : Cls) : Bool :=
  κ.classes.all fun old => old.name == c.name ||
    classApartB κ.classes κ.wholeCls c.name old.name ||
    classApartB κ.classes κ.wholeCls old.name c.name

end Ratchet
