import Ratchet.Guards.ClassHeader

/-! Definition-side guards. Owner separation uses declared ancestry, not unequal names:
two names may denote one heap class, while different owners may share a method name. -/
set_option autoImplicit false
namespace Ratchet

def classApartB (C W : CTable) (cn dn : String) : Bool :=
  mixinFreeChain W rootAncestors &&
    (ancestors? C cn).any (fun ch => !(ch ++ rootAncestors).contains dn)

/-- Updating one name's bound must cover every alias to that heap owner. This sufficient
guard proves that any declared alias has the same name, using ancestry in either direction. -/
def memberOwnersB (κ : Ctx) (c : Cls) : Bool :=
  κ.classes.all fun old => old.name == c.name ||
    classApartB κ.classes κ.wholeCls c.name old.name ||
    classApartB κ.classes κ.wholeCls old.name c.name

def memberFreshB (κ : Ctx) (c : Cls) (d : Defn) : Bool :=
  (κ.classes.all fun old => old.methods.all (fun prev => prev.name != d.name) ||
    classApartB κ.classes κ.wholeCls c.name old.name ||
    classApartB κ.classes κ.wholeCls old.name c.name) && memberOwnersB κ c

theorem memberFreshB_owners {κ : Ctx} {c : Cls} {d : Defn}
    (h : memberFreshB κ c d = true) : memberOwnersB κ c = true := by
  simp only [memberFreshB, Bool.and_eq_true] at h
  exact h.2

def memberTableFrameB (C : CTable) (c : Cls) (d : Defn) : Bool :=
  declLookupFrameB C (classWithMethod c d :: C)

end Ratchet
