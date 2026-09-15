import Ratchet.ClassHeader

/-! Definition-side guards. Owner separation uses declared ancestry, not unequal names:
two names may denote one heap class, while different owners may share a method name. -/
set_option autoImplicit false
namespace Ratchet

def classApartB (C W : CTable) (cn dn : String) : Bool :=
  mixinFreeChain W rootAncestors &&
    (ancestors? C cn).any (fun ch => !(ch ++ rootAncestors).contains dn)

def memberFreshB (κ : Ctx) (c : Cls) (d : Defn) : Bool :=
  κ.classes.all fun old => old.methods.all (fun prev => prev.name != d.name) ||
    classApartB κ.classes κ.wholeCls c.name old.name ||
    classApartB κ.classes κ.wholeCls old.name c.name

def memberTableFrameB (C : CTable) (c : Cls) (d : Defn) : Bool :=
  declLookupFrameB C (classWithMethod c d :: C)

end Ratchet
