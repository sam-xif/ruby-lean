import Ratchet.Static.All

/-! State descriptions for ordinary top-level method installation. Reserving a name is
negative information only; `topDeclCtx` additionally records the installed definition. -/
namespace Ratchet

/-- Native methods on main itself shadow ordinary top-level Object definitions. -/
def mainSingletonNames : List String :=
  ["define_method", "include", "inspect", "private", "public", "ruby2_keywords", "to_s", "using"]

/-- Main-native names are reserved. Existing declared owners must be separate
from Object; `new` needs additional allocator transport when classes exist. -/
def topDeclClassesB (κ : Ctx) (name : String) : Bool :=
  !mainSingletonNames.contains name && name != "singleton_method_added" &&
    (κ.classes.isEmpty || (name != "new" &&
      κ.classes.all (fun c => !rootAncestors.contains c.name)))

def reserveNameCtx (κ : Ctx) (name : String) : Ctx :=
  { κ with neg := { κ.neg with declared := name :: κ.declared } }

def topDeclCtx (κ : Ctx) (d : Defn) : Ctx :=
  { reserveNameCtx κ d.name with pos := { κ.pos with defs := d :: κ.defs } }

def topBodyCtx (κ : Ctx) (d : Defn) : Ctx :=
  (topDeclCtx κ d).withFrame (some ⟨"Object", "Object", d.name, false⟩)

end Ratchet
