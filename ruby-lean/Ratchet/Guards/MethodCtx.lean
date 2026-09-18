import Ratchet.Static.All

/-! State descriptions for ordinary top-level method installation. Reserving a name is
negative information only; `topDeclCtx` additionally records the installed definition. -/
namespace Ratchet

def reserveNameCtx (κ : Ctx) (name : String) : Ctx :=
  { κ with neg := { κ.neg with declared := name :: κ.declared } }

def topDeclCtx (κ : Ctx) (d : Defn) : Ctx :=
  { reserveNameCtx κ d.name with pos := { κ.pos with defs := d :: κ.defs } }

def topBodyCtx (κ : Ctx) (d : Defn) : Ctx :=
  (topDeclCtx κ d).withFrame (some ⟨"Object", "Object", d.name⟩)

end Ratchet
