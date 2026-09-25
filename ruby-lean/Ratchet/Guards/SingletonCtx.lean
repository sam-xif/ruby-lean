import Ratchet.Guards.ClassHeader

/-! Publication of an executed singleton definition; no body annotation is certified here. -/
set_option autoImplicit false
namespace Ratchet

def classWithSingleton (c : Cls) (d : Defn) : Cls := { c with smethods := d :: c.smethods }

def singletonDeclCtx (κ : Ctx) (c : Cls) (d : Defn) : Ctx :=
  { reserveNameCtx κ d.name with
    pos := { κ.pos with classes := classWithSingleton c d :: κ.classes } }

/-- Sufficient freshness across singleton tables; instance selectors may coincide. -/
def singletonFreshB (C : CTable) (d : Defn) : Bool :=
  C.all fun c => c.smethods.all fun prev => prev.name != d.name

theorem singletonFreshB_sound {C : CTable} {d : Defn} (hf : singletonFreshB C d = true) :
    ∀ c ∈ C, ∀ prev ∈ c.smethods, prev.name ≠ d.name := by
  intro c hc prev hp
  exact bne_iff_ne.mp (List.all_eq_true.mp (List.all_eq_true.mp hf c hc) prev hp)

def singletonTableFrameB (C : CTable) (c : Cls) (d : Defn) : Bool :=
  declLookupFrameB C (classWithSingleton c d :: C)

end Ratchet
