import Ratchet.Guards.ClassGuards

/-! Top-level constant assignment, first fragment: one constant, no classes yet, a value
type with no class-valued inhabitants. The core class names are never rebound. -/
namespace Ratchet

def constAddCtx (κ : Ctx) (n : String) (τ : Ty) : Ctx :=
  { κ with pos := { κ.pos with consts := envSet κ.pos.consts (constKey n) τ
                               globalConsts := n :: κ.pos.globalConsts } }

/-- Value types whose inhabitants are never classes. -/
def constValTyB : Ty → Bool
  | .int | .float | .sym | .bool | .nilT | .arrayOf _ | .hashOf _ _ => true
  | _ => false

/-- Names the builtin/exception `.const` rules read; a constant must not rebind them. -/
def reservedConstNames : List String :=
  ["Integer", "Float", "String", "Symbol", "NilClass", "TrueClass", "FalseClass", "Array",
   "Hash", "StandardError", "RuntimeError", "ArgumentError", "TypeError", "NameError",
   "NoMethodError", "ZeroDivisionError", "IndexError", "KeyError", "RangeError",
   "IOError", "FrozenError", "NotImplementedError"]

def casgnTopB (κ : Ctx) (Γ : Env) (I τ : Ty) (n : String) : Bool :=
  constValTyB τ && FirstOrder τ && localTypesB Γ && reframeTypesB κ I &&
    decide (κ.asms = [] ∧ κ.scope.runtimeMain = true ∧ κ.frame = none ∧
      κ.scope.runtimeClass = none ∧ κ.selfTy = none ∧ κ.blockTy = none ∧
      κ.classes = [] ∧ κ.consts = [] ∧ n ∉ κ.pos.globalConsts ∧
      n ∉ reservedConstNames ∧ ':' ∉ n.toList)

end Ratchet
