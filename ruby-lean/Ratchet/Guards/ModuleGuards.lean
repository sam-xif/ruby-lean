import Ratchet.Guards.ClassGuards
import Ratchet.Guards.ModuleHeader

/-! Static module entry/return guards. Method bodies and signatures remain separate
proof obligations; this guard publishes no future method or allocator capability. -/
namespace Ratchet

def moduleRuleB (κ κb : Ctx) (Γ : Env) (I τ : Ty) (name : String) : Bool :=
  reframeTypesB (returnScopeCtx κ κb) I && localTypesB Γ && FirstOrder τ &&
    decide (κ.asms = [] ∧ κ.scope.runtimeMain = true ∧ κ.frame = none ∧
      κb.pos.mainWorld = true ∧ κ.scope.runtimeClass = none ∧
      κb.scope.runtimeClass = some name ∧ κb.consts = []) &&
    plainClassTablesB κ && classNativeFrameB κ name && freshClassNameB κ name && !name.isEmpty &&
    unqualifiedClassB name && moduleHeaderFrameB κ.classes name

end Ratchet
