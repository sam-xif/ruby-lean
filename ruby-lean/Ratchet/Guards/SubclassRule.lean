import Ratchet.Guards.ClassGuards
import Ratchet.Guards.SubclassGuards
import Ratchet.Guards.SubclassHeader

/-! Pure side conditions for a subclass body, evaluated after its superclass expression.
Method-body admission remains a separate judgment/cache obligation. -/
namespace Ratchet

def subclassRuleB (κ κb : Ctx) (Γ : Env) (I τ : Ty) (name parent : String) : Bool :=
  reframeTypesB (returnScopeCtx κ κb) I && localTypesB Γ && FirstOrder τ &&
    decide (κ.asms = [] ∧ κ.scope.runtimeMain = true ∧ κ.frame = none ∧
      κb.pos.mainWorld = true ∧ κ.scope.runtimeClass = none ∧
      κb.scope.runtimeClass = some name ∧ κb.consts = []) &&
    plainClassTablesB κ && classNativeFrameB κ name && freshClassNameB κ name && !name.isEmpty &&
    subclassBaseFrameB κ parent && κ.pos.plainAlloc.contains parent && classNativeQuietB name "new" &&
    (smroGet? κ.classes parent "new").isNone && subclassHeaderFrameB κ.classes name parent &&
    unqualifiedClassB name

end Ratchet
