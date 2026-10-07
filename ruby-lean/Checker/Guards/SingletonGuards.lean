import Checker.Guards.ClassGuards
import Checker.Guards.SingletonCtx

/-! Decidable publication guards; body checking is a separate judgment premise. -/
namespace Checker

def singletonRuleB (κ : Ctx) (Γ : Env) (I : Ty) (c : Cls) (d : Defn) : Bool :=
  reframeTypesB κ I && localTypesB Γ &&
    decide (κ.asms = [] ∧ κ.scope.runtimeClass = some c.name ∧
      κ.selfTy = some (.clsOf c.name) ∧ "new" ≠ d.name ∧ "method_missing" ≠ d.name ∧
      "method_added" ≠ d.name ∧ "initialize" ≠ d.name) &&
    !classHookSelectors.contains d.name && unqualifiedClassB c.name && singletonFreshB κ.classes d && singletonTableFrameB κ.classes c d

end Checker
