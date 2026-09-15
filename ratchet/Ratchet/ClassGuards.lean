import Ratchet.MemberFrame
import Ratchet.NativeGuards

/-! Pure constructor-rule guards. Their semantic interpretation lives in Denote. -/
namespace Ratchet

def reframeTypesB (κ : Ctx) (I : Ty) : Bool :=
  FirstOrder I && κ.selfTy.all FirstOrder && κ.blockTy.all FirstOrder &&
    κ.consts.all (fun p => FirstOrder p.2)
def localTypesB (Γ : Env) : Bool := Γ.all (fun p => FirstOrder (stripAlias p.2))
def plainClassTablesB (κ : Ctx) : Bool :=
  κ.consts.isEmpty && κ.classes.all (fun c => unqualifiedClassB c.name)
def explicitReceiverB : Expr → Bool | .self' => false | _ => true

def classRuleB (κ κb : Ctx) (Γ : Env) (I τ : Ty) (cn : String) : Bool :=
  reframeTypesB (returnScopeCtx κ κb) I && localTypesB Γ && FirstOrder τ &&
    decide (κ.asms = [] ∧ κ.scope.runtimeMain = true ∧ κ.frame = none ∧
      κ.pos.mainWorld = true ∧ κb.pos.mainWorld = true ∧ κ.scope.runtimeClass = none ∧
      κb.scope.runtimeClass = some cn ∧ κb.consts = []) &&
    plainClassTablesB κ && classNativeFrameB κ cn && freshClassNameB κ cn && !cn.isEmpty &&
    nameFreeN κ "new" && classNativeQuietB cn "new" && unqualifiedClassB cn &&
    headerTableFrameB κ.classes cn

def memberRuleB (κ : Ctx) (Γ : Env) (I : Ty) (c : Cls) (d : Defn) : Bool :=
  reframeTypesB κ I && localTypesB Γ &&
    decide (κ.asms = [] ∧ κ.scope.runtimeClass = some c.name ∧ c.name ∉ rootAncestors ∧
      "new" ≠ d.name ∧ "method_missing" ≠ d.name ∧ "method_added" ≠ d.name) &&
    unqualifiedClassB c.name && memberFreshB κ c d && memberTableFrameB κ.classes c d

def mainCallB (κ : Ctx) (Γ : Env) (I : Ty) : Bool :=
  reframeTypesB κ I && localTypesB Γ &&
    decide (κ.asms = [] ∧ κ.scope.runtimeMain = true ∧ κ.pos.mainWorld = true ∧
      κ.scope.runtimeClass = none ∧ κ.consts = [])

end Ratchet
