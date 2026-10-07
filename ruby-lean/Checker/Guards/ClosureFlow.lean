import Checker.Static.LocalFacts
import Checker.Static.All

/-! Decidable activation/return obligations for current-frame lambda calls.
Capture origins and body certificates are checked separately; these guards grant neither. -/
namespace Checker

def procCallNameB (name : String) : Bool := name == "call" || name == "[]"

def activationStableB (τ : Ty) : Bool :=
  FirstOrder τ || match τ with
    | .clos _ .ivar0 .never => true
    | _ => false

def activationEnvB (Γ : Env) : Bool :=
  Γ.all (fun p => activationStableB p.2 && !isAliasTy p.2)

/-- Returning captures erase aliases, including those naming body-only slots. -/
def activationReturnB (Γ : Env) : Bool :=
  Γ.all (fun p => activationStableB (stripAlias p.2))

def closureMainB (κ : Ctx) (I : Ty) : Bool :=
  κ.scope.runtimeMain && κ.pos.mainWorld && κ.scope.runtimeClass.isNone &&
    κ.asms.isEmpty && κ.selfTy.isNone && κ.blockTy.isNone && κ.consts.isEmpty && FirstOrder I

def closureBodyCtx (κ : Ctx) : Ctx := κ.withoutRuntimeScope.withFrame none

end Checker
