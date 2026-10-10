import Books.TypeSoundness.Checker.Lang.Ty

/-! The environment inside a desugared `x && c`: after `t = x`, both names refined to `ρ`. -/
namespace Checker

def aliasEnv (Γ : Env) (x t : String) (σ : Ty) : Env :=
  envSet (killClosOver (killAliasesTo Γ t) t σ) t (.sameAs x σ)

def andEnv (Γ : Env) (x t : String) (σ ρ : Ty) : Env :=
  envSet (envSet (aliasEnv Γ x t σ) x ρ) t (.sameAs x ρ)

end Checker
