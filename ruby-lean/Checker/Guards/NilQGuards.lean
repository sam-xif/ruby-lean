import Checker.Guards.IsAGuards

/-! Guards for general `nil?` narrowing (`DJudge.ifNilQuery`). -/
namespace Checker

/-- A leaf whose `nil?` is the native row and whose values are all nil or all non-nil. -/
def nilLeafB (κ : Ctx) (τ : Ty) : Bool :=
  match τ with
  | .int | .float | .sym | .nilT => true
  | .cls "String" => isANoOk κ.wholeCls (["String", "Comparable"] ++ rootAncestors)
  | .inst n _ =>
    match clsGet? κ.classes n with
    | some c => !c.isModule && noDeclaredSelectorB κ.classes n "nil?"
    | none => false
  | _ => false

def nilRecvB (κ : Ctx) : Ty → Bool
  | .union σ τ => nilRecvB κ σ && nilRecvB κ τ
  | .nilable ρ => nilRecvB κ ρ
  | τ => nilLeafB κ τ

/-- The nil members of an admitted receiver type. Sharper than `isNilTy`, which must keep
nominal types because it is also used where `nil` may inhabit them. -/
def nilYesTy : Ty → Ty
  | .nilT => .nilT
  | .nilable _ => .nilT
  | .union σ τ => joinT (nilYesTy σ) (nilYesTy τ)
  | _ => .never

def ifNilQB (κ : Ctx) (ρ : Ty) : Bool :=
  nilRecvB κ ρ && nameFreeN κ "nil?" && !isAliasTy (nilYesTy ρ) && !isAliasTy (nonNilTy ρ)

end Checker
