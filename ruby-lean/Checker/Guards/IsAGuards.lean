import Checker.Static.All
import Checker.Guards.MemberRoute

/-! Guards for general `is_a?` narrowing (`DJudge.ifIsA`). The branch types are
`isATy`/`notATy`; these say which receivers dispatch the native test and which names are
classes the context can resolve. -/
namespace Checker

/-- A leaf whose values have one known class: a scalar builtin type whose chain the context
leaves alone, or an exact instance of a declared class that does not define `is_a?`. -/
def isALeafB (κ : Ctx) (τ : Ty) : Bool :=
  match τ with
  | .int | .float | .nilT | .sym | .cls "String" =>
    match builtinAncestors τ with
    | some ch => isANoOk κ.wholeCls ch
    | none => false
  | .inst n _ =>
    match clsGet? κ.classes n with
    | some c => !c.isModule && noDeclaredSelectorB κ.classes n "is_a?"
    | none => false
  | _ => false

/-- Receivers the rule admits: leaves, and unions/nilables of admitted receivers. -/
def isARecvB (κ : Ctx) : Ty → Bool
  | .union σ τ => isARecvB κ σ && isARecvB κ τ
  | .nilable ρ => isARecvB κ ρ && isALeafB κ .nilT
  | τ => isALeafB κ τ

/-- The tested name is a class the machine resolves: a core chain name the context has not
rebound, or a declared class. -/
def isAClassB (κ : Ctx) (cn : String) : Bool :=
  coreChainNames.contains cn || κ.classes.any (fun c => c.name == cn)

/-- Everything `DJudge.ifIsA` asks of the context, receiver type and tested name. -/
def ifIsAB (κ : Ctx) (ρ : Ty) (cn : String) : Bool :=
  isARecvB κ ρ && isAClassB κ cn && coreConstFreeN κ && !κ.boundConsts.contains cn &&
    nameFreeN κ "is_a?" &&
    FirstOrder (isATy κ.classes κ.wholeCls cn ρ) && !isAliasTy (isATy κ.classes κ.wholeCls cn ρ) &&
    FirstOrder (notATy κ.classes κ.wholeCls cn ρ) && !isAliasTy (notATy κ.classes κ.wholeCls cn ρ)

end Checker
