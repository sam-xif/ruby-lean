import Ratchet.Static.All

/-! Guards for general `is_a?` narrowing (`DJudge.ifIsA`). The branch types are
`isATy`/`notATy`; these say which receivers dispatch the native test and which names are
classes the context can resolve. -/
namespace Ratchet

/-- A scalar builtin type whose chain the context leaves alone: its values have exactly
that class, so the native test's answer is the static chain's. -/
def isALeafB (W : CTable) (τ : Ty) : Bool :=
  match τ with
  | .int | .float | .nilT | .sym | .cls "String" =>
    match builtinAncestors τ with
    | some ch => isANoOk W ch
    | none => false
  | _ => false

/-- Receivers the rule admits: leaves, and unions/nilables of admitted receivers. -/
def isARecvB (W : CTable) : Ty → Bool
  | .union σ τ => isARecvB W σ && isARecvB W τ
  | .nilable ρ => isARecvB W ρ && isALeafB W .nilT
  | τ => isALeafB W τ

/-- The tested name is a class the machine resolves: a core chain name the context has not
rebound, or a declared class. -/
def isAClassB (κ : Ctx) (cn : String) : Bool :=
  coreChainNames.contains cn || κ.classes.any (fun c => c.name == cn)

/-- Everything `DJudge.ifIsA` asks of the context, receiver type and tested name. -/
def ifIsAB (κ : Ctx) (ρ : Ty) (cn : String) : Bool :=
  isARecvB κ.wholeCls ρ && isAClassB κ cn && coreConstFreeN κ && !κ.boundConsts.contains cn &&
    nameFreeN κ "is_a?" &&
    FirstOrder (isATy κ.classes κ.wholeCls cn ρ) && !isAliasTy (isATy κ.classes κ.wholeCls cn ρ) &&
    FirstOrder (notATy κ.classes κ.wholeCls cn ρ) && !isAliasTy (notATy κ.classes κ.wholeCls cn ρ)

end Ratchet
