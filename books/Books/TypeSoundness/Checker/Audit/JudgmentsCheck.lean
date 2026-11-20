import Books.TypeSoundness.Checker.Audit.Derive
import Books.TypeSoundness.Checker.Audit.Judgments

/-!
# The written-out traced judgments are the derived ones

`Judgments.lean` is generated source (`Generate.lean`), so that the checker's
executable does not import Lean's metaprogramming library. This module re-derives
every traced judgment with the metaprogram in `Derive.lean` and fails the build
unless each declaration in `Judgments.lean` has exactly the derived type: the same
families, the same constructors in the same order, and each constructor's type
definitionally equal to the derived one.
-/
open Lean Meta Elab Command
namespace Checker.Audit

elab "#check_audit_judgments" : command => liftTermElabM do
  for raw in families do
    let rawInfo ← getConstInfoInduct raw
    let info ← getConstInfoInduct (auditName raw)
    unless ← isDefEq info.type (mkForall `used .implicit traceTy rawInfo.type) do
      throwError "{auditName raw}: its type is not the derived one"
    unless info.ctors == rawInfo.ctors.map auditName do
      throwError "{auditName raw}: its constructors are not the derived ones"
    for c in rawInfo.ctors do
      let derived ← traceConstructor (← getConstInfoCtor c).type (ruleName c)
      unless ← isDefEq (← getConstInfoCtor (auditName c)).type derived do
        throwError "{auditName c}: its type is not the derived one; run `make gen`"
  logInfo m!"{families.length} traced judgments match their derivation"

/-- info: 17 traced judgments match their derivation -/
#guard_msgs in
#check_audit_judgments

end Checker.Audit
