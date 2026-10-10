import Books.TypeSoundness.Rules.Method.MethodEntry
import Books.TypeSoundness.Conformance.Core.Boot
import Books.TypeSoundness.Checker.Check.Check

/-! Ordinary code metadata must exclude the for callback's alternate binding path. -/
namespace Checker.Soundness.Typed
open RubyCore Checker.Soundness

private def retargetedMethod : MethodDef :=
  { params := [.req "y"], owner := Boot.objectId,
    body := .send (some (.var .lvar "y")) "+" [.int 1] .none,
    fromBlock := true, forTargets := some [(.lvar, "z"), (.lvar, "y")],
    forMultiple := true }

-- Retain the old guard as the counterexample's independently evaluated premise.
private def legacyCodeB (md : MethodDef) : Bool :=
  decide (md.owner = Boot.objectId ∧ md.cref = [] ∧ md.superName = none ∧
    md.builtin = none ∧ md.capturedFrame = none ∧ md.declared = [] ∧
    md.fromPrelude = false ∧ md.visibilityOnly = false)

#guard legacyCodeB retargetedMethod
#guard !ordinaryMethodCodeB Boot.objectId [] retargetedMethod
#guard !ordinaryMethodCodeB Boot.objectId [] { retargetedMethod with fromBlock := false }
#guard !ordinaryMethodCodeB Boot.objectId [] { retargetedMethod with forTargets := none }
#guard ordinaryMethodCodeB Boot.objectId []
  { retargetedMethod with fromBlock := false, forTargets := none }
#guard (Checker.check 100 [("y", .int)]
  (.send (some (.var .lvar "y")) "+" [.int 1] none)
  (.prim (.var .lvar "y") "+" [.intLit 1] .int .int)).isSome
#guard match Interp.enterUserMethod bootMachine bootMachine.currentFrame.self
    "bump" retargetedMethod [.int 7] none with
  | .next n => Semantics.typeStuck (Interp.run 200 n)
  | _ => false
end Checker.Soundness.Typed
