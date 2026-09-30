import Denote.Bridge.Literal
import Denote.Clink.GateStatus

namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

#eval IO.println s!"CLINK REBUILD: {dRegisteredRules.length} certified, {dGatedRules.length} gated, {dAllRules.length} total"
#eval IO.println s!"  enabled: {String.intercalate ", " dRegisteredRules}"

-- These controls follow the active profile rather than pinning every literal on.
-- Disabling an optional literal must remove its acceptance and its clink reference.
#guard validateActiveLiteralD (.int 7) (.intLit 7) == clinkEnabled "intLit"
#guard validateActiveLiteralD (.flt 0) (.fltLit 0) == clinkEnabled "fltLit"
#guard validateActiveLiteralD (.str "ok") (.strLit "ok") == clinkEnabled "strLit"
#guard validateActiveLiteralD (.sym "ok") (.symLit "ok") == clinkEnabled "symLit"
#guard validateActiveLiteralD .tru .truLit == clinkEnabled "truLit"
#guard validateActiveLiteralD .fls .flsLit == clinkEnabled "flsLit"
#guard validateActiveLiteralD .nil .nilLit == clinkEnabled "nilLit"
#guard !validateActiveLiteralD (.int 7) (.intLit 8)
#guard !validateActiveLiteralD (.int 7) (.flow (.intLit 7))
#guard !validateActiveLiteralD (.seq [.int 7]) (.seq [.intLit 7])

-- A real model-safety witness, alongside the fixture-only registration controls.
theorem rebuilt_int_safe {m : Machine} (hm : StateOk ctx0 [] .ivar0 m) :
    StuckFree m (.int 0) := validateActiveLiteralD_safe (by decide :
      validateActiveLiteralD (.int 0) (.intLit 0) = true) hm
#print axioms rebuilt_int_safe

-- The subset bridge reaches the exact executable runner used by the full gate.
theorem rebuilt_int_safe_run (hb : bootOkB = true) (fuel : Nat) :
    Semantics.typeStuck (Semantics.run fuel (toRuby (.int 0))) = false :=
  validateActiveLiteralD_safe_run (by decide :
    validateActiveLiteralD (.int 0) (.intLit 0) = true) hb fuel
#print axioms rebuilt_int_safe_run
#print axioms validateActiveLiteralD_safe_run
end Ratchet.Denote.Typed
