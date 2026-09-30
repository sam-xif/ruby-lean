import Denote.Clink.Registry
import Denote.Clink.GateStatus

namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

#eval IO.println s!"CLINK REBUILD: {dRegisteredRules.length} certified, {dGatedRules.length} gated, {dAllRules.length} total"
#eval IO.println s!"  enabled: {String.intercalate ", " dRegisteredRules}"

-- A real model-safety witness, alongside the fixture-only registration controls.
theorem rebuilt_int_safe {m : Machine} (hm : StateOk ctx0 [] .ivar0 m) :
    StuckFree m (.int 0) := dregistry_safe djudgeC_intLit hm
#print axioms rebuilt_int_safe
end Ratchet.Denote.Typed
