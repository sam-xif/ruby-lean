import Ratchet.Guards.WriteTypes

/-! Each value-sensitive conformance component must be covered by the write guard. -/
namespace Ratchet.WriteControl
private def snapshot : Ty := .inst "Point" (.ivarCons "@x" .nilT .ivar0)
private def ctx : Ctx := { ctx0 with scope := { ctx0.scope with
  selfTy := some (.inst "Point" .ivar0), runtimeMain := false } }

#guard writeTypesB ctx [("v", .int)] .ivar0 "@x" .int
#guard writeTypesB ctx [("items", .arrayOf (.nilable (.cls "String")))] .ivar0
  "@items" (.arrayOf (.nilable (.cls "String")))
#guard IvarStable (.hashOf (.cls "String") (.arrayOf (.inst "Point" .ivar0)))
#guard !IvarStable snapshot
#guard !IvarStable (.arrayOf snapshot)
#guard !IvarStable (.hashOf .sym (.nilable snapshot))

-- Assigned value, retained locals, and retained fields are independent obligations.
#guard !writeTypesB ctx [] .ivar0 "@x" snapshot
#guard !writeTypesB ctx [("saved", .arrayOf snapshot)] .ivar0 "@x" .int
#guard !writeTypesB ctx [] (.ivarCons "@saved" snapshot .ivar0) "@x" .int
#guard writeTypesB ctx [] (.ivarCons "@saved" snapshot .ivar0) "@saved" .int

#guard !writeTypesB { ctx with scope := { ctx.scope with selfTy := some snapshot } }
  [] .ivar0 "@x" .int
#guard !writeTypesB { ctx with scope := { ctx.scope with blockTy := some snapshot } }
  [] .ivar0 "@x" .int
#guard !writeTypesB { ctx with pos := { ctx.pos with consts := [("::SAVED", snapshot)] } }
  [] .ivar0 "@x" .int
#guard writeTypesB { ctx with
    scope := { ctx.scope with blockTy := some (.arrayOf .int) },
    pos := { ctx.pos with consts := [("::SAVED", .nilable (.cls "String"))] } }
  [] .ivar0 "@x" .int

-- First-visible field lookup, not a scan requiring hidden duplicates to hold.
#guard writeTypesB ctx [] (.ivarCons "@saved" .int (.ivarCons "@saved" snapshot .ivar0)) "@x" .int
#guard !writeTypesB ctx [] (.ivarCons "@saved" snapshot (.ivarCons "@saved" .int .ivar0)) "@x" .int
end Ratchet.WriteControl
