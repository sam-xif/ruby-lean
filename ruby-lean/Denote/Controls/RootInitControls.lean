import Denote.Controls.DefaultConstructorControls
import Denote.Controls.ConstructorGeneralControls

/-! Root absence is indexed by top-level declarations, not global name reservations or
other classes' methods. Existing annotation checks remain mandatory for actual definitions. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed.RootInitControls
open RubyCore Ratchet Ratchet.Denote

def topInit : Defn := ⟨"initialize", [.req "x"], .var .lvar "x"⟩
def topExpr : Ratchet.Expr := .def' topInit.name topInit.params topInit.body
def topHint (arg : Ty := .int) : Deriv := .defDecl "initialize" [("x", arg)] .int (.var .lvar "x")
def topChecked : Certified [] topExpr := (check fuelD [] topExpr topHint).get (by decide +kernel)
def reserved : Ctx := reserveNameCtx ctx0 "initialize"

#guard rootInitFreeB ctx0.defs
#guard !nameFreeN reserved "initialize" && rootInitFreeB reserved.defs
#guard !nameFreeN FlagBox.callerCtx "initialize" && rootInitFreeB FlagBox.callerCtx.defs
#guard validateD topExpr topHint
#guard !validateD topExpr (topHint (.nilable .int))
#guard !rootInitFreeB topChecked.ctx.defs

def topCall : Ratchet.Expr := .seq [topExpr, .send none "initialize" [.int 7] none]
#guard validateD topCall (.seq [topHint, .callSig "initialize" [.intLit 7] .int])
#guard !validateD topCall (.seq [topHint (.nilable .int), .callSig "initialize" [.intLit 7] .int])
#guard match Interp.run 80 (evalFrom bootMachine topCall) with
  | .value (.int 7) _ => true
  | _ => false

/-- Installing another class's annotated initializer preserves root absence, even though
the global initialize name has ceased to be free. No physical root premise is assumed. -/
theorem after_class_root (hb : bootOkB = true) {m : Machine} {fuel rest : Nat} {v : Value}
    (hr : runA fuel (evalFrom bootMachine FlagBox.program) = .ans (.val v) m rest) :
    Interp.userInit? m.heap Boot.objectId = none := by
  have hs := ((FlagBox.class_run (stateOk_boot hb)).2 fuel (.val v) m rest hr).2.2 v rfl
  exact hs.rootInit rfl

theorem after_top_definition (hb : bootOkB = true) {m : Machine} {fuel rest : Nat} {v : Value}
    (hr : runA fuel (evalFrom bootMachine topExpr) = .ans (.val v) m rest) :
    StateOk topChecked.ctx [] .ivar0 m := by
  have hs := certified_context topChecked
  have ho : topChecked.out = [] ∧ topChecked.spine = .ivar0 := by decide +kernel
  rw [ho.1, ho.2] at hs
  exact ((hs bootMachine (stateOk_boot hb)).2 fuel (.val v) m rest hr).2.2 v rfl

-- Top-level initialize is legal, but deleting its declaration cannot re-enable default new.
#guard match Interp.run 80 (evalFrom bootMachine topExpr) with
  | .value _ m => !rootInitOkB [] m.heap && rootInitOkB [topInit] m.heap &&
      (Interp.userInit? m.heap Boot.objectId).isSome
  | _ => false
#guard match Interp.run 100 (evalFrom bootMachine FlagBox.program) with
  | .value _ m => rootInitOkB [] m.heap &&
      (classNamed? m.heap "FlagBox").any (fun k => (Interp.userInit? m.heap k).isSome)
  | _ => false

-- Waiving an unrelated top-level selector cannot admit the hidden prelude initializer.
#guard !rootInitOkB [⟨"other", [], .nil⟩] DefaultConstructorControls.hiddenRoot.heap
#guard !rootInitOkB reserved.defs DefaultConstructorControls.hiddenRoot.heap

-- Excluding only Object is insufficient: Kernel also belongs to its physical chain.
def withoutRootBuiltin : Machine :=
  match bootMachine.heap.classPayload? Boot.objectId with
  | none => bootMachine
  | some cp =>
    let cp' := { cp with methods := cp.methods.filter (·.1 != "initialize") }
    { bootMachine with heap := bootMachine.heap.setClassPayload Boot.objectId cp' }
def hiddenKernel (m : Machine) : Machine :=
  let md := { DefaultConstructorControls.hiddenInit with owner := Boot.kernelId }
  { m with heap := defineMethod m.heap Boot.kernelId "initialize" md }
#guard bootStateB withoutRootBuiltin
#guard (Interp.methodOn withoutRootBuiltin.heap Boot.objectId "initialize").isNone
-- Real boot's Object builtin masks Kernel; conformance constrains effective lookup.
#guard bootStateB (hiddenKernel bootMachine)
#guard bootStateBaseB (hiddenKernel withoutRootBuiltin)
#guard !bootStateB (hiddenKernel withoutRootBuiltin)

#print axioms after_class_root
#print axioms after_top_definition
end Ratchet.Denote.Typed.RootInitControls
