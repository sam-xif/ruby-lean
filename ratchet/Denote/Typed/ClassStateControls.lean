import Denote.Sem.ClassState
import Denote.Typed.ClassEntry
import Denote.Sanity

/-! Full class-entry conformance, with table-framing countermodels. None of these controls
admits the unexecuted class body or replaces an annotated method body with its signature. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem class_entry_state {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine}
    {name : String} {body : Ratchet.Expr} (hm : StateOk κ Γ I m)
    (hr : κ.scope.runtimeMain = true) (hf : κ.frame = none) (ha : κ.asms = [])
    (ht : ClassTablesFrame κ name m) (hq : FreshClass.nativeFrameB κ name = true)
    (hn : constOwn m.heap Boot.objectId name = none) (hne : name.isEmpty = false) :
    ∃ n, Interp.stepFn (evalFrom m (.class' name none body)) = .next n ∧
      StateOk (classBodyCtx κ name) [] .ivar0 n := by
  obtain ⟨e, he, hstep⟩ := stepFn_class_fresh hm hr hn hne
  refine ⟨_, hstep, ?_⟩
  exact FreshClass.state (StateOk_reCtl hm _ []) hr hf ha (ht.heap rfl)
    (FreshClass.nativeFrameB_sound hq) hn hne he

theorem boot_class_state (hb : bootOkB = true) {name : String} {body : Ratchet.Expr}
    (hq : FreshClass.nativeFrameB ctx0 name = true)
    (hn : constOwn bootMachine.heap Boot.objectId name = none) (hne : name.isEmpty = false) :
    ∃ n, Interp.stepFn (evalFrom bootMachine (.class' name none body)) = .next n ∧
      StateOk (classBodyCtx ctx0 name) [] .ivar0 n :=
  class_entry_state (stateOk_boot hb) rfl rfl rfl (ClassTablesFrame.empty rfl rfl) hq hn hne

#guard FreshClass.nativeFrameB ctx0 "Point"
#guard FreshClass.nativeFrameB ctx0 "IOError"
#guard !FreshClass.nativeFrameB ctx0 "String"
#guard (constOwn bootMachine.heap Boot.objectId "Point").isNone
#guard (constOwn bootMachine.heap Boot.objectId "IOError").isNone

-- Conditional path claims are silent when their owner or value is absent.
private def pathClaim (m : Machine) (owner cn : String) (p : Value → Bool) : Bool :=
  match classNamed? m.heap owner with
  | none => true
  | some k => (constLookupFrom m.heap k cn).all p

-- A new owner can activate an old claim about a different leaf name.
#guard pathClaim bootMachine "Point" "Integer" isBoolV &&
  match Interp.enterClassBody bootMachine "Point" false none .nil with
  | .next n => !pathClaim n "Point" "Integer" isBoolV
  | _ => false

-- The owner can pre-exist while registration changes the claimed leaf.
#guard pathClaim bootMachine "Object" "Point" isBoolV &&
  match Interp.enterClassBody bootMachine "Point" false none .nil with
  | .next n => !pathClaim n "Object" "Point" isBoolV
  | _ => false

-- Merely requiring owner != the new name is insufficient: dangling aliases can activate.
#guard
  let m := { bootMachine with
    heap := constSetIn bootMachine.heap Boot.objectId "Future" (.ref bootMachine.heap.objs.size) }
  (classNamed? m.heap "Future").isNone && pathClaim m "Future" "Integer" isBoolV &&
    match Interp.enterClassBody m "Point" false none .nil with
    | .next n => !pathClaim n "Future" "Integer" isBoolV
    | _ => false

-- Existing, untouched constant data survives both global and inherited class-body lookup.
#guard
  let m := { bootMachine with heap := constSetIn bootMachine.heap Boot.objectId "LIMIT" (.int 7) }
  pathClaim m "Object" "LIMIT" isIntV &&
    match Interp.enterClassBody m "Point" false none .nil with
    | .next n => pathClaim n "Object" "LIMIT" isIntV &&
        (constResolveAt n "LIMIT").any (·.identEq (.int 7))
    | _ => false

#print axioms class_entry_state
#print axioms boot_class_state
end Ratchet.Denote.Typed
