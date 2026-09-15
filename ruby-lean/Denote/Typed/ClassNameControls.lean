import Denote.Typed.ClassEntry
import Denote.Sem.ClassNames
import Denote.Sanity

/-! Class entry changes self's dispatch chain. These controls distinguish the required
Object metaclass chain from unrelated singleton methods such as the shim's T.proc. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem class_entry_names {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine}
    {name : String} {body : Ratchet.Expr} (hm : StateOk κ Γ I m)
    (hr : κ.scope.runtimeMain = true)
    (hn : constOwn m.heap Boot.objectId name = none) (hne : name.isEmpty = false) :
    ∃ n, Interp.stepFn (evalFrom m (.class' name none body)) = .next n ∧ NameFreeOk κ n := by
  obtain ⟨e, he, hstep⟩ := stepFn_class_fresh hm hr hn hne
  exact ⟨_, hstep, FreshClass.nameFree hm.core.classReady.chains hm.sat he hm.nameFree⟩

private def currentNamesFree (m : Machine) : Bool :=
  shadowableNames.all fun n =>
    (Interp.methodOn m.heap (classOf m.heap m.currentFrame.self) n).isNone

private def hiddenLambda : Machine :=
  let e := (bootMachine.heap.get Boot.objectId).eigen.getD Boot.classId
  { bootMachine with
    heap := defineMethod bootMachine.heap e "lambda"
      { owner := e, params := [], body := .nil, fromPrelude := true } }

-- This is the entire old boot conjunction, not merely the component being refuted.
#guard
  let m := hiddenLambda
  saturatedB m.heap && coreOkB m.heap && frameOkB m && topScopeB m &&
    methodsExactB ctx0 m && currentNamesFree m && missFreeB m && selfLiveB m &&
    localsEmptyB m && queryOkB m && clsQueryOkB m && baseChainsOkB m && nilQueryOkB m &&
    primitiveDispatchB m.heap (nameFreeN ctx0) && primitiveErrorsB m.heap &&
    stringPayloadB m.heap && arrayPayloadB m.heap && hashPayloadB m.heap && mainReadyB m

#guard currentNamesFree hiddenLambda
#guard !nameFreeB hiddenLambda
#guard nameFreeB bootMachine
#guard match Interp.enterClassBody bootMachine "Point" false none .nil with
  | .next n => nameFreeB n
  | _ => false
#guard match Interp.enterClassBody hiddenLambda "Point" false none .nil with
  | .next n => !currentNamesFree n &&
      (Interp.methodOn n.heap (classOf n.heap n.currentFrame.self) "lambda").any
        (fun (_, md) => md.builtin.isNone && !md.undefined && md.fromPrelude)
  | _ => false

-- A heap-global absence condition would reject the real prelude.
#guard match classNamed? bootMachine.heap "T" with
  | some t =>
      (Interp.methodOn bootMachine.heap (classOf bootMachine.heap (.ref t)) "proc").any
        (fun (_, md) => md.builtin.isNone && !md.undefined && md.fromPrelude)
  | none => false

#print axioms class_entry_names
end Ratchet.Denote.Typed
