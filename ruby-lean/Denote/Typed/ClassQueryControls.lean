import Denote.Sem.ClassQueries
import Denote.Typed.ClassEntry
import Denote.Sanity

/-! Query transport consumes boot conformance through actual class entry. These are not
class admission controls: full body conformance and checked instance methods remain owed. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote
open RubyCore.Proof.Judgment (freshClsHeap freshClsMachine)

private theorem point_quiet (mn : String) : FreshClass.NativeQuiet "Point" mn := by
  unfold FreshClass.NativeQuiet crubyClassDefines
  change false = false ∧ false = false
  exact ⟨rfl, rfl⟩

theorem boot_point_queries (hb : bootOkB = true)
    (hn : constOwn bootMachine.heap Boot.objectId "Point" = none) (body : Ratchet.Expr) :
    ∃ n, Interp.stepFn (evalFrom bootMachine (.class' "Point" none body)) = .next n ∧
      QueryOk ctx0 n ∧ ClsQueryOk ctx0 n ∧ NilQueryOk ctx0 n := by
  have hm := stateOk_boot hb
  obtain ⟨e, he, hstep⟩ := stepFn_class_fresh (body := body) hm rfl
    (name := "Point") hn rfl
  have hc := hm.core.classReady.chains
  have hel := hc.eigen Boot.objectId hc.boot.2.2.2.2 e he
  refine ⟨_, hstep, ?_, ?_, ?_⟩
  · exact FreshClass.query hc hm.sat hel rfl (fun mn _ _ _ => point_quiet mn) rfl hm.query
  · exact FreshClass.clsQuery hc hm.sat (hm.runtime rfl).classLive he rfl
      (fun mn _ _ _ => point_quiet mn) rfl hm.clsQuery
  · exact FreshClass.nilQuery hc hm.sat hel rfl (fun _ => point_quiet "nil?") rfl hm.nilQuery

#guard clsQueryAtB bootMachine Boot.classId
#guard (constOwn bootMachine.heap Boot.objectId "Point").isNone
#guard match Interp.enterClassBody bootMachine "Point" false none .nil with
  | .next n => queryOkB n && clsQueryOkB n && nilQueryOkB n
  | _ => false

-- A countermodel to checking only existing class receivers: route them through Module,
-- masking an incompatible direct Class method. It is not a reachable-program claim.
private def classReceiversViaModule : Machine :=
  { bootMachine with heap := { bootMachine.heap with objs := bootMachine.heap.objs.map fun obj =>
    match obj.payload with
    | .cls _ => { obj with eigen := some Boot.moduleId }
    | _ => obj } }
private def hiddenClassOverride : Machine :=
  { classReceiversViaModule with
    heap := defineMethod classReceiversViaModule.heap Boot.classId "to_s"
      { params := [], body := .nil, owner := Boot.classId, builtin := some "Object#to_s" } }

#guard classReadyB hiddenClassOverride.heap
#guard saturatedB hiddenClassOverride.heap
#guard (List.range hiddenClassOverride.heap.objs.size).all (fun o =>
  !(hiddenClassOverride.heap.classPayload? o).isSome ||
    clsQueryAtB hiddenClassOverride (classOf hiddenClassOverride.heap (.ref o)))
#guard !clsQueryOkB hiddenClassOverride
#guard match Interp.enterClassBody hiddenClassOverride "Point" false none .nil with
  | .next n => !clsQueryAtB n (classOf n.heap (.ref (hiddenClassOverride.heap.objs.size + 1)))
  | _ => false

-- Forcing the composite to use a native name preserves lookup but introduces a shadow.
-- This is not the actual String-reopen branch, and it must not justify class admission.
#guard
  let h := freshClsHeap bootMachine.heap Boot.objectId "String" "String"
    ((bootMachine.heap.get Boot.objectId).eigen.getD Boot.classId)
  let k := bootMachine.heap.objs.size
  match Interp.methodOn h k "to_s" with
  | some (owner, _) =>
      (Interp.methodOn h k "to_s").map (·.1) ==
        (Interp.methodOn bootMachine.heap Boot.objectId "to_s").map (·.1) &&
      (Interp.crubyShadow h ((ancestors h k).takeWhile (· != owner)) "to_s").isSome
  | _ => false

#print axioms boot_point_queries
end Ratchet.Denote.Typed
