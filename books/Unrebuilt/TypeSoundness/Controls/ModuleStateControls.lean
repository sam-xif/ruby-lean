import Books.TypeSoundness.Rules.Module.ModuleStateEntry
import Books.TypeSoundness.Conformance.Core.Boot

/-! Full module entry from boot, ordinary query execution, and a selected-contract
countermodel to omitting the direct Module source from class-query conformance. -/
set_option autoImplicit false
namespace Checker.Soundness.Typed.ModuleStateControls
open RubyCore Checker Checker.Soundness

theorem boot_module_state (hb : bootOkB = true) (body : Checker.Expr) :
    ∃ n, Interp.stepFn (evalFrom bootMachine (.module' "CheckedModule" body)) = .next n ∧
      StateOk (moduleHeaderCtx (moduleBodyCtx ctx0 "CheckedModule") "CheckedModule") [] .ivar0 n :=
  module_entry_state (stateOk_boot hb) rfl rfl rfl (ClassTablesFrame.empty rfl rfl)
    (by decide) (by decide) rfl (by decide) (by decide)

#guard !(moduleHeaderCtx (moduleBodyCtx ctx0 "CheckedModule") "CheckedModule").pos.plainAlloc.contains "CheckedModule"
#guard match Interp.stepFn (evalFrom bootMachine (.module' "CheckedModule" .nil)) with
  | .next n => queryOkB n && clsQueryOkB n && nilQueryOkB n &&
    match Interp.run 100 n with
    | .value _ m => match Interp.run 100 (evalFrom m (.send (some (.const "CheckedModule")) "to_s" [] none)) with
      | .value v result => Builtins.strPayload? result.heap v == some "CheckedModule"
      | _ => false
    | _ => false
  | _ => false

#guard match Interp.run 100 (evalFrom bootMachine (.seq [
    .module' "CheckedModule" .nil,
    .send (some (.const "CheckedModule")) "===" [.int 1] none])) with
  | .value (.bool false) _ => true
  | _ => false

-- Route all old class objects through Class, bypassing Module, and supply clean direct
-- Class query rows. The hidden Module body appears only at real fresh module dispatch.
private def hiddenModuleQuery : Machine :=
  let h := match bootMachine.heap.classPayload? Boot.classId with
    | none => bootMachine.heap
    | some cp => bootMachine.heap.setClassPayload Boot.classId { cp with superclass := some Boot.objectId }
  let h := defineMethod h Boot.classId "to_s" { owner := Boot.classId, params := [], body := .nil, builtin := some "Module#to_s" }
  let h := defineMethod h Boot.classId "===" { owner := Boot.classId, params := [], body := .nil, builtin := some "Module#===" }
  let h := { h with objs := h.objs.map fun obj => match obj.payload with
    | .cls _ => { obj with eigen := some Boot.classId }
    | _ => obj }
  { bootMachine with heap := defineMethod h Boot.moduleId "to_s" { owner := Boot.moduleId, params := [], body := .nil } }

#guard classReadyB hiddenModuleQuery.heap && saturatedB hiddenModuleQuery.heap &&
  clsQueryAtB hiddenModuleQuery Boot.classId &&
  (List.range hiddenModuleQuery.heap.objs.size).all (fun o =>
    !(hiddenModuleQuery.heap.classPayload? o).isSome ||
      clsQueryAtB hiddenModuleQuery (classOf hiddenModuleQuery.heap (.ref o))) &&
  !clsQueryAtB hiddenModuleQuery Boot.moduleId && !clsQueryOkB hiddenModuleQuery

#guard match Interp.stepFn (evalFrom hiddenModuleQuery (.module' "ExposedModule" .nil)) with
  | .next n => !clsQueryAtB n (classOf n.heap n.currentFrame.self) &&
    match Interp.run 100 n with
    | .value _ m => match Interp.run 100 (evalFrom m (.send (some (.const "ExposedModule")) "to_s" [] none)) with
      | .value .nil _ => true
      | _ => false
    | _ => false
  | _ => false

theorem hidden_module_query_not_state {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine}
    {owner : ObjId} {md : MethodDef} (hf : nameFreeN κ "to_s" = true)
    (hl : Interp.methodOn m.heap Boot.moduleId "to_s" = some (owner, md))
    (hb : md.builtin = none) : ¬ StateOk κ Γ I m := by
  intro hm
  have hh := ((hm.clsQuery "to_s" "Module#to_s" (by simp [clsQueryBuiltins]) hf
    Boot.moduleId (Or.inr (Or.inl rfl))).1 owner md hl).1
  rw [hb] at hh; cases hh

#print axioms boot_module_state
#print axioms hidden_module_query_not_state
end Checker.Soundness.Typed.ModuleStateControls
