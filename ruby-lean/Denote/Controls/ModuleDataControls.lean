import Denote.Rules.Module.ModuleEntry
import Denote.Sem.Core.Boot

/-! Module allocation controls: nested data, the real singleton-call path, and two
premise countermodels. These do not claim whole-program checker admission. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed.ModuleDataControls
open RubyCore Ratchet Ratchet.Denote

theorem entry_keeps_type {κ : Ctx} {Γ : Env} {I τ : Ty} {m : Machine}
    {name : String} {body : Ratchet.Expr} {v : Value}
    (hm : StateOk κ Γ I m) (hr : κ.scope.runtimeMain = true)
    (hf : constOwn m.heap Boot.objectId name = none) (hn : name.isEmpty = false)
    (ht : FirstOrder τ = true) (hv : denM τ m v) :
    ∃ n, Interp.stepFn (evalFrom m (.module' name body)) = .next n ∧ denM τ n v := by
  obtain ⟨n, hs, hd⟩ := module_entry_data hm hr hf hn
  exact ⟨n, hs, hd.denM ht hv⟩

/-- The current ordinary-class contract cannot be reused for a module header. -/
theorem module_not_declared_class {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine}
    {c : Cls} {k : ObjId} (hc : c ∈ κ.classes) (hn : classNamed? m.heap c.name = some k)
    (hp : (m.heap.classPayload? k).map (·.isModule) = some true) : ¬ StateOk κ Γ I m := by
  intro hm
  have hc := (hm.declCls c hc k hn).2.2.2.1
  rw [hp] at hc; cases hc

#guard (ancestors bootMachine.heap Boot.moduleId).contains Boot.basicObjectId

-- Real 077 allocation and singleton invocation. The module's own ancestor chain is
-- just itself; its value's dispatch chain goes through its metaclass and Module.
#guard match Interp.stepFn (evalFrom bootMachine
    (.module' "M" (.defs .self' "foo" [] (.int 1)))) with
  | .next n =>
    let k := bootMachine.heap.objs.size
    n.heap.objs.size == k + 2 && classNamed? n.heap "M" == some k &&
      (n.heap.classPayload? k).any (fun cp => cp.isModule && cp.superclass.isNone) &&
      ancestors n.heap k == [k] && !(ancestors n.heap k).contains Boot.basicObjectId &&
      (n.heap.get k).eigen == some (k + 1) &&
      (n.heap.classPayload? (k + 1)).any (fun cp => cp.superclass == some Boot.moduleId) &&
      classReadyB n.heap && saturatedB n.heap && metaReadyB n.heap k &&
      isA n.heap (.ref k) Boot.basicObjectId &&
      (match n.currentFrame.self with | .ref r => r == k | _ => false) &&
      n.currentFrame.defmod == k && n.currentFrame.cref == [k, Boot.objectId] &&
      match Interp.run 100 n with
      | .value _ finished => match Interp.run 100
          (evalFrom finished (.send (some (.const "M")) "foo" [] none)) with
        | .value (.int 1) _ => true
        | _ => false
      | _ => false
  | _ => false

-- A module body starts with its own locals and returns to the saved caller frame.
#guard
  let m := bootMachine.setLocal "outside" (.int 9)
  match Interp.stepFn (evalFrom m (.module' "Cabinet" (.seq [
      .vasgn .lvar "outside" (.int 42), .var .lvar "outside"]))) with
  | .next n =>
    (match n.getLocal "outside" with | .nil => true | _ => false) &&
      match Interp.run 100 n with
      | .value (.int 42) finished =>
        finished.stack == m.stack &&
          (match finished.getLocal "outside" with | .int 9 => true | _ => false)
      | _ => false
  | _ => false

private def setup : Ratchet.Expr := .seq [
  .class' "Capsule" none (.def' "initialize" [.req "flag"]
    (.vasgn .ivar "@flag" (.var .lvar "flag"))),
  .hash [(.sym "sample", .array [.send (some (.const "Capsule")) "new" [.tru] none])]]

private def snapshotB (h : Heap) (v : Value) : Bool :=
  (hshEntries? h v).any fun es => !es.isEmpty && es.all fun (key, a) =>
    (match key with | .sym "sample" => true | _ => false) &&
      (arrElems? h a).any fun xs => !xs.isEmpty && xs.all fun o =>
        isExactInst h o "Capsule" && (match ivarOf h o "@flag" with | .bool true => true | _ => false)

#guard match Interp.run 200 (evalFrom bootMachine setup) with
  | .value v m => snapshotB m.heap v &&
    match Interp.stepFn (evalFrom m (.module' "Container" .nil)) with
    | .next n => snapshotB n.heap v &&
      (List.range 3).all (fun j => isA m.heap (.ref (m.heap.objs.size + j)) Boot.basicObjectId &&
        isA n.heap (.ref (m.heap.objs.size + j)) Boot.basicObjectId)
    | _ => false
  | _ => false

-- Bypassing the fresh-name premise destroys exact-instance observations at an old name.
#guard match Interp.run 200 (evalFrom bootMachine setup) with
  | .value v m => snapshotB m.heap v &&
      !snapshotB (Proof.Judgment.freshModHeap m.heap Boot.objectId "Capsule" "Capsule") v
  | _ => false

-- A selected-contract countermodel, not a reachable heap or a full-StateOk witness:
-- Class still reaches Object while Module has no parent. ClassReady and saturation pass,
-- but module allocation destroys BasicObject membership at the formerly dangling id.
#guard match bootMachine.heap.classPayload? Boot.classId,
    bootMachine.heap.classPayload? Boot.moduleId with
  | some cc, some mc =>
    let h := (bootMachine.heap.setClassPayload Boot.classId
      { cc with superclass := some Boot.objectId }).setClassPayload Boot.moduleId
      { mc with superclass := none }
    classReadyB h && saturatedB h && !coreOkB h &&
      !(ancestors h Boot.moduleId).contains Boot.basicObjectId &&
      isA h (.ref h.objs.size) Boot.basicObjectId &&
      match Interp.stepFn (evalFrom { bootMachine with heap := h } (.module' "Isolated" .nil)) with
      | .next n => !isA n.heap (.ref h.objs.size) Boot.basicObjectId
      | _ => false
  | _, _ => false

theorem unrooted_module_not_state {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine}
    (hmod : (ancestors m.heap Boot.moduleId).contains Boot.basicObjectId = false) :
    ¬ StateOk κ Γ I m := by
  intro hm
  have hb := hm.core.moduleBasic
  rw [hmod] at hb; cases hb

#print axioms entry_keeps_type
#print axioms module_not_declared_class
#print axioms unrooted_module_not_state
end Ratchet.Denote.Typed.ModuleDataControls
