import Denote.Rules.Subclass.SubclassEntry
import Denote.Sem.Core.Boot

/-! All-first-order entry theorem plus concrete nested-data and dangling-reference controls.
These are heap/entry proofs and model executions, not whole-program checker admission. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed.SubclassDataControls
open RubyCore Ratchet Ratchet.Denote

theorem entry_keeps_type {κ : Ctx} {Γ : Env} {I τ : Ty} {m : Machine} {c : Cls}
    {parent : ObjId} {name : String} {body : RubyCore.Expr} {v : Value}
    (hm : StateOk κ Γ I m) (hr : κ.scope.runtimeMain = true) (hc : c ∈ κ.classes)
    (hp : classNamed? m.heap c.name = some parent) (hf : constOwn m.heap Boot.objectId name = none)
    (hn : name.isEmpty = false) (ht : FirstOrder τ = true) (hv : denM τ m v) :
    ∃ n, Interp.enterClassBody m name false (some parent) body = .next n ∧ denM τ n v := by
  obtain ⟨n, hs, hd⟩ := Subclass.enter_declared_data hm hr hc hp hf hn
  exact ⟨n, hs, hd.denM ht hv⟩

private def setup : Ratchet.Expr := .seq [
  .class' "Capsule" none (.seq [
    .def' "initialize" [.req "flag"] (.vasgn .ivar "@flag" (.var .lvar "flag")),
    .def' "flag" [] (.var .ivar "@flag")]),
  .hash [(.sym "sample", .array [.send (some (.const "Capsule")) "new" [.tru] none])]]

private def snapshotB (h : Heap) (v : Value) : Bool :=
  (hshEntries? h v).any fun es => !es.isEmpty && es.all fun (key, a) =>
    (match key with | .sym "sample" => true | _ => false) &&
      (arrElems? h a).any fun xs => !xs.isEmpty && xs.all fun o =>
        isExactInst h o "Capsule" && (match ivarOf h o "@flag" with | .bool true => true | _ => false)

#guard match Interp.run 200 (evalFrom bootMachine setup) with
  | .value v m => snapshotB m.heap v && match classNamed? m.heap "Capsule" with
    | some parent => match Interp.enterClassBody m "CapsuleChild" false (some parent) .nil with
      | .next n => snapshotB n.heap v &&
          (List.range 3).all (fun j => isA m.heap (.ref (m.heap.objs.size + j)) Boot.basicObjectId &&
            isA n.heap (.ref (m.heap.objs.size + j)) Boot.basicObjectId) &&
          match Interp.run 30 n with
          | .value _ finished => match Interp.run 120 (evalFrom finished
              (.send (some (.send (some (.const "CapsuleChild")) "new" [.fls] none)) "flag" [] none)) with
            | .value (.bool false) _ => true
            | _ => false
          | _ => false
      | _ => false
    | none => false
  | _ => false

-- Synthetic stale-name registration changes old exact-instance types despite unchanged fields.
#guard match Interp.run 200 (evalFrom bootMachine setup) with
  | .value v m => match classNamed? m.heap "Capsule" with
    | some parent => match (m.heap.get parent).eigen with
      | some ep => snapshotB m.heap v &&
          !snapshotB (Subclass.heap m.heap Boot.objectId "Capsule" "Capsule" parent ep) v
      | none => false
    | none => false
  | _ => false

-- Dropping only the parent metaclass's superclass preserves ClassReady and saturation,
-- but allocation then changes a dangling reference from BasicObject to a non-BasicObject.
-- This is a weak-premise heap countermodel, not full StateOk or a reachable Ruby program.
#guard match Interp.run 200 (evalFrom bootMachine setup) with
  | .value _ m => match classNamed? m.heap "Capsule" with
    | some parent => match (m.heap.get parent).eigen with
      | some ep => match m.heap.classPayload? ep with
        | some cp =>
          let h := m.heap.set ep { m.heap.get ep with payload := .cls { cp with superclass := none } }
          classReadyB h && saturatedB h && !metaReadyB h parent &&
            isA h (.ref h.objs.size) Boot.basicObjectId &&
            match Interp.enterClassBody { m with heap := h } "CapsuleChild" false (some parent) .nil with
            | .next n => !isA n.heap (.ref h.objs.size) Boot.basicObjectId
            | _ => false
        | none => false
      | none => false
    | none => false
  | _ => false

theorem unrooted_parent_not_state {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine}
    {c : Cls} {k ep : ObjId} (hc : c ∈ κ.classes) (hn : classNamed? m.heap c.name = some k)
    (he : (m.heap.get k).eigen = some ep)
    (hr : (ancestors m.heap ep).contains Boot.basicObjectId = false) : ¬ StateOk κ Γ I m := by
  intro hm
  obtain ⟨e, he', hb, _⟩ := hm.classSites.metaclass hc hn
  rw [he] at he'; cases he'
  rw [hr] at hb; cases hb

#print axioms entry_keeps_type
#print axioms unrooted_parent_not_state
end Ratchet.Denote.Typed.SubclassDataControls
