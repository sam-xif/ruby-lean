import Denote.Rules.Subclass.SubclassEntry
import Denote.Sem.Core.Boot

/-! Actual entry with installed code, aliases and heap payloads. These model controls do
not certify the new body or infer a default constructor from an empty own-method table. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed.SubclassCoreControls
open RubyCore Ratchet Ratchet.Denote

private def setup : Ratchet.Expr := .seq [
  .def' "kept" [.req "x"] (.var .lvar "x"),
  .class' "Relay" none (.seq [
    .def' "initialize" [.req "text"] (.vasgn .ivar "@text" (.var .lvar "text")),
    .def' "text" [] (.var .ivar "@text")]),
  .casgn "RelayAlias" (.const "Relay"),
  .array [.str "before", .hash [(.sym "key", .str "value")]]]

private def newAfterBody (n : Machine) (name : String) (args : List Ratchet.Expr) : Interp.RunResult :=
  match Interp.run 30 n with
  | .value _ m => Interp.run 150 (evalFrom m
      (.send (some (.send (some (.const name)) "new" args none)) "text" [] none))
  | result => result

private def entryCoreB (name : String) : Bool :=
  match Interp.run 250 (evalFrom bootMachine setup) with
  | .value _ m => match classNamed? m.heap "Relay" with
    | some parent => match Interp.enterClassBody m name false (some parent) .nil with
      | .next n =>
        coreOkB n.heap && stringPayloadB n.heap && arrayPayloadB n.heap && hashPayloadB n.heap &&
          classNamed? n.heap name == some m.heap.objs.size &&
          classNamed? n.heap "Relay" == some parent &&
          classNamed? n.heap "RelayAlias" == some parent &&
          (n.heap.classPayload? m.heap.objs.size).any (·.methods.isEmpty) &&
          (Interp.userInit? n.heap m.heap.objs.size).any (fun md =>
            md.owner == parent && md.params.length == 1 && md.builtin.isNone &&
              !md.undefined && md.capturedFrame.isNone && md.cref == [parent, Boot.objectId]) &&
          (Interp.methodOn n.heap Boot.objectId "kept").any (fun (_, md) =>
            md.owner == Boot.objectId && md.params.length == 1 && md.builtin.isNone &&
              !md.undefined && md.cref == [Boot.objectId] && md.capturedFrame.isNone &&
              match md.body with | .var .lvar "x" => true | _ => false) &&
          (match newAfterBody n name [.str "delivered"] with
          | .value v result => Builtins.strPayload? result.heap v == some "delivered"
          | _ => false) &&
          (match newAfterBody n name [] with
          | .uncaught exc result => isAName result.heap exc "ArgumentError"
          | _ => false)
      | _ => false
    | none => false
  | _ => false

#guard entryCoreB "RelayChild"
-- A previously absent core-name slot is allowed: core preservation is an implication,
-- not a blacklist. Neither the production theorem nor this control fixes a class id.
#guard (constOwn bootMachine.heap Boot.objectId "IOError").isNone
#guard entryCoreB "IOError"

-- Synthetic dangling alias: without ConstRefsLive, fresh-name uniqueness is false even
-- though the alias was not classNamed before entry. This heap is not full StateOk.
#guard match Interp.run 250 (evalFrom bootMachine setup) with
  | .value _ m => match classNamed? m.heap "Relay" with
    | some parent =>
      let h := constSetIn m.heap Boot.objectId "Future" (.ref m.heap.objs.size)
      !constRefsLiveB h && (classNamed? h "Future").isNone &&
        match Interp.enterClassBody { m with heap := h } "RelayChild" false (some parent) .nil with
        | .next n => classNamed? n.heap "Future" == some m.heap.objs.size &&
            classNamed? n.heap "RelayChild" == classNamed? n.heap "Future"
        | _ => false
    | none => false
  | _ => false

end Ratchet.Denote.Typed.SubclassCoreControls
