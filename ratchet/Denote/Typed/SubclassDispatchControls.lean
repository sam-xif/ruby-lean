import Denote.Typed.SubclassEntry
import Denote.Sanity

/-! Real instance/metaclass inheritance plus native-prefix controls. Singleton definitions
are model inputs here, not new checker admission or annotation-body evidence. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed.SubclassDispatchControls
open RubyCore Ratchet Ratchet.Denote

private def setup : Ratchet.Expr := .class' "Beacon" none (.seq [
  .def' "echo" [.req "flag"] (.var .lvar "flag"),
  .defs .self' "kind" [] (.sym "beacon")])

#guard match Interp.run 150 (evalFrom bootMachine setup) with
  | .value _ m => match classNamed? m.heap "Beacon" with
    | some parent => match (m.heap.get parent).eigen with
      | some ep => match Interp.enterClassBody m "Flare" false (some parent) .nil with
        | .next n =>
          (Interp.methodOn n.heap m.heap.objs.size "echo").map (·.1) == some parent &&
            (Interp.methodOn n.heap (m.heap.objs.size + 1) "kind").map (·.1) == some ep &&
            queryOkB n && clsQueryOkB n && nilQueryOkB n &&
            primitiveDispatchB n.heap (nameFreeN ctx0) && primitiveErrorsB n.heap &&
            match Interp.run 30 n with
            | .value _ finished => match Interp.run 150 (evalFrom finished (.array [
                .send (some (.const "Flare")) "kind" [] none,
                .send (some (.send (some (.const "Flare")) "new" [] none)) "echo" [.tru] none])) with
              | .value v result => (arrElems? result.heap v).any fun xs =>
                  match xs.toList with | [.sym "beacon", .bool true] => true | _ => false
              | _ => false
            | _ => false
        | _ => false
      | none => false
    | none => false
  | _ => false

-- Synthetic heap: native metadata follows the runtime class name, not the constant key.
-- Pure inherited lookup still agrees, while the fresh String-named head intercepts to_s.
#guard match Interp.run 150 (evalFrom bootMachine setup) with
  | .value _ m => match classNamed? m.heap "Beacon" with
    | some parent => match (m.heap.get parent).eigen with
      | some ep =>
        let h := Subclass.heap m.heap Boot.objectId "Facade" "String" parent ep
        FreshClass.nativeQuietB "Facade" "to_s" && !FreshClass.nativeQuietB "String" "to_s" &&
          match Interp.methodOn h m.heap.objs.size "to_s", Interp.methodOn m.heap parent "to_s" with
          | some (owner, _), some (oldOwner, _) => owner == oldOwner &&
              (Interp.crubyShadow h ((ancestors h m.heap.objs.size).takeWhile (· != owner)) "to_s").isSome
          | _, _ => false
      | none => false
    | none => false
  | _ => false

end Ratchet.Denote.Typed.SubclassDispatchControls
