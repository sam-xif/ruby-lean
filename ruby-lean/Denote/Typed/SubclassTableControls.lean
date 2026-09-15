import Denote.Typed.SubclassEntry
import Denote.Sanity

/-! Static ancestry framing, preservation of old rows, and actual multi-level inherited
calls. Tables here are model probes, not body certificates or whole-program admission. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed.SubclassTableControls
open RubyCore Ratchet Ratchet.Denote

private def echo : Defn := ⟨"echo", [.req "flag"], .var .lvar "flag"⟩
private def carrier : Cls := classWithMethod (classHeader "Carrier") echo
private def relay : Cls := { classHeader "Relay" with super? := some "Carrier" }
private def leaf : Cls := { classHeader "Leaf" with super? := some "Relay" }
private def spare : Cls := classWithMethod (classHeader "Spare") echo
private def old : CTable := [spare, relay, carrier]
private def ctx : Ctx := { ctx0 with
  pos := { ctx0.pos with classes := old }
  neg := { ctx0.neg with wholeCls := leaf :: old } }

#guard subclassBaseFrameB ctx "Relay"
#guard !subclassBaseFrameB ctx "Unknown"
#guard !subclassBaseFrameB { ctx with neg := { ctx.neg with boundConsts := ["Integer"] } } "Relay"

private def string : Cls := classHeader "String"
private def stringChild : Cls := { classHeader "TextChild" with super? := some "String" }
private def stringCtx : Ctx := { ctx0 with
  pos := { ctx0.pos with classes := [string] }
  neg := { ctx0.neg with wholeCls := [stringChild, string] } }

-- Not a builtin-parent blacklist: the whole-program guard can waive precisely the
-- negative String answer that creating TextChild invalidates. Stale whole tables decline.
#guard subclassBaseFrameB stringCtx "String"
#guard !subclassBaseFrameB { stringCtx with neg := { stringCtx.neg with wholeCls := [string] } } "String"

private def setup : Ratchet.Expr := .seq [
  .class' "Carrier" none (.def' echo.name echo.params echo.body),
  .class' "Relay" (some (.const "Carrier")) .nil,
  .class' "Spare" none (.def' echo.name echo.params echo.body)]
private def call (cn : String) (flag : Ratchet.Expr) : Ratchet.Expr :=
  .send (some (.send (some (.const cn)) "new" [] none)) "echo" [flag] none

#guard match Interp.run 250 (evalFrom bootMachine setup) with
  | .value _ m => match classNamed? m.heap "Relay", classNamed? m.heap "Carrier" with
    | some parent, some owner =>
      classChainsB old m.heap && classOwnNamesB old m.heap && baseChainsOkB m &&
        match Interp.enterClassBody m "Leaf" false (some parent) .nil with
        | .next n =>
          classChainsB old n.heap && classOwnNamesB old n.heap && baseChainsOkB n &&
            classChainsB (leaf :: old) n.heap && classOwnNamesB (leaf :: old) n.heap &&
            (Interp.methodOn n.heap m.heap.objs.size "echo").map (·.1) == some owner &&
            match Interp.run 30 n with
            | .value _ finished => match Interp.run 250 (evalFrom finished
                (.array [call "Leaf" .tru, call "Relay" .fls, call "Spare" .tru])) with
              | .value v result => (arrElems? result.heap v).any fun xs =>
                  match xs.toList with | [.bool true, .bool false, .bool true] => true | _ => false
              | _ => false
            | _ => false
        | _ => false
    | _, _ => false
  | _ => false

-- Ready metaclass alone is insufficient: the instance parent can itself be a builtin.
-- This actual entry invalidates the unguarded boot negative Float ancestry answer.
#guard
  let (_, m) := Interp.eigenclassOf bootMachine Boot.floatId
  metaReadyB m.heap Boot.floatId && baseChainsOkB m &&
    match Interp.enterClassBody m "FloatChild" false (some Boot.floatId) .nil with
    | .next n => !baseChainsOkB n &&
        (ancestors n.heap m.heap.objs.size).contains Boot.floatId
    | _ => false

/-- A static ordinary-parent claim cannot hide an active builtin-parent alias under full
conformance. This exclusion is generic in every class, context and builtin row. -/
theorem aliased_parent_not_state {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine}
    {c : Cls} {base : ObjId} {ch : List String} (hc : c ∈ κ.classes)
    (hp : classNamed? m.heap c.name = some base) (hf : subclassBaseFrameB κ c.name = true)
    (hb : (base, ch) ∈ builtinBases) (hn : isANoOk κ.wholeCls ch = true) : ¬ StateOk κ Γ I m := by
  intro hm
  exact hm.subclass_parent_separate hc hp hf hb hn rfl

#print axioms aliased_parent_not_state
end Ratchet.Denote.Typed.SubclassTableControls
