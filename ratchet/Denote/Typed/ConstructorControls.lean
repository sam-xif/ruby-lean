import Denote.Typed.ConstructorState
import Denote.Typed.InitBodyControls

/-! The complete Point initializer is checked over its annotation domain and then used
after real constructor dispatch. Runtime controls include a subsequent getter call. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

private def callerCtx : Ctx := reserveNameCtx ctx0 "initialize"
private def initCtx : Ctx := initializerBodyCtx callerCtx "Point"
private def pointClass : Ratchet.Expr := .class' "Point" none (.seq [
  .def' "initialize" [.req "x", .req "y"] pointInitBody,
  .def' "getX" [] (.var .ivar "@x")])
private def pointNew (args : List Ratchet.Expr) : Ratchet.Expr :=
  .send (some (.const "Point")) "new" args none
private def pointGet (args : List Ratchet.Expr) : Ratchet.Expr :=
  .send (some (pointNew args)) "getX" [] none

/-- The body proof has no concrete arguments; binding instantiates its Integer domain.
This stops at the body boundary, not at the outer newK/caller return. -/
theorem point_constructor_body {m : Machine} {k : ObjId} {md : MethodDef}
    (hm : StateOk callerCtx [] .ivar0 m) (hc : OrdinaryClass m.heap k)
    (site : InstanceSite callerCtx "Point" k m.heap)
    (hd : NewDispatch m.heap (classOf m.heap (.ref k))) (hmath : k ≠ Boot.mathId)
    (code : InstanceMethodCode k "initialize" md)
    (hi : Interp.userInit? m.heap k = some md)
    (hp : md.params = [.req "x", .req "y"]) (hb : md.body = toRuby pointInitBody)
    (x y : Int) :
    ∃ n, Interp.finishSend m (.ref k) .explicit "new" [.int x, .int y] .none = .next n ∧
      n.ctl = .eval (toRuby pointInitBody) ∧
      InitState m.heap initCtx pointInitParams .ivar0 n ∧
      InitRunSpec m.heap n (evalFrom n pointInitBody) pointInitParams .any initCtx pointInitSpine := by
  exact constructor_body_entry hm (ReframeFO.empty rfl rfl rfl rfl) rfl hc site hd hmath
    (hm.runtime rfl).phase code hi hp hb rfl (by simp [pointInitParams, DenAll, denM, isIntV])
    (by simp [pointInitParams, FirstOrder, isAliasTy])
    (fun name => (constGet?_empty (κ := initCtx) rfl name).trans (constGet?_empty rfl name).symm)
    (point_initializer_sem rfl rfl rfl)

#guard initCtx.scope.closedIvars
#guard !(instanceBodyCtx callerCtx ⟨"Point", "Point", "initialize"⟩ .ivar0).scope.closedIvars

-- Actual class definition, initializer invocation, caller return, and getter invocation.
#guard match Interp.run 300 (evalFrom bootMachine (.seq [pointClass, pointGet [.int 1, .int 2]])) with
  | .value (.int 1) _ => true
  | _ => false

#guard Semantics.typeStuck (Interp.run 300 (evalFrom bootMachine
  (.seq [pointClass, pointGet [.int 1]])))
#guard Semantics.typeStuck (Interp.run 300 (evalFrom bootMachine (.seq [pointClass,
  .send (some (pointGet [.tru, .int 2])) "+" [.int 1] none])))

-- A singleton override bypasses initialize; allocation must not be inferred from its sig.
#guard match Interp.run 200 (evalFrom bootMachine (.class' "Point" none (.seq [
    .def' "initialize" [.req "x", .req "y"] pointInitBody,
    .defs .self' "new" [.req "x", .req "y"] .fls]))) with
  | .value _ m => (classNamed? m.heap "Point").any fun k =>
      !newDispatchB m.heap (classOf m.heap (.ref k)) &&
      match Interp.run 100 (evalFrom m (pointNew [.int 1, .int 2])) with
      | .value (.bool false) _ => true
      | _ => false
  | _ => false

#print axioms point_constructor_body
end Ratchet.Denote.Typed
