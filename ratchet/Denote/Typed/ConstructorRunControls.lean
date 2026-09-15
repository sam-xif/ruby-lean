import Denote.Typed.ConstructorRun
import Denote.Typed.InitBodyControls

/-! Full constructor contract, not only body entry: all Integer arguments, caller locals,
initialized result fields, and the actual return continuations. Class admission is separate. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

private def callerCtx : Ctx := reserveNameCtx ctx0 "initialize"
private def initCtx : Ctx := initializerBodyCtx callerCtx "Point"

theorem point_constructor_run {m : Machine} {Γ : Env} {k : ObjId} {md : MethodDef}
    (hm : StateOk callerCtx Γ .ivar0 m) (hc : OrdinaryClass m.heap k)
    (site : InstanceSite callerCtx "Point" k m.heap)
    (hd : NewDispatch m.heap (classOf m.heap (.ref k))) (hmath : k ≠ Boot.mathId)
    (code : InstanceMethodCode k "initialize" md) (hi : Interp.userInit? m.heap k = some md)
    (hp : md.params = [.req "x", .req "y"]) (hb : md.body = toRuby pointInitBody)
    (hΓ : ∀ p ∈ Γ, FirstOrder (stripAlias p.2) = true) (hkont : m.kont = []) (x y : Int) :
    ∃ n, Interp.finishSend m (.ref k) .explicit "new" [.int x, .int y] .none = .next n ∧
      RunSpec m n Γ (.inst "Point" pointInitSpine) callerCtx .ivar0 := by
  have hconst (name : String) : constGet? initCtx name = constGet? callerCtx name :=
    (constGet?_empty (κ := initCtx) rfl name).trans (constGet?_empty rfl name).symm
  exact constructor_runSpec (κ := callerCtx) (ps := pointInitParams) (κb := initCtx) hm
    (ReframeFO.empty rfl rfl rfl rfl) rfl
    (ReframeFO.empty rfl rfl rfl rfl) hc site hd hmath code hi hp hb rfl
    (by simp [pointInitParams, DenAll, denM, isIntV])
    (by simp [pointInitParams, FirstOrder, isAliasTy]) hconst rfl rfl rfl rfl hconst hΓ rfl rfl hkont
    (point_initializer_sem rfl rfl rfl)

private def pointClass : Ratchet.Expr := .class' "Point" none (.seq [
  .def' "initialize" [.req "x", .req "y"] pointInitBody,
  .def' "getX" [] (.var .ivar "@x")])
private def pointNew : Ratchet.Expr := .send (some (.const "Point")) "new" [.int 1, .int 2] none

-- The initializer returns 2, but new returns the receiver with both initialized fields.
#guard match Interp.run 300 (evalFrom bootMachine (.seq [pointClass, pointNew])) with
  | .value (.ref o) m => isExactInst m.heap (.ref o) "Point" &&
      (ivarOf m.heap (.ref o) "@x").identEq (.int 1) && (ivarOf m.heap (.ref o) "@y").identEq (.int 2)
  | _ => false

-- Callee x is an Integer, caller x is a String; both remain usable after construction.
#guard match Interp.run 400 (evalFrom bootMachine (.seq [
    .vasgn .lvar "x" (.str "caller"), pointClass, .vasgn .lvar "p" pointNew,
    .send (some (.send (some (.var .lvar "p")) "getX" [] none)) "+"
      [.send (some (.var .lvar "x")) "length" [] none] none])) with
  | .value (.int 7) _ => true
  | _ => false

-- Substituting initialize's Integer return type for new's receiver type is not sound.
example (origin m : Machine) (o : ObjId) (Γ : Env) (κ : Ctx) (I : Ty) :
    ¬ RunSpec origin (deliverA (.val (.ref o)) m []) Γ .int κ I := by
  intro h
  have hv := (h.2 0 (.val (.ref o)) (deliverA (.val (.ref o)) m []) 0
    (by rw [runA_ans (by rfl)])).2.1
  simp only [AnsOk, denM, isIntV, Bool.false_eq_true] at hv

#print axioms point_constructor_run
end Ratchet.Denote.Typed
