import Denote.Typed.PointClass
import Denote.Typed.ConstructorLookup
import Denote.Sanity

/-! Complete 061 class execution and the published code at its returned caller state.
This does not yet certify the subsequent constructor/getter expression. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed.PointClass
open RubyCore Ratchet Ratchet.Denote

theorem boot_run (hb : bootOkB = true)
    (hn : constOwn bootMachine.heap Boot.objectId "Point" = none) :
    RunSpec bootMachine (evalFrom bootMachine program) [] .sym callerCtx .ivar0 :=
  runSpec (stateOk_boot hb) rfl (by simp) hn

theorem constructor_code {Γ : Env} {I : Ty} {m : Machine} (hm : StateOk callerCtx Γ I m) :
    ∃ k md, InstanceSite callerCtx "Point" k m.heap ∧
      NewDispatch m.heap (classOf m.heap (.ref k)) ∧
      md.params = [.req "x", .req "y"] ∧ md.body = toRuby pointInitBody ∧
      InstanceMethodCode k "initialize" md ∧ Interp.userInit? m.heap k = some md :=
  declared_constructor_code (c := classWithMethod initClass getter) (d := initDecl) hm
    (by change classWithMethod initClass getter ∈ [classWithMethod initClass getter, initClass, header]; simp)
    (by change initDecl ∈ [getter, initDecl]; simp) rfl (by decide)

theorem after_run {Γ : Env} {I : Ty} {m n : Machine} {fuel rest : Nat} {v : Value}
    (hm : StateOk ctx0 Γ I m) (hI : FirstOrder I = true)
    (hΓ : ∀ p ∈ Γ, FirstOrder (stripAlias p.2) = true)
    (hn : constOwn m.heap Boot.objectId "Point" = none)
    (hr : runA fuel (evalFrom m program) = .ans (.val v) n rest) :
    StateOk callerCtx Γ I n ∧
      ∃ k md, InstanceSite callerCtx "Point" k n.heap ∧
        NewDispatch n.heap (classOf n.heap (.ref k)) ∧
        md.params = [.req "x", .req "y"] ∧ md.body = toRuby pointInitBody ∧
        InstanceMethodCode k "initialize" md ∧ Interp.userInit? n.heap k = some md := by
  have hs := ((runSpec hm hI hΓ hn).2 fuel (.val v) n rest hr).2.2 v rfl
  exact ⟨hs, constructor_code hs⟩

-- The class result is the last definition's symbol, not an instance or initializer value.
#guard match Interp.run 200 (evalFrom bootMachine program) with
  | .value (.sym "getX") m =>
      m.currentFrame.kind == .toplevel && (classNamed? m.heap "Point").any (fun k =>
        (Interp.userInit? m.heap k).any (fun md => md.params == [.req "x", .req "y"]))
  | _ => false

-- Methods execute only at calls; the class statement preserves the caller's String local.
#guard match Interp.run 300 (evalFrom bootMachine (.seq [
    .vasgn .lvar "x" (.str "caller"), program, .send (some (.var .lvar "x")) "length" [] none])) with
  | .value (.int 6) _ => true
  | _ => false

#guard match Interp.run 300 (evalFrom bootMachine (.seq [program,
    .send (some (.send (some (.const "Point")) "new" [.int 1, .int 2] none)) "getX" [] none])) with
  | .value (.int 1) _ => true
  | _ => false

#guard match Interp.run 300 (evalFrom bootMachine (.seq [program,
    .send (some (.const "Point")) "new" [] none])) with
  | .uncaught exc m => isAName m.heap exc "ArgumentError"
  | _ => false

#print axioms boot_run
#print axioms after_run
end Ratchet.Denote.Typed.PointClass
