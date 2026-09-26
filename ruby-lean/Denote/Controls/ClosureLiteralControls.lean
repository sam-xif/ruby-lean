import Denote.Rules.Closure.Literal
import Denote.Sem.Core.Boot
import Denote.Ty.DenB

/-! Creation is safe for arbitrary code. The legacy callable denotation and table
predicate do not justify calling that code: identity, mode and block locals matter. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed.ClosureLiteralControls
open RubyCore Ratchet Ratchet.Denote

example (hb : bootOkB = true) (lam : Bool) (ps : List Ratchet.Param)
    (ls : List String) (body : Ratchet.Expr) :
    ∃ n, Interp.stepFn (evalFrom bootMachine (.send none (if lam then "lambda" else "proc") []
        (some (.block ps ls body)))) = .next n ∧ StateOk ctx0 [] .ivar0 n ∧
      Framed bootMachine n ∧ procClosure? n.heap (.ref bootMachine.heap.objs.size) =
        some (reifiedClosure bootMachine (toRubyParams ps) ls (toRuby body) lam) :=
  closure_literal_result (stateOk_boot hb) lam (by cases lam <;> rfl) ps ls body

/-- The superseded empty-capture denotation, retained to keep F49's witness explicit. -/
def LegacyIndexDen (_idx : Nat) (m : Machine) (f : Value) : Prop :=
  ∃ cl, procClosure? m.heap f = some cl

theorem reified_unindexed (idx : Nat) (m : Machine) (ps : List RubyCore.Param)
    (ls : List String) (body : RubyCore.Expr) (lam : Bool) :
    LegacyIndexDen idx (reifiedMachine m ps ls body lam) (.ref m.heap.objs.size) :=
  ⟨_, reified_payload m ps ls body lam⟩

theorem wrong_body_not_table (m : Machine) (body : RubyCore.Expr) (hb : body ≠ .int 1) :
    ¬ closTblOk [⟨[], .int 1⟩] 0 (reifiedMachine m [] [] body true) (.ref m.heap.objs.size) := by
  rintro ⟨c, cl, hk, hp, _, hbody⟩
  have hc : (some (⟨[], .int 1⟩ : Clos)) = some c := hk
  cases Option.some.inj hc
  rw [reified_payload] at hp
  cases Option.some.inj hp
  exact hb hbody

/-- The old table predicate does not constrain lambda mode or block-local shadowing. -/
theorem reified_table (m : Machine) (ps : List Ratchet.Param) (ls : List String)
    (body : Ratchet.Expr) (lam : Bool) (hd : declFree body = true) :
    closTblOk [⟨ps, body⟩] 0 (reifiedMachine m (toRubyParams ps) ls (toRuby body) lam)
      (.ref m.heap.objs.size) := by
  refine ⟨⟨ps, body⟩, _, ?_, reified_payload m _ _ _ _, rfl, rfl⟩
  simp [closGet?, hd]

private def callReified (ps : List RubyCore.Param) (ls : List String)
    (body : RubyCore.Expr) (lam : Bool) (m : Machine := bootMachine) : Interp.RunResult :=
  let n := (reifiedMachine m ps ls body lam).setLocal "f" (.ref m.heap.objs.size)
  Interp.run 100 (evalFrom n (.send (some (.var .lvar "f")) "call" [] none))

-- Same parameter/body table row: a proc accepts a missing argument, a lambda rejects it.
#guard match callReified [.req "x"] [] (.int 1) false with
  | .value (.int 1) _ => true
  | _ => false
#guard Semantics.typeStuck (callReified [.req "x"] [] (.int 1) true)

-- Same parameter/body/capture types: a block-local shadows the captured Integer with nil.
private def plusX : RubyCore.Expr := .send (some (.var .lvar "x")) "+" [.int 1] none
private def plusCode : ClosureCode :=
  ⟨[], [], .send (some (.var .lvar "x")) "+" [.int 1] none, true, rfl⟩
#guard closB (.clos plusCode (.ivarCons "x" .int .ivar0) .never)
  (reifiedMachine (bootMachine.setLocal "x" (.int 1)) [] [] plusX true)
  (.ref bootMachine.heap.objs.size)
#guard !closB (.clos plusCode (.ivarCons "x" .int .ivar0) .never)
  (reifiedMachine (bootMachine.setLocal "x" (.int 1)) [] ["x"] plusX true)
  (.ref bootMachine.heap.objs.size)
#guard match callReified [] [] plusX true (bootMachine.setLocal "x" (.int 1)) with
  | .value (.int 2) _ => true
  | _ => false
#guard Semantics.typeStuck (callReified [] ["x"] plusX true (bootMachine.setLocal "x" (.int 1)))

-- Even an unsafe body satisfies the index-free denotation above.
#guard Semantics.typeStuck (callReified [] [] (.send (some (.int 1)) "+" [.nil] none) true)

-- Capturing stores a frame reference. Mutating that frame changes the later call.
#guard Semantics.typeStuck (Interp.run 100 (evalFrom bootMachine (.seq [
  .vasgn .lvar "x" (.int 1),
  .vasgn .lvar "f" (.send none "lambda" []
    (some (.block [] [] (.send (some (.var .lvar "x")) "+" [.int 1] none)))),
  .vasgn .lvar "x" (.str "s"),
  .send (some (.var .lvar "f")) "call" [] none])))

-- The creation theorem requires name freedom; an ordinary method shadows Kernel#lambda.
#guard match Interp.run 100 (evalFrom bootMachine (.seq [
    .def' "lambda" [] (.int 7), .send none "lambda" [] (some (.block [] [] (.int 1)))])) with
  | .value (.int 7) _ => true
  | _ => false

#print axioms reified_unindexed
#print axioms wrong_body_not_table
#print axioms reified_table
end Ratchet.Denote.Typed.ClosureLiteralControls
