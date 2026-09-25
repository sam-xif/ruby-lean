import Denote.Judgment.JudgeA
import Denote.Sem.Module.ModuleFrame

/-! Actual module entry and preservation of old data. This does not yet publish a module
header in StateOk or justify checking its body in a module scope. -/
set_option autoImplicit false
namespace Ratchet.Denote
open RubyCore Ratchet
open RubyCore.Interp (stepFn)
open RubyCore.Proof.Judgment (freshModMachine)

theorem stepFn_module_fresh {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine}
    {name : String} {body : Ratchet.Expr} (hm : StateOk κ Γ I m)
    (hr : κ.scope.runtimeMain = true)
    (hn : constOwn m.heap Boot.objectId name = none) (hne : name.isEmpty = false) :
    stepFn (evalFrom m (.module' name body)) =
      .next (freshModMachine (evalFrom m (.module' name body)) Boot.objectId
        m.currentFrame.cref name name (toRuby body)) := by
  have ho := hm.core.classReady.chains.boot.2.2.2.2
  have hd := (hm.runtime hr).owner
  simpa only [evalFrom, toRuby, stepFn, currentFrame_reCtl, hd] using
    (Proof.Judgment.evalExpr_module_fresh
      (m := evalFrom m (.module' name body)) (q := name) (body := toRuby body)
      (by simpa only [evalFrom, currentFrame_reCtl, hd] using hn)
      (by simpa only [evalFrom, currentFrame_reCtl, hd] using ho)
      (by simp only [evalFrom, currentFrame_reCtl, hd, beq_self_eq_true, ite_true])
      (by simp only [hne, Bool.false_eq_true, not_false_eq_true]))

theorem module_entry_data {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine}
    {name : String} {body : Ratchet.Expr} (hm : StateOk κ Γ I m)
    (hr : κ.scope.runtimeMain = true)
    (hn : constOwn m.heap Boot.objectId name = none) (hne : name.isEmpty = false) :
    ∃ n, stepFn (evalFrom m (.module' name body)) = .next n ∧ DataPres m.heap n.heap :=
  ⟨_, stepFn_module_fresh hm hr hn hne,
    FreshModule.dataPres hm.core.classReady hm.sat hm.core.basicSelf hn hm.core.moduleBasic⟩

theorem module_entry_ready {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine}
    {name : String} {body : Ratchet.Expr} (hm : StateOk κ Γ I m)
    (hr : κ.scope.runtimeMain = true)
    (hn : constOwn m.heap Boot.objectId name = none) (hne : name.isEmpty = false) :
    ∃ n, stepFn (evalFrom m (.module' name body)) = .next n ∧
      ClassReady n.heap ∧ HeapSaturated n ∧
      MetaReady n.heap m.heap.objs.size ∧ SelfTyOk (some (.clsOf name)) n := by
  refine ⟨_, stepFn_module_fresh hm hr hn hne,
    FreshModule.ready hm.core.classReady hm.sat,
    Proof.Judgment.saturated_fresh hm.core.classReady.chains hm.sat
      hm.core.classReady.chains.boot.2.2.2.2,
    FreshModule.meta_fresh hm.core.classReady.chains hm.sat hm.core.moduleBasic, ?_⟩
  exact FreshModule.self_type (hm.runtime hr).classLive

#print axioms stepFn_module_fresh
#print axioms module_entry_data
#print axioms module_entry_ready
end Ratchet.Denote
