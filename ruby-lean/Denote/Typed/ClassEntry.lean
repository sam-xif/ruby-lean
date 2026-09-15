import Denote.Typed.JudgeA
import Denote.Sem.ClassHeap
import RubyCore.Proof.Judgment.ClsFresh

/-! Fresh class entry uses the model's proved heap composite, not a second allocator.
Only operational/heap lemmas are reused from the older judgment library. No old judgment
or checker acceptance is a premise. Body checking and constructor calls remain separate.
-/
set_option autoImplicit false
namespace Ratchet.Denote
open RubyCore Ratchet
open RubyCore.Interp (stepFn)
open RubyCore.Proof.Judgment (freshClsHeap freshClsMachine)

/-- Default-superclass entry at an ordinary top-level frame. The successor's heap and
class-body frame are explicit; the body has not executed or been accepted by this lemma. -/
theorem stepFn_class_fresh {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine}
    {name : String} {body : Ratchet.Expr} (hm : StateOk κ Γ I m)
    (hr : κ.scope.runtimeMain = true)
    (hn : constOwn m.heap Boot.objectId name = none) (hne : name.isEmpty = false) :
    ∃ e, (m.heap.get Boot.objectId).eigen = some e ∧
      stepFn (evalFrom m (.class' name none body)) =
        .next (freshClsMachine (evalFrom m (.class' name none body)) Boot.objectId
          m.currentFrame.cref name name e (toRuby body)) := by
  obtain ⟨e, he, _⟩ := hm.core.classReady.objectEigen
  have ho := hm.core.classReady.chains.boot.2.2.2.2
  have hd := (hm.runtime hr).owner
  refine ⟨e, he, ?_⟩
  simpa only [evalFrom, toRuby, toRubyOpt, stepFn, currentFrame_reCtl, hd] using
    (Proof.Judgment.evalExpr_class_fresh
      (m := evalFrom m (.class' name none body))
      (q := name) (eO := e) (body := toRuby body)
      (by simpa only [evalFrom, currentFrame_reCtl, hd] using hn)
      (by simpa only [evalFrom, currentFrame_reCtl, hd] using ho)
      ho he (by simp only [evalFrom, currentFrame_reCtl, hd, beq_self_eq_true, ite_true])
      (by simp only [hne, Bool.false_eq_true, not_false_eq_true]))

#print axioms ClassReady.freshClass
#print axioms stepFn_class_fresh
#print axioms classNamed_freshClass
end Ratchet.Denote
