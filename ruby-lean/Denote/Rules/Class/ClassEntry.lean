import Denote.Judgment.JudgeA
import Denote.Sem.Class.ClassHeap
import Denote.Sem.Class.ClassHeapActual
import RubyCore.Proof.Judgment.ClsFresh

/-! Fresh class entry uses the proved actual registration/metaclass heap.
Only operational/heap lemmas are reused from the older judgment library. No old judgment
or checker acceptance is a premise. Body checking and constructor calls remain separate.
-/
set_option autoImplicit false
namespace Ratchet.Denote
open RubyCore Ratchet
open RubyCore.Interp (stepFn)

/-- Default-superclass entry at an ordinary top-level frame. The successor queues
const_added; inherited and the body frame follow through ClassCallbacks. -/
theorem stepFn_class_fresh {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine}
    {name : String} {body : Ratchet.Expr} (hm : StateOk κ Γ I m)
    (hr : κ.scope.runtimeMain = true)
    (hn : constOwn m.heap Boot.objectId name = none) (_hne : name.isEmpty = false) :
    ∃ e, (m.heap.get Boot.objectId).eigen = some e ∧
      stepFn (evalFrom m (.class' name none body)) =
        .next { evalFrom m (.class' name none body) with
          heap := FreshClassActual.heap m name e,
          ctl := .send (.ref Boot.objectId) .reflective "const_added" [.sym name] none [],
          kont := [.constClassK m.heap.objs.size (some Boot.objectId) name (toRuby body)] } := by
  obtain ⟨e, he, _⟩ := hm.core.classReady.objectEigen
  refine ⟨e, he, ?_⟩
  have ready := (StateOk_reCtl hm (.eval (toRuby (.class' name none body))) []).runtime hr
  have hs := FreshClassActual.stepFn_fresh (m := evalFrom m (.class' name none body))
    (body := toRuby body) ready hn he
  have hh : FreshClassActual.heap (evalFrom m (.class' name none body)) name e =
      FreshClassActual.heap m name e := rfl
  rw [hh] at hs
  simpa only [evalFrom, toRuby, toRubyOpt] using hs

#print axioms ClassReady.freshClass
#print axioms stepFn_class_fresh
#print axioms classNamed_freshClass
end Ratchet.Denote
