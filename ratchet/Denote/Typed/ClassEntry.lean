import Denote.Typed.JudgeA
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

/-- The same readiness invariant survives both allocations and constant registration. -/
theorem ClassReady.freshClass {h : Heap} {d : ObjId} {name q : String} {e : ObjId}
    (hc : ClassReady h) (hsat : Proof.Saturated h) (hd : d < h.objs.size)
    (he : (h.get Boot.objectId).eigen = some e) :
    ClassReady (freshClsHeap h d name q e) := by
  have ho := hc.chains.boot.2.2.2.2
  have hel := hc.chains.eigen _ ho _ he
  refine ⟨Proof.Judgment.chainsIn_freshC hc.chains hd hel, ⟨e, ?_, ?_⟩, ?_⟩
  · rw [Proof.Judgment.freshClsHeap_get_old ho,
      (Proof.get_constSetIn_fields h d name (.ref h.objs.size) Boot.objectId).2.2.1]
    exact he
  · rw [Proof.Judgment.ancestors_old_freshC hc.chains hsat hel]
    obtain ⟨e', he', hb⟩ := hc.objectEigen
    rw [he] at he'; cases he'; exact hb
  · rw [Proof.Judgment.ancestors_old_freshC hc.chains hsat hc.chains.boot.1]
    exact hc.classBasic

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

/-- The newly registered name denotes the allocated class, not its eigenclass. -/
theorem classNamed_freshClass {h : Heap} {name : String} {e : ObjId}
    (hc : (h.classPayload? Boot.objectId).isSome = true)
    (ho : Boot.objectId < h.objs.size) :
    classNamed? (freshClsHeap h Boot.objectId name name e) name = some h.objs.size := by
  have hn : constOwn (freshClsHeap h Boot.objectId name name e) Boot.objectId name =
      some (.ref h.objs.size) := by
    rw [Proof.Judgment.constOwn_old_freshC ho ho]
    exact Proof.Judgment.constOwn_constSetIn_self hc ho
  have hl : constLookup (freshClsHeap h Boot.objectId name name e) name =
      some (.ref h.objs.size) := by
    cases hp : (freshClsHeap h Boot.objectId name name e).classPayload? Boot.objectId <;>
      simpa only [constLookup, constOwn, hp, Option.bind] using hn
  simp only [classNamed?, hl, Proof.Judgment.freshClsHeap_cp_k, Option.isSome_some, ite_true]

#print axioms ClassReady.freshClass
#print axioms stepFn_class_fresh
#print axioms classNamed_freshClass
end Ratchet.Denote
