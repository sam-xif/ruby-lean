import Denote.Typed.ClassRun
import Denote.Sem.ClassHeader
import Denote.Sem.ClassFreshness

/-! Execute a class body in its published header context and retain its outgoing tables
after restoring the caller. The body contract must include annotated definition proofs. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote
open RubyCore.Proof.Judgment (freshClsMachine)

theorem class_header_runSpec {κ κb : Ctx} {Γ Γb : Env} {I Ib τ : Ty} {m : Machine}
    {name : String} {body : Ratchet.Expr}
    (hm : StateOk κ Γ I m) (ht : ReframeFO (returnScopeCtx κ κb) I) (ha : κ.asms = [])
    (hr : κ.scope.runtimeMain = true) (hf : κ.frame = none) (hin : κ.pos.mainWorld = true)
    (hw : κb.pos.mainWorld = true) (hcl : κ.scope.runtimeClass = none)
    (hq : κb.scope.runtimeClass = some name)
    (hk : ∀ x, constGet? κb x = constGet? (returnScopeCtx κ κb) x)
    (hΓ : ∀ p ∈ Γ, FirstOrder (stripAlias p.2) = true) (hτ : FirstOrder τ = true)
    (htables : ClassTablesFrame κ name m) (hnative : FreshClass.nativeFrameB κ name = true)
    (hfresh : freshClassNameB κ name = true) (hne : name.isEmpty = false)
    (hnew : nameFreeN κ "new" = true) (hquiet : FreshClass.NativeQuiet name "new")
    (hplain : unqualifiedClassB name = true) (hframe : headerTableFrameB κ.classes name = true)
    (hb : SemSafeCtxA (classHeaderCtx (classBodyCtx κ name) name) [] .ivar0 body τ κb Γb Ib) :
    RunSpec m (evalFrom m (.class' name none body)) Γ τ (returnScopeCtx κ κb) I := by
  have hn := hm.freshClassName hfresh
  obtain ⟨e, he, hs⟩ := stepFn_class_fresh (body := body) hm hr hn hne
  let start := evalFrom m (.class' name none body)
  have hstart : StateOk κ Γ I start := StateOk_reCtl hm _ []
  have hentry : StateOk (classBodyCtx κ name) [] .ivar0
      (freshClsMachine start Boot.objectId m.currentFrame.cref name name e (toRuby body)) :=
    FreshClass.state hstart hr hf ha (htables.heap rfl)
      (FreshClass.nativeFrameB_sound hnative) hn hne he
  have hheader := StateOk_publish_header hentry rfl hplain
    (FreshClass.declared_header hm.core.classReady hm.sat hm.core.rootNames
      (hm.runtime hr).classLive hn hne he hquiet ((hm.mainSite hin).newDispatch hnew) rfl
      hm.classes hm.declCls (headerTableFrameB_sound hframe))
    ⟨m.heap.objs.size, classNamed_freshClass (hm.runtime hr).classLive
      hm.core.classReady.chains.boot.2.2.2.2, FreshClass.plain hm.core hm.sat⟩
    (FreshClass.ownNames_header hm.core.classReady.chains.boot.2.2.2.2
      (hm.runtime hr).classLive hn hm.classes hm.ownNames)
  have hrun := class_body_runSpec hstart ht ha hr hw hcl rfl hq hk hΓ hτ hn he (hb _ hheader)
  exact RunSpec.step (answerPoint_evalFrom _ _) hs (hrun.rebase (Framed_reCtl m _ []))

#print axioms class_header_runSpec
end Ratchet.Denote.Typed
