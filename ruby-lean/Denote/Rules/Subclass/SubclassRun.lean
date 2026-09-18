import Denote.Rules.Subclass.SubclassBodyRun
import Denote.Rules.Subclass.SubclassHeaderEntry

/-! A resolved superclass value enters, publishes the actual header, executes a checked
body and restores full caller conformance. No body is proved by its signature or caller. -/
set_option autoImplicit false
namespace Ratchet.Denote.Subclass
open RubyCore Ratchet Ratchet.Denote.Typed RubyCore.Interp

theorem resolved_runSpec {κ κb : Ctx} {Γ Γb : Env} {I Ib τ : Ty} {m : Machine}
    {c : Cls} {name : String} {parent : ObjId} {body : Ratchet.Expr}
    (hm : StateOk κ Γ I m) (ht : ReframeFO (returnScopeCtx κ κb) I) (ha : κ.asms = [])
    (hr : κ.scope.runtimeMain = true) (hf : κ.frame = none)
    (hw : κb.pos.mainWorld = true) (hcl : κ.scope.runtimeClass = none)
    (hq : κb.scope.runtimeClass = some name)
    (hk : ∀ x, constGet? κb x = constGet? (returnScopeCtx κ κb) x)
    (hΓ : ∀ p ∈ Γ, FirstOrder (stripAlias p.2) = true) (hτ : FirstOrder τ = true)
    (htables : ClassTablesFrame κ name m) (hnative : FreshClass.nativeFrameB κ name = true)
    (hfresh : freshClassNameB κ name = true) (hne : name.isEmpty = false)
    (hc : c ∈ κ.classes) (hp : classNamed? m.heap c.name = some parent)
    (hbase : subclassBaseFrameB κ c.name = true)
    (halloc : c.name ∈ κ.pos.plainAlloc) (hquiet : FreshClass.NativeQuiet name "new")
    (hnew : smroGet? κ.classes c.name "new" = none)
    (hframe : subclassHeaderFrameB κ.classes name c.name = true)
    (hplain : unqualifiedClassB name = true)
    (hb : SemSafeCtxA (subclassHeaderCtx (classBodyCtx κ name) name c.name) [] .ivar0 body τ κb Γb Ib) :
    RunSpec m (deliverA (.val (.ref parent)) m [.classDefK name (toRuby body)])
      Γ τ (returnScopeCtx κ κb) I := by
  have ready := hm.runtime hr
  have caps := ParentCaps.of_declared hm hc hp hbase
  obtain ⟨ep, he, _, _⟩ := caps.metaclass
  have hn := hm.freshClassName hfresh
  let start := reCtl m (.value (.ref parent)) []
  let entry := machine start Boot.objectId m.currentFrame.cref name name parent ep (toRuby body)
  have hstart : StateOk κ Γ I start := StateOk_reCtl hm _ []
  have hentry : StateOk (classBodyCtx κ name) [] .ivar0 entry :=
    state hstart hr hf ha (htables.heap rfl) (FreshClass.nativeFrameB_sound hnative) hn hne caps he
  have hheader := publish_header hstart hr hentry hc hp halloc he hn hne hquiet hnew
    (subclassHeaderFrameB_sound hframe) hplain rfl
  have hrun := body_runSpec hstart ht ha hr hw hcl rfl hq hk hΓ hτ hc hp hn he (hb entry hheader)
  have hmod := (hm.declCls c hc parent hp).2.2.2.1
  obtain ⟨cp, hcp, hfalse⟩ : ∃ cp, m.heap.classPayload? parent = some cp ∧ cp.isModule = false := by
    cases he : m.heap.classPayload? parent with
    | none => simp only [he, Option.map_none, reduceCtorEq] at hmod
    | some cp => exact ⟨cp, rfl, Option.some.inj (by simpa only [he, Option.map_some] using hmod)⟩
  have hs : stepFn (deliverA (.val (.ref parent)) m [.classDefK name (toRuby body)]) = .next entry := by
    simpa only [deliverA, Answer.ctl, currentFrame_reCtl, ready.owner] using
      step_resolved (m := deliverA (.val (.ref parent)) m [.classDefK name (toRuby body)])
        (q := name) rfl rfl hcp hfalse
        (by change constOwn m.heap m.currentFrame.defmod name = none; rwa [ready.owner])
        (by change m.currentFrame.defmod < m.heap.objs.size; rw [ready.owner]; exact hm.core.classReady.chains.boot.2.2.2.2)
        (lt_size_of_classPayload caps.classLive) he
        (by change (if m.currentFrame.defmod == Boot.objectId then name
              else className m.heap m.currentFrame.defmod ++ "::" ++ name) = name
            simp only [ready.owner, beq_self_eq_true, ite_true]) hne
  exact RunSpec.step (by rfl) hs (hrun.rebase (Framed_reCtl m _ []))

#print axioms resolved_runSpec
end Ratchet.Denote.Subclass
