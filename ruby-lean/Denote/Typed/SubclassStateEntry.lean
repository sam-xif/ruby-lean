import Denote.Sem.SubclassState
import Denote.Sem.ClassFreshness
import Denote.Typed.SubclassEntry

/-! Full conformance through the actual fresh-subclass entry. These statements are
class/body-generic; entry does not certify an unexecuted body or publish a signature. -/
set_option autoImplicit false
namespace Ratchet.Denote.Subclass
open RubyCore Ratchet RubyCore.Interp

theorem enter_declared_state {κ : Ctx} {Γ : Env} {I : Ty}
    {m : Machine} {c : Cls} {parent : ObjId} {name : String} {body : RubyCore.Expr}
    (hm : StateOk κ Γ I m) (hr : κ.scope.runtimeMain = true)
    (hf : κ.frame = none) (ha : κ.asms = [])
    (ht : ClassTablesFrame κ name m) (hq : FreshClass.nativeFrameB κ name = true)
    (hc : c ∈ κ.classes) (hp : classNamed? m.heap c.name = some parent)
    (hb : subclassBaseFrameB κ c.name = true)
    (hn : constOwn m.heap Boot.objectId name = none) (hne : name.isEmpty = false) :
    ∃ n, enterClassBody m name false (some parent) body = .next n ∧
      StateOk (classBodyCtx κ name) [] .ivar0 n := by
  have caps := ParentCaps.of_declared hm hc hp hb
  obtain ⟨ep, he, _, _⟩ := caps.metaclass
  have ready := hm.runtime hr
  refine ⟨machine m Boot.objectId m.currentFrame.cref name name parent ep body, ?_,
    state hm hr hf ha ht (FreshClass.nativeFrameB_sound hq) hn hne caps he⟩
  simpa only [ready.owner] using enter_fresh (m := m) (q := name) (body := body)
    (by simpa only [ready.owner] using hn)
    (by simpa only [ready.owner] using hm.core.classReady.chains.boot.2.2.2.2)
    (lt_size_of_classPayload caps.classLive) he
    (by simp only [ready.owner, beq_self_eq_true, ite_true]) hne

/-- The superclass continuation must reject modules before invoking the entry operation.
Its parent class record, not a certificate-supplied heap payload, proves that check. -/
theorem step_declared_state {κ : Ctx} {Γ : Env} {I : Ty}
    {m : Machine} {c : Cls} {parent : ObjId} {name : String} {body : RubyCore.Expr}
    {rest : List Kont} (hm : StateOk κ Γ I m)
    (hctl : m.ctl = .value (.ref parent)) (hkont : m.kont = .classDefK name body :: rest)
    (hr : κ.scope.runtimeMain = true) (hf : κ.frame = none) (ha : κ.asms = [])
    (ht : ClassTablesFrame κ name m) (hq : FreshClass.nativeFrameB κ name = true)
    (hc : c ∈ κ.classes) (hp : classNamed? m.heap c.name = some parent)
    (hb : subclassBaseFrameB κ c.name = true)
    (hn : freshClassNameB κ name = true) (hne : name.isEmpty = false) :
    ∃ n, stepFn m = .next n ∧ StateOk (classBodyCtx κ name) [] .ivar0 n := by
  have hmod := (hm.declCls c hc parent hp).2.2.2.1
  obtain ⟨cp, hcp, hfalse⟩ : ∃ cp, m.heap.classPayload? parent = some cp ∧ cp.isModule = false := by
    cases he : m.heap.classPayload? parent with
    | none => simp only [he, Option.map_none, reduceCtorEq] at hmod
    | some cp => exact ⟨cp, rfl, Option.some.inj (by simpa only [he, Option.map_some] using hmod)⟩
  obtain ⟨n, he, hs⟩ := enter_declared_state
    (StateOk_reCtl hm m.ctl rest) hr hf ha (ht.heap rfl) hq hc hp hb
    (hm.freshClassName hn) hne
  refine ⟨n, ?_, hs⟩
  simpa only [stepFn, hctl, applyKont, hkont, hcp, hfalse, Bool.false_eq_true, ↓reduceIte]
    using he

#print axioms enter_declared_state
#print axioms step_declared_state
end Ratchet.Denote.Subclass
