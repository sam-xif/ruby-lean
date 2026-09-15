import Denote.Typed.SubclassStateEntry
import Denote.Sem.SubclassHeader

/-! Actual subclass entry publishes only the executed header. The body is still arbitrary
and unexecuted; a later class rule must consume its full checked-body contract. -/
set_option autoImplicit false
namespace Ratchet.Denote.Subclass
open RubyCore Ratchet RubyCore.Interp

theorem enter_declared_header {κ : Ctx} {Γ : Env} {I : Ty}
    {m : Machine} {c : Cls} {parent : ObjId} {name : String} {body : RubyCore.Expr}
    (hm : StateOk κ Γ I m) (hr : κ.scope.runtimeMain = true)
    (hf : κ.frame = none) (ha : κ.asms = [])
    (ht : ClassTablesFrame κ name m) (hq : FreshClass.nativeFrameB κ name = true)
    (hc : c ∈ κ.classes) (hp : classNamed? m.heap c.name = some parent)
    (hb : subclassBaseFrameB κ c.name = true)
    (hn : freshClassNameB κ name = true) (hne : name.isEmpty = false)
    (halloc : c.name ∈ κ.pos.plainAlloc) (hquiet : FreshClass.NativeQuiet name "new")
    (hnew : smroGet? κ.classes c.name "new" = none)
    (hframe : subclassHeaderFrameB κ.classes name c.name = true)
    (hplain : unqualifiedClassB name = true) :
    ∃ n, enterClassBody m name false (some parent) body = .next n ∧
      StateOk (subclassHeaderCtx (classBodyCtx κ name) name c.name) [] .ivar0 n := by
  have caps := ParentCaps.of_declared hm hc hp hb
  obtain ⟨ep, he, _, _⟩ := caps.metaclass
  have ready := hm.runtime hr
  have fresh := hm.freshClassName hn
  refine ⟨machine m Boot.objectId m.currentFrame.cref name name parent ep body, ?_, ?_⟩
  · simpa only [ready.owner] using enter_fresh (m := m) (q := name) (body := body)
      (by simpa only [ready.owner] using fresh)
      (by simpa only [ready.owner] using hm.core.classReady.chains.boot.2.2.2.2)
      (lt_size_of_classPayload caps.classLive) he
      (by simp only [ready.owner, beq_self_eq_true, ite_true]) hne
  · exact publish_header hm hr (state hm hr hf ha ht (FreshClass.nativeFrameB_sound hq) fresh hne caps he)
      hc hp halloc he fresh hne hquiet hnew (subclassHeaderFrameB_sound hframe) hplain rfl

#print axioms enter_declared_header
end Ratchet.Denote.Subclass
