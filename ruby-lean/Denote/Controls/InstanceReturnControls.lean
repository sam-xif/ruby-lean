import Denote.Sem.Heap.WriteState
import Denote.Sem.Core.DataPres
import Denote.Rules.Instance.InstanceReturn
import Denote.Controls.ClassStateControls

/-! First-order value types do not observe fields of objects with eigenclasses.
Caller restoration must preserve those field observations separately. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem eigen_write_dataPres {m : Machine} {o e : ObjId} (x : String) (v : Value)
    (hs : m.currentFrame.self = .ref o) (he : (m.heap.get o).eigen = some e) :
    DataPres m.heap (Interp.bindIvar m x v).heap := by
  have hi := bindIvar_ivarOnly m x v
  refine ⟨fun w cn hw => by rwa [bindIvar_isAName],
    fun cn k hk => by rwa [bindIvar_classNamed], ?_, ?_, ?_⟩
  · intro w cn hw
    refine ⟨by rwa [bindIvar_isExactInst], ivarOf_bindIvar_other hs ?_⟩
    intro h; subst w
    cases hc : classNamed? m.heap cn <;> simp [isExactInst, hc, he] at hw
  · intro w xs hw
    cases w <;> simpa only [arrElems?, hi.payload] using hw
  · intro w es hw
    cases w <;> simpa only [hshEntries?, hi.payload] using hw

/-- All five old frame clauses hold, while the caller's closed self-spine is destroyed.
This is a countermodel to the contract, not a claim that the current checker admits a write. -/
theorem eigen_write_old_frame {m : Machine} {o e : ObjId} {x : String}
    (hs : m.currentFrame.self = .ref o) (he : (m.heap.get o).eigen = some e)
    (ho : o < m.heap.objs.size) :
    (Interp.bindIvar m x (.int 7)).stack = m.stack ∧
      (∀ k, (m.heap.classPayload? k).isSome = true →
        ((Interp.bindIvar m x (.int 7)).heap.classPayload? k).isSome = true) ∧
      (∀ v cn, isAName m.heap v cn = true →
        isAName (Interp.bindIvar m x (.int 7)).heap v cn = true) ∧
      (∀ τ, FirstOrder τ = true → ∀ v, denM τ m v →
        denM τ (Interp.bindIvar m x (.int 7)) v) ∧
      FramePres m (Interp.bindIvar m x (.int 7)) ∧
      ¬ SelfSpineOk .ivar0 (Interp.bindIvar m x (.int 7)) := by
  have hi := bindIvar_ivarOnly m x (.int 7)
  have hp := eigen_write_dataPres x (.int 7) hs he
  refine ⟨by simp, fun k hk => by rwa [hi.classPayload],
    hp.nominal, fun _ ht _ hv => hp.denM ht hv, .bindIvar m x (.int 7), ?_⟩
  intro bad
  have hn := bad.2 x rfl rfl
  rw [bindIvar_currentFrame, hs, ivarOf_bindIvar_self hs ho] at hn
  cases hn

/-- The new field clause excludes the witness independently of nominal/exact typing. -/
theorem nil_field_write_not_framed {m : Machine} {o : ObjId} {x : String}
    (hs : m.currentFrame.self = .ref o) (ho : o < m.heap.objs.size)
    (hn : ivarOf m.heap (.ref o) x = .nil) :
    ¬ Framed m (Interp.bindIvar m x (.int 7)) := by
  intro bad
  have hv := bad.fields.typed o ho x .nilT rfl (by rw [hn, denM]; rfl)
  rw [ivarOf_bindIvar_self hs ho, denM] at hv
  cases hv

/-- The blind spot occurs at a fully conformant, real fresh-class entry, not just an
arbitrary heap. The injected write preserves value types but loses a known nil field. -/
theorem boot_class_field_frame_gap (hb : bootOkB = true) {name : String}
    (hq : FreshClass.nativeFrameB ctx0 name = true)
    (hn : constOwn bootMachine.heap Boot.objectId name = none) (hne : name.isEmpty = false) :
    ∃ n, Interp.stepFn (evalFrom bootMachine (.class' name none .nil)) = .next n ∧
      StateOk (classBodyCtx ctx0 name) [] .ivar0 n ∧
      DataPres n.heap (Interp.bindIvar n "@extra" (.int 7)).heap ∧
      ¬ Framed n (Interp.bindIvar n "@extra" (.int 7)) := by
  open RubyCore.Proof.Judgment in
  have hm := stateOk_boot hb
  obtain ⟨e, he, hstep⟩ := stepFn_class_fresh (body := .nil) hm rfl hn hne
  let start := evalFrom bootMachine (.class' name none .nil)
  let n := freshClsMachine start Boot.objectId start.currentFrame.cref name name e .nil
  have hs : n.currentFrame.self = .ref bootMachine.heap.objs.size :=
    congrArg RubyCore.Frame.self FreshClass.current_frame
  have hl := FreshClass.self_live (m := start) (name := name) (e := e) (body := .nil)
  have heigen : (n.heap.get bootMachine.heap.objs.size).eigen =
      some (bootMachine.heap.objs.size + 1) := by
    change ((freshClsHeap bootMachine.heap Boot.objectId name name e).get
      bootMachine.heap.objs.size).eigen = _
    rw [freshClsHeap_get_k]
  refine ⟨n, hstep, ?_, eigen_write_dataPres "@extra" (.int 7) hs heigen,
    nil_field_write_not_framed hs (hl _ hs) ?_⟩
  · exact FreshClass.state (StateOk_reCtl hm _ []) rfl rfl rfl
      (ClassTablesFrame.empty rfl rfl) (FreshClass.nativeFrameB_sound hq) hn hne he
  · rw [← hs]
    exact FreshClass.ivar_nil "@extra"

-- Real definition, instance call with a different self, then a read of the caller's field.
#guard match Interp.run 250 (evalFrom bootMachine (.class' "Point" none (.seq [
    .def' "answer" [] (.int 1),
    .send (some (.send (some (.const "Point")) "new" [] none)) "answer" [] none,
    .var .ivar "@extra"]))) with
  | .value .nil _ => true
  | _ => false

#print axioms eigen_write_dataPres
#print axioms eigen_write_old_frame
#print axioms nil_field_write_not_framed
#print axioms boot_class_field_frame_gap
end Ratchet.Denote.Typed
