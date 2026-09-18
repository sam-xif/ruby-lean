import Denote.Rules.Instance.InstanceEntry
import Denote.Rules.Method.MethodResolve
import Denote.Sem.Instance.InstanceSite

/-! Installed instance-method resolution and real explicit dispatch. A method record is
not a body proof; this layer supplies the code which an annotation-checked body must cover.
No-prepend and ordinary-payload obligations remain visible, not inferred from a class name. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem exactInst_receiver {h : Heap} {recv : Value} {cn : String} {k : ObjId}
    (hv : isExactInst h recv cn = true) (hk : classNamed? h cn = some k) :
    ∃ o, recv = .ref o ∧ o < h.objs.size ∧ (h.get o).eigen = none ∧ (h.get o).klass = k := by
  cases recv <;> simp only [isExactInst, hk, Bool.false_eq_true] at hv
  rename_i o
  simp only [Bool.and_eq_true, decide_eq_true_eq, Option.isNone_iff_eq_none, beq_iff_eq] at hv
  exact ⟨o, rfl, hv.1.1, hv.1.2, hv.2⟩

theorem exactInst_classOf {h : Heap} {recv : Value} {cn : String} {k : ObjId}
    (hv : isExactInst h recv cn = true) (hk : classNamed? h cn = some k) :
    classOf h recv = k := by
  obtain ⟨o, rfl, _, he, hc⟩ := exactInst_receiver hv hk
  simp only [classOf, he, hc]

theorem classesOk_lookup {C : CTable} {m : Machine} {c : Cls} {d : Defn}
    {recv : Value} {I : Ty} (hm : ClassesOk C m) (hc : c ∈ C) (hd : d ∈ c.methods)
    (hv : denM (.inst c.name I) m recv)
    (hf : ∀ k, classNamed? m.heap c.name = some k → classFrontB m.heap k = true) :
    ∃ k md, classNamed? m.heap c.name = some k ∧
      lookup m.heap recv d.name = some (k, md) ∧
      md.params = toRubyParams d.params ∧ md.body = toRuby d.body ∧
      md.undefined = false ∧ InstanceMethodCode k d.name md := by
  obtain ⟨k, hk, hm⟩ := hm c hc
  obtain ⟨md, hm, hp, hb, hu, hcode⟩ := hm d hd
  rw [denM] at hv
  obtain ⟨rest, hrest⟩ := classFrontB_sound (hf k hk)
  have hco := exactInst_classOf hv.1 hk
  exact ⟨k, md, hk, lookup_own_first (by rw [hco]; exact hrest) hm, hp, hb, hu, hcode⟩

theorem instance_required_frame_at {m : Machine} {recv : Value} {cn ownerCn name : String}
    {r k : ObjId} {md : MethodDef} {I : Ty} (names : List String) (args : List Value)
    (hk : classNamed? m.heap cn = some r) (hv : denM (.inst cn I) m recv)
    (hf : classFrontB m.heap r = true) (hc : InstanceMethodCode k name md) :
    FrameOk (some ⟨cn, ownerCn, name⟩) (pushMethodFrame m (requiredFrame recv name md names args)) := by
  rw [denM] at hv
  have hco := exactInst_classOf hv.1 hk
  obtain ⟨rest, ha⟩ := classFrontB_sound hf
  simp only [FrameOk, currentFrame_pushMethodFrame, requiredFrame, hc.superName, Option.getD_none]
  refine ⟨trivial, ?_⟩
  change isAName m.heap recv cn = true
  simp only [isAName, hk, isA, hco, ha, List.contains_cons, beq_self_eq_true, Bool.true_or]

theorem instance_required_frame {m : Machine} {recv : Value} {cn name : String}
    {k : ObjId} {md : MethodDef} {I : Ty} (names : List String) (args : List Value)
    (hk : classNamed? m.heap cn = some k) (hv : denM (.inst cn I) m recv)
    (hf : classFrontB m.heap k = true) (hc : InstanceMethodCode k name md) :
    FrameOk (some ⟨cn, cn, name⟩) (pushMethodFrame m (requiredFrame recv name md names args)) :=
  instance_required_frame_at names args hk hv hf hc

theorem instance_required_live {m : Machine} {recv : Value} {cn name : String}
    {k : ObjId} {I : Ty} (md : MethodDef) (names : List String) (args : List Value)
    (hk : classNamed? m.heap cn = some k) (hv : denM (.inst cn I) m recv) :
    SelfLive (pushMethodFrame m (requiredFrame recv name md names args)) := by
  rw [denM] at hv
  obtain ⟨o, rfl, hl, _, _⟩ := exactInst_receiver hv.1 hk
  intro j hj
  rw [currentFrame_pushMethodFrame] at hj
  change Value.ref o = .ref j at hj
  cases hj
  exact hl

theorem instance_required_scope {m : Machine} {recv : Value} {cn name : String}
    {k : ObjId} {md : MethodDef} (names : List String) (args : List Value)
    (hk : classNamed? m.heap cn = some k) (hl : k < m.heap.objs.size)
    (hc : InstanceMethodCode k name md) (hp : m.preludeMode = false)
    (hh : definitionHookQuietB m.heap k = true) :
    ClassScopeAt cn k (pushMethodFrame m (requiredFrame recv name md names args)) := by
  refine ⟨hk, hl, ?_, ?_, ?_, hp, ?_, hh⟩
  · rw [currentFrame_pushMethodFrame]; exact hc.owner
  · rw [currentFrame_pushMethodFrame]; exact hc.cref
  · rw [currentFrame_pushMethodFrame]; rfl
  · simp only [defaultDefVis, currentFrame_pushMethodFrame, requiredFrame]; rfl

theorem finishSend_instance {m : Machine} {o k : ObjId} {name : String} {md : MethodDef}
    {args : List Value} {rest : List ObjId}
    (hp : (m.heap.get o).payload = .none)
    (hl : lookup m.heap (.ref o) name = some (k, md)) (hu : md.undefined = false)
    (hc : InstanceMethodCode k name md) (hn : name ≠ "initialize")
    (ha : ancestors m.heap (classOf m.heap (.ref o)) = k :: rest) :
    Interp.finishSend m (.ref o) .explicit name args .none =
      Interp.enterUserMethod m (.ref o) name md args none := by
  apply invoke_ordinary_userMethod hp hl hc.builtin hu hc.fromPrelude
  · simp [Interp.visError?, hc.visibility, hn]
  · simp [ha, Interp.crubyShadow]; rfl

theorem classesOk_explicit_entry {C : CTable} {m : Machine} {c : Cls} {d : Defn}
    {recv : Value} {I : Ty} {args : List Value}
    (hm : ClassesOk C m) (hc : c ∈ C) (hd : d ∈ c.methods)
    (hv : denM (.inst c.name I) m recv)
    (hf : ∀ k, classNamed? m.heap c.name = some k → classFrontB m.heap k = true)
    (hp : ∀ o, recv = .ref o → (m.heap.get o).payload = .none) (hn : d.name ≠ "initialize") :
    ∃ k md, md.params = toRubyParams d.params ∧ md.body = toRuby d.body ∧
      InstanceMethodCode k d.name md ∧
      Interp.finishSend m recv .explicit d.name args .none =
        Interp.enterUserMethod m recv d.name md args none := by
  obtain ⟨k, md, hk, hl, hparams, hbody, hu, hcode⟩ := classesOk_lookup hm hc hd hv hf
  rw [denM] at hv
  have hco := exactInst_classOf hv.1 hk
  obtain ⟨o, rfl, _, _, _⟩ := exactInst_receiver hv.1 hk
  obtain ⟨rest, ha⟩ := classFrontB_sound (hf k hk)
  exact ⟨k, md, hparams, hbody, hcode,
    finishSend_instance (hp o rfl) hl hu hcode hn (by rw [hco]; exact ha)⟩

#print axioms classFrontB_sound
#print axioms classesOk_lookup
#print axioms instance_required_frame
#print axioms instance_required_frame_at
#print axioms instance_required_live
#print axioms instance_required_scope
#print axioms classesOk_explicit_entry
end Ratchet.Denote.Typed
