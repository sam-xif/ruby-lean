import Denote.Sem.Names.SuperLookup
import Denote.Rules.Instance.InstanceResolve

/-! The actual super dispatch enters the parent body on the existing receiver. This
establishes lookup and parameter binding only; nested initializer return still needs its
anchored field-preservation contract. Full conformance identifies the method activation. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem methodFrame_current {m : Machine} (hs : m.stack ≠ []) (hk : m.currentFrame.kind ≠ .block) :
    m.frames.getD (Interp.methodFrameOf m) default = m.currentFrame := by
  cases he : m.stack with
  | nil => exact False.elim (hs he)
  | cons i ids =>
    simp only [Machine.currentFrame, he] at hk ⊢
    simp only [Interp.methodFrameOf, he, List.headD_cons]

theorem doSuper_user {m : Machine} {name : String} {owner : ObjId} {md : MethodDef}
    {args : List Value} {blk : Option Value}
    (hs : m.stack ≠ []) (hk : m.currentFrame.kind ≠ .block) (hn : m.currentFrame.meth = name) (hne : name ≠ "")
    (hl : Interp.superFound m.heap (classOf m.heap m.currentFrame.self)
      m.currentFrame.defmod name = some (owner, md)) (hb : md.builtin = none) :
    Interp.doSuper m args blk = Interp.enterUserMethod m m.currentFrame.self name md args blk := by
  simp only [Interp.doSuper, methodFrame_current hs hk, hn, beq_eq_false_iff_ne.mpr hne,
    Bool.false_eq_true, ↓reduceIte, hl, hb]

/-- Required positional super arguments bind using the existing receiver and a fresh
method frame. No object allocation or ordinary receiver dispatch occurs here. -/
theorem doSuper_required {m : Machine} {name : String} {owner : ObjId} {md : MethodDef}
    {args : List Value} {names : List String}
    (hs : m.stack ≠ []) (hk : m.currentFrame.kind ≠ .block) (hn : m.currentFrame.meth = name) (hne : name ≠ "")
    (hl : Interp.superFound m.heap (classOf m.heap m.currentFrame.self)
      m.currentFrame.defmod name = some (owner, md)) (hb : md.builtin = none)
    (hp : md.params = names.map RubyCore.Param.req) (hcap : md.capturedFrame = none)
    (hdecl : md.declared = []) (ha : args.length = names.length) :
    Interp.doSuper m args none = .next (Interp.withKont
      (pushMethodFrame m (requiredFrame m.currentFrame.self name md names args))
      (.eval md.body) (.frameK m.frames.size)) := by
  rw [doSuper_user hs hk hn hne hl hb]
  exact enterUserMethod_required _ _ _ _ _ _ hp hcap hdecl ha

/-- Full conformance supplies receiver identity, lexical owner, method activation and code. -/
theorem declared_super_dispatch {κ : Ctx} {Γ : Env} {I fields : Ty} {m : Machine}
    {receiver : Cls} {current owner : String} {d : Defn} {args : List Value} {blk : Option Value}
    (hm : StateOk κ Γ I m) (hr : receiver ∈ κ.classes)
    (hf : κ.frame = some ⟨receiver.name, current, d.name⟩)
    (hc : κ.scope.runtimeClass = some current)
    (ht : κ.selfTy = some (.inst receiver.name fields))
    (hn : d.name ≠ "")
    (route : SuperRoute κ.classes receiver.name current owner d) :
    ∃ k md, classNamed? m.heap owner = some k ∧ md.params = toRubyParams d.params ∧
      md.body = toRuby d.body ∧ InstanceMethodCode k d.name md ∧
      Interp.doSuper m args blk = Interp.enterUserMethod m m.currentFrame.self d.name md args blk := by
  obtain ⟨r, hrn, _⟩ := hm.classes receiver hr
  obtain ⟨currentId, scope⟩ := hm.classRuntime current hc
  obtain ⟨k, md, hkn, hl, hp, hb, _, code⟩ := declared_super_code hm hr hrn scope.named route
  have hv : denM (.inst receiver.name fields) m m.currentFrame.self := by
    simpa only [SelfTyOk, ht] using hm.selfTy
  rw [denM] at hv
  have hco := exactInst_classOf hv.1 hrn
  have hname : m.currentFrame.meth = d.name := by
    have h := hm.frame
    simp only [FrameOk, hf] at h
    exact h.1
  have hk : m.currentFrame.kind ≠ .block := by
    have h := hm.frame
    simp only [FrameOk, hf] at h
    rw [h.2.2]
    decide
  refine ⟨k, md, hkn, hp, hb, code, ?_⟩
  exact doSuper_user hm.frameInRange.1 hk hname hn
    (by simpa only [hco, scope.owner] using hl) code.builtin

#print axioms methodFrame_current
#print axioms doSuper_required
#print axioms declared_super_dispatch
end Ratchet.Denote.Typed
