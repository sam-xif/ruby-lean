import Denote.Rules.Method.MethodState
import Denote.Sem.Instance.MethodHeap
import Denote.Sem.Instance.UserDispatch
import Denote.Sem.Instance.DefinitionHook

/-! The ordinary method's installation and dispatch paths. These are interpreter
equalities, not annotation-based admission: safety still consumes the checked body.
-/

set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

/-- The source `def` record, before the mutation protocol's privacy normalization. -/
def sourceMethod (m : Machine) (ps : List RubyCore.Param)
    (body : RubyCore.Expr) : MethodDef :=
  { params := ps, body, owner := m.currentFrame.defmod,
    definee := some m.currentFrame.defmod, cref := m.currentFrame.cref,
    fromPrelude := m.preludeMode || m.currentFrame.libraryOrigin,
    visibility := m.currentDefinitionFrame.defVis }

def definedMethod (m : Machine) (name : String) (ps : List RubyCore.Param)
    (body : RubyCore.Expr) : MethodDef :=
  Interp.normalizeDefinitionVisibility m.heap m.currentFrame.defmod name (sourceMethod m ps body)

theorem sourceMethod_reCtl (m : Machine) (c : Ctl) (k : List Kont)
    (ps : List RubyCore.Param) (body : RubyCore.Expr) :
    sourceMethod (reCtl m c k) ps body = sourceMethod m ps body := by
  simp only [sourceMethod, currentDefinitionFrame_reCtl]
  rfl

def installMethod (m : Machine) (name : String) (ps : List RubyCore.Param)
    (body : RubyCore.Expr) : Machine :=
  let md := definedMethod m name ps body
  { m with heap := defineMethod m.heap m.currentFrame.defmod name md }

theorem definedMethod_params (m : Machine) (name : String) (ps : List RubyCore.Param)
    (body : RubyCore.Expr) : (definedMethod m name ps body).params = ps := by
  unfold definedMethod Interp.normalizeDefinitionVisibility
  split <;> rfl

theorem definedMethod_body (m : Machine) (name : String) (ps : List RubyCore.Param)
    (body : RubyCore.Expr) : (definedMethod m name ps body).body = body := by
  unfold definedMethod Interp.normalizeDefinitionVisibility
  split <;> rfl

theorem definedMethod_undefined (m : Machine) (name : String) (ps : List RubyCore.Param)
    (body : RubyCore.Expr) : (definedMethod m name ps body).undefined = false := by
  unfold definedMethod Interp.normalizeDefinitionVisibility
  split <;> rfl

theorem definedMethod_code {m : Machine} {name : String} {ps : List RubyCore.Param}
    {body : RubyCore.Expr} (ho : m.currentFrame.defmod = Boot.objectId)
    (hc : m.currentFrame.cref = []) (hp : m.preludeMode = false)
    (hlib : m.currentFrame.libraryOrigin = false) :
    TopMethodCode (definedMethod m name ps body) := by
  unfold definedMethod Interp.normalizeDefinitionVisibility
  split <;> exact ⟨ho, hc, rfl, rfl, rfl, rfl, by simp [sourceMethod, hp, hlib],
    rfl, rfl, rfl, ho, rfl⟩

/-- Only the installed native no-op hook is covered by ordinary definitions. -/
def DefHookQuiet (m : Machine) : Prop :=
  definitionHookQuietB m.heap m.currentFrame.defmod = true

def defHookQuietB (m : Machine) : Bool := definitionHookQuietB m.heap m.currentFrame.defmod

theorem defHookQuietB_sound {m : Machine} (h : defHookQuietB m = true) : DefHookQuiet m := h

theorem mainReady_defHookQuiet {m : Machine} (h : MainReady m) : DefHookQuiet m :=
  defHookQuietB_sound (by
    unfold defHookQuietB
    rw [h.owner]
    exact h.hook)

theorem defHookQuiet_install {m : Machine} {name : String} {ps : List RubyCore.Param}
    {body : RubyCore.Expr} (hn : "method_added" ≠ name) (hh : DefHookQuiet m) :
    DefHookQuiet (installMethod m name ps body) := by
  unfold DefHookQuiet definitionHookQuietB installMethod
  dsimp only
  rw [Proof.lookup_defineMethod _ _ _ _ _ _ hn (Proof.classOf_defineMethod ..)]
  exact hh

theorem step_def_install {m : Machine} {name : String} {ps : List RubyCore.Param}
    {body : RubyCore.Expr} (hc : m.ctl = .eval (.def' name ps body))
    (hp : m.preludeMode = false)
    (hw : frozenMethodReceiver? m.heap m.currentFrame.defmod = none)
    (hd : (m.heap.classPayload? m.currentFrame.defmod).bind (·.attached) = none) :
    Interp.stepFn m = .next
      { installMethod m name ps body with
        ctl := .send (.ref m.currentFrame.defmod) .reflective "method_added" [.sym name] none [],
        kont := .methodEditsK [] (.sym name) :: m.kont } := by
  simp only [Interp.stepFn, hc, Interp.evalExpr, hw]
  simp only [Interp.runMethodEdits, hw, Interp.finishMethodEdit, hp,
    Bool.false_or, installMethod, definedMethod, sourceMethod,
    attached_defineMethod, hd, Option.getD_none, Option.isSome_none]
  rfl

/-- Consume the real queued callback and its edit continuation. A native shadow
gate remains a gate; successful native dispatch resumes with the definition name. -/
theorem definition_hook_runSpec {origin n : Machine} {κ : Ctx} {Γ : Env} {I : Ty}
    {name : String} {k : ObjId}
    (hn : StateOk κ Γ I n) (hf : Framed origin n)
    (hc : (n.heap.classPayload? k).isSome = true)
    (hh : definitionHookQuietB n.heap k = true) :
    RunSpec origin
      { n with ctl := .send (.ref k) .reflective "method_added" [.sym name] none [],
               kont := [.methodEditsK [] (.sym name)] } Γ .sym κ I := by
  let start : Machine :=
    { n with ctl := .send (.ref k) .reflective "method_added" [.sym name] none [],
             kont := [.methodEditsK [] (.sym name)] }
  obtain ⟨cp, hcp⟩ := Option.isSome_iff_exists.mp hc
  have hpay : (n.heap.get k).payload = .cls cp := by
    unfold Heap.classPayload? at hcp
    split at hcp <;> simp_all
  unfold definitionHookQuietB at hh
  cases hl : lookup n.heap (.ref k) "method_added" with
  | none => simp only [hl, Option.any] at hh; cases hh
  | some pair =>
    obtain ⟨owner, md⟩ := pair
    simp only [hl, Option.any, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hh
    obtain hs | ⟨msg, hs⟩ := invoke_native_method_added (m := start)
      (name := name) hpay hl hh.2 hh.1
    · apply RunSpec.step (show answerPoint start = none from rfl)
        (show Interp.stepFn start = .next (Interp.withCtl start (.value .nil)) from hs)
      apply RunSpec.step (show answerPoint (Interp.withCtl start (.value .nil)) = none from rfl)
        (show Interp.stepFn (Interp.withCtl start (.value .nil)) =
          .next (deliverA (.val (.sym name)) n []) from ?_)
      · exact RunSpec.answer ⟨hf, by simp [AnsOk, denM, isSymV], fun _ _ => hn⟩
      · rfl
    · exact RunSpec.unsupported (show answerPoint start = none from rfl) hs

/-- The new entry resolves when the defining class is first in the receiver's
ancestor chain. Prepends/eigenclasses must establish this, not be wished away. -/
theorem lookup_installed {m : Machine} {recv : Value} {name : String}
    {ps : List RubyCore.Param} {body : RubyCore.Expr} {rest : List ObjId}
    (hc : (m.heap.classPayload? m.currentFrame.defmod).isSome = true)
    (ha : ancestors m.heap (classOf m.heap recv) = m.currentFrame.defmod :: rest) :
    lookup (installMethod m name ps body).heap recv name =
      some (m.currentFrame.defmod, definedMethod m name ps body) := by
  unfold installMethod lookup
  dsimp only
  rw [Proof.classOf_defineMethod, Proof.ancestors_defineMethod, ha]
  apply Proof.lookup_go_defineMethod_self _ _ _ _ hc _
  unfold definedMethod Interp.normalizeDefinitionVisibility
  split <;> rfl

theorem finishSend_ordinary_userMethod {m : Machine} {o owner : ObjId}
    {name : String} {md : MethodDef} {args : List Value}
    (ho : (m.heap.get o).payload = .none)
    (hl : lookup m.heap (.ref o) name = some (owner, md))
    (hb : md.builtin = none) (hu : md.undefined = false) (hp : md.fromPrelude = false)
    (hs : Interp.crubyShadow m.heap
      ((ancestors m.heap (classOf m.heap (.ref o))).takeWhile (· != owner)) name = none) :
    Interp.finishSend m (.ref o) .implicit name args .none =
      Interp.enterUserMethod m (.ref o) name md args none :=
  invoke_ordinary_userMethod ho hl hb hu hp rfl hs

/-- Preserve the interpreter's fidelity gate when a native prefix shadows the
ordinary checked body. This outcome is safe without claiming body execution. -/
theorem finishSend_ordinary_shadow {m : Machine} {o owner : ObjId}
    {name cname : String} {md : MethodDef} {args : List Value}
    (ho : (m.heap.get o).payload = .none)
    (hl : lookup m.heap (.ref o) name = some (owner, md))
    (hb : md.builtin = none) (hu : md.undefined = false) (hp : md.fromPrelude = false)
    (hs : Interp.crubyShadow m.heap
      ((ancestors m.heap (classOf m.heap (.ref o))).takeWhile (· != owner)) name = some cname) :
    Interp.finishSend m (.ref o) .implicit name args .none =
      .unsupported s!"unmodeled builtin would shadow: {cname}#{name}" := by
  change Interp.invoke m (.ref o) .implicit name args none [] = _
  unfold Interp.invoke
  simp only [hl, Option.isNone, Bool.and_false, Bool.false_eq_true, ↓reduceIte, ho]
  simp only [Interp.invoke.invokeDispatch, hl, hu, hp, Bool.false_eq_true, ↓reduceIte,
    Interp.crubyResolvedShadow, hb, Option.any, hs]

/-- Installation supplies the lookup and both shadow checks. The ordinary receiver
is distinct from its defining class; its payload survives the class-table write. -/
theorem finishSend_installed {m : Machine} {o : ObjId} {name : String}
    {ps : List RubyCore.Param} {body : RubyCore.Expr} {rest : List ObjId}
    {args : List Value}
    (ho : (m.heap.get o).payload = .none) (hne : o ≠ m.currentFrame.defmod)
    (hc : (m.heap.classPayload? m.currentFrame.defmod).isSome = true)
    (ha : ancestors m.heap (classOf m.heap (.ref o)) = m.currentFrame.defmod :: rest)
    (hp : m.preludeMode = false) (hlib : m.currentFrame.libraryOrigin = false) :
    Interp.finishSend (installMethod m name ps body) (.ref o) .implicit name args .none =
      Interp.enterUserMethod (installMethod m name ps body) (.ref o) name
        (definedMethod m name ps body) args none := by
  apply finishSend_ordinary_userMethod (md := definedMethod m name ps body)
    (owner := m.currentFrame.defmod)
  · change ((defineMethod m.heap m.currentFrame.defmod name _).get o).payload = .none
    rw [heap_get_defineMethod_ne hne, ho]
  · exact lookup_installed hc ha
  · unfold definedMethod Interp.normalizeDefinitionVisibility; split <;> rfl
  · unfold definedMethod Interp.normalizeDefinitionVisibility; split <;> rfl
  · unfold definedMethod Interp.normalizeDefinitionVisibility
    split <;> simp [sourceMethod, hp, hlib]
  · change Interp.crubyShadow (defineMethod m.heap m.currentFrame.defmod name _)
      ((ancestors (defineMethod m.heap m.currentFrame.defmod name _)
        (classOf (defineMethod m.heap m.currentFrame.defmod name _) (.ref o))).takeWhile
          (· != m.currentFrame.defmod)) name = none
    rw [Proof.classOf_defineMethod, Proof.ancestors_defineMethod, ha]
    simp [Interp.crubyShadow]
    rfl

/-- Call safety after ordinary dispatch, from the annotated body proof. Lookup may
come from `lookup_installed`; transporting conformance across installation is still
separate. No signature-only or concrete-argument body shortcut is admitted here. -/
theorem required_method_call_runSpec {κ : Ctx} {Γ Γb : Env} {I τ : Ty} {m : Machine}
    {md : MethodDef} {name : String} {ps : List SigParam} {args : List Value}
    {e : Ratchet.Expr} {fr : Option Ratchet.Frame} {o owner : ObjId}
    (hm : StateOk κ Γ I m) (ht : ReframeFO κ I) (ha : κ.asms = [])
    (hkont : m.kont = []) (hp : md.params = (ps.map (·.1)).map RubyCore.Param.req)
    (hcap : md.capturedFrame = none) (hdecl : md.declared = []) (hbody : md.body = toRuby e)
    (hblock : md.fromBlock = false) (hfor : md.forTargets = none)
    (hlen : args.length = ps.length) (hargs : DenAll (ps.map (·.2)) m args)
    (hps : ∀ p ∈ ps, FirstOrder p.2 = true ∧ isAliasTy p.2 = false)
    (hτ : FirstOrder τ = true) (hΓ : ∀ p ∈ Γ, FirstOrder (stripAlias p.2) = true)
    (hscope : frameScope (requiredFrame m.currentFrame.self name md (ps.map (·.1)) args) =
      frameScope m.currentFrame)
    (hk : ∀ x, constGet? (κ.withFrame fr) x = constGet? κ x)
    (hframe : FrameOk fr
      (pushMethodFrame m (requiredFrame m.currentFrame.self name md (ps.map (·.1)) args)))
    (hb : SemSafeCtxA (κ.withFrame fr) ps I e τ (κ.withFrame fr) Γb I)
    (hself : m.currentFrame.self = .ref o) (ho : (m.heap.get o).payload = .none)
    (hl : lookup m.heap (.ref o) name = some (owner, md))
    (hbi : md.builtin = none) (hu : md.undefined = false) (hpre : md.fromPrelude = false)
    (hs : Interp.crubyShadow m.heap
      ((ancestors m.heap (classOf m.heap (.ref o))).takeWhile (· != owner)) name = none) :
    ∃ next, Interp.finishSend m m.currentFrame.self .implicit name args .none = .next next ∧
      RunSpec m next Γ τ κ I := by
  obtain ⟨next, he, hr⟩ := required_method_runSpec hm ht ha hkont hp hcap hdecl hbody
    hblock hfor hlen hargs hps hτ hΓ hscope hk hframe hb
  refine ⟨next, ?_, hr⟩
  rw [hself] at he ⊢
  rw [finishSend_ordinary_userMethod ho hl hbi hu hpre hs]
  exact he

#print axioms step_def_install
#print axioms definition_hook_runSpec
#print axioms lookup_installed
#print axioms finishSend_ordinary_userMethod
#print axioms finishSend_ordinary_shadow
#print axioms finishSend_installed
#print axioms required_method_call_runSpec
end Ratchet.Denote.Typed
