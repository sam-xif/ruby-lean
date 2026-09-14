import Denote.Typed.MethodState
import Denote.Sem.MethodHeap

/-! The ordinary method's installation and dispatch paths. These are interpreter
equalities, not annotation-based admission: safety still consumes the checked body.
-/

set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

/-- Exactly the method record constructed by the `def` step. -/
def definedMethod (m : Machine) (name : String) (ps : List RubyCore.Param)
    (body : RubyCore.Expr) : MethodDef :=
  { params := ps, body, owner := m.currentFrame.defmod, cref := m.currentFrame.cref,
    fromPrelude := m.preludeMode,
    visibility := if name == "initialize" then .priv
      else if m.currentFrame.kind == .toplevel then .priv else m.currentFrame.defVis }

def installMethod (m : Machine) (name : String) (ps : List RubyCore.Param)
    (body : RubyCore.Expr) : Machine :=
  let md := definedMethod m name ps body
  { m with heap := defineMethod m.heap m.currentFrame.defmod name md }

theorem definedMethod_code {m : Machine} {name : String} {ps : List RubyCore.Param}
    {body : RubyCore.Expr} (ho : m.currentFrame.defmod = Boot.objectId)
    (hc : m.currentFrame.cref = [Boot.objectId]) (hp : m.preludeMode = false) :
    TopMethodCode (definedMethod m name ps body) := ⟨ho, hc, rfl, rfl, rfl, rfl, hp⟩

/-- A missing or CRuby-shadowed `method_added` does not run user code. A genuine
hook is deliberately not covered by this definition-only transition. -/
def DefHookQuiet (m : Machine) : Prop :=
  match lookup m.heap (.ref m.currentFrame.defmod) "method_added" with
  | none => True
  | some (owner, md) =>
    (md.undefined || owner == Boot.objectId || owner == Boot.kernelId ||
      owner == Boot.basicObjectId) = true

def defHookQuietB (m : Machine) : Bool :=
  match lookup m.heap (.ref m.currentFrame.defmod) "method_added" with
  | none => true
  | some (owner, md) => md.undefined || owner == Boot.objectId ||
      owner == Boot.kernelId || owner == Boot.basicObjectId

theorem defHookQuietB_sound {m : Machine} (h : defHookQuietB m = true) : DefHookQuiet m := by
  unfold defHookQuietB at h
  unfold DefHookQuiet
  cases he : lookup m.heap (.ref m.currentFrame.defmod) "method_added" with
  | none => trivial
  | some pair => cases pair; simpa only [he] using h

theorem mainReady_defHookQuiet {m : Machine} (h : MainReady m) : DefHookQuiet m :=
  defHookQuietB_sound (by
    unfold defHookQuietB
    rw [h.owner]
    have hh := h.hook
    unfold objectHookQuietB at hh
    cases hl : lookup m.heap (.ref Boot.objectId) "method_added" with
    | none => rfl
    | some p => cases p; simpa only [hl] using hh)

theorem defHookQuiet_install {m : Machine} {name : String} {ps : List RubyCore.Param}
    {body : RubyCore.Expr} (hn : "method_added" ≠ name) (hh : DefHookQuiet m) :
    DefHookQuiet (installMethod m name ps body) := by
  unfold DefHookQuiet installMethod
  dsimp only
  rw [Proof.lookup_defineMethod _ _ _ _ _ _ hn (Proof.classOf_defineMethod ..)]
  exact hh

theorem step_def_install {m : Machine} {name : String} {ps : List RubyCore.Param}
    {body : RubyCore.Expr} (hc : m.ctl = .eval (.def' name ps body))
    (hh : DefHookQuiet (installMethod m name ps body)) :
    Interp.stepFn m = .next (Interp.withCtl (installMethod m name ps body)
      (.value (.sym name))) := by
  simp only [Interp.stepFn, hc]
  change (if m.preludeMode then _ else _) = _
  split
  · rfl
  · unfold DefHookQuiet at hh
    have hcf : (installMethod m name ps body).currentFrame = m.currentFrame := rfl
    rw [hcf] at hh
    cases hl : lookup (installMethod m name ps body).heap
        (.ref m.currentFrame.defmod) "method_added" with
    | none =>
      simp only [installMethod, definedMethod] at hl
      simp only [hl]
      rfl
    | some pair =>
      obtain ⟨owner, md⟩ := pair
      simp only [installMethod, definedMethod] at hl hh ⊢
      rw [hl] at hh
      simp only [hl, hh, ↓reduceIte]

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
  exact Proof.lookup_go_defineMethod_self _ _ _ _ hc _

theorem invokeDispatch_userMethod {m : Machine} {recv : Value} {site : SendSite}
    {name : String} {md : MethodDef} {owner : ObjId} {args : List Value}
    {blk : Option Value} {kw : List (Value × Value)}
    (hl : lookup m.heap recv name = some (owner, md))
    (hb : md.builtin = none) (hu : md.undefined = false) (hp : md.fromPrelude = false)
    (hv : Interp.visError? m recv site md name = none)
    (hs : Interp.crubyShadow m.heap
      ((ancestors m.heap (classOf m.heap recv)).takeWhile (· != owner)) name = none)
    (hss : Interp.crubySingletonShadow m.heap recv name = none) :
    Interp.invoke.invokeDispatch m recv site name args blk kw =
      Interp.enterUserMethod m recv name md args blk kw := by
  simp only [Interp.invoke.invokeDispatch, hl, hu, hp, Bool.false_eq_true, ↓reduceIte,
    hs, hv, hb, hss]

/-- Ordinary objects have no Proc/Hash/Class interception. A found entry also
shadows the reflective `send` family, so no method-name blacklist is necessary. -/
theorem invoke_ordinary_userMethod {m : Machine} {o owner : ObjId} {site : SendSite}
    {name : String} {md : MethodDef} {args : List Value} {blk : Option Value}
    {kw : List (Value × Value)}
    (ho : (m.heap.get o).payload = .none)
    (hl : lookup m.heap (.ref o) name = some (owner, md))
    (hb : md.builtin = none) (hu : md.undefined = false) (hp : md.fromPrelude = false)
    (hv : Interp.visError? m (.ref o) site md name = none)
    (hs : Interp.crubyShadow m.heap
      ((ancestors m.heap (classOf m.heap (.ref o))).takeWhile (· != owner)) name = none) :
    Interp.invoke m (.ref o) site name args blk kw =
      Interp.enterUserMethod m (.ref o) name md args blk kw := by
  unfold Interp.invoke
  simp only [hl, Option.isNone, Bool.and_false, Bool.false_eq_true, ↓reduceIte, ho]
  exact invokeDispatch_userMethod hl hb hu hp hv hs
    (by simp [Interp.crubySingletonShadow, ho])

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

/-- Installation supplies the lookup and both shadow checks. The ordinary receiver
is distinct from its defining class; its payload survives the class-table write. -/
theorem finishSend_installed {m : Machine} {o : ObjId} {name : String}
    {ps : List RubyCore.Param} {body : RubyCore.Expr} {rest : List ObjId}
    {args : List Value}
    (ho : (m.heap.get o).payload = .none) (hne : o ≠ m.currentFrame.defmod)
    (hc : (m.heap.classPayload? m.currentFrame.defmod).isSome = true)
    (ha : ancestors m.heap (classOf m.heap (.ref o)) = m.currentFrame.defmod :: rest)
    (hp : m.preludeMode = false) :
    Interp.finishSend (installMethod m name ps body) (.ref o) .implicit name args .none =
      Interp.enterUserMethod (installMethod m name ps body) (.ref o) name
        (definedMethod m name ps body) args none := by
  apply finishSend_ordinary_userMethod (md := definedMethod m name ps body)
    (owner := m.currentFrame.defmod)
  · change ((defineMethod m.heap m.currentFrame.defmod name _).get o).payload = .none
    rw [heap_get_defineMethod_ne hne, ho]
  · exact lookup_installed hc ha
  · rfl
  · rfl
  · exact hp
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
    hlen hargs hps hτ hΓ hscope hk hframe hb
  refine ⟨next, ?_, hr⟩
  rw [hself] at he ⊢
  rw [finishSend_ordinary_userMethod ho hl hbi hu hpre hs]
  exact he

#print axioms step_def_install
#print axioms lookup_installed
#print axioms finishSend_ordinary_userMethod
#print axioms finishSend_installed
#print axioms required_method_call_runSpec
end Ratchet.Denote.Typed
