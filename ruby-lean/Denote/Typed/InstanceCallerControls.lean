import Denote.Typed.InstanceImplicit
import Denote.Typed.InstanceRead
import Denote.Typed.Sequence
import Denote.Sem.ClassGuards
import Denote.Sanity

/-! Different caller/callee classes and field types, plus all ordinary receiver sites.
Each call consumes a complete annotation-domain body proof; none assumes its result. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed.InstanceCallerControls
open RubyCore Ratchet Ratchet.Denote

private def fields : Ty := .ivarCons "@value" .bool .ivar0
private def callerFields : Ty := .ivarCons "@tag" .int .ivar0
private def getter : Defn := ⟨"get", [], .var .ivar "@value"⟩
private def beta : Cls := classWithMethod (classHeader "Beta") getter
private def base : Ctx :=
  instanceDeclCtx (classHeaderCtx (classHeaderCtx ctx0 "Alpha") "Beta")
    (classHeader "Beta") getter
private def caller : Ctx := instanceBodyCtx base ⟨"Alpha", "Alpha", "relay"⟩ callerFields
private def localEnv : Env := [("other", .inst "Beta" fields)]
private def selfCaller : Ctx := instanceBodyCtx base ⟨"Beta", "Beta", "relay"⟩ fields
private def otherGet : Ratchet.Expr := .send (some (.var .lvar "other")) "get" [] none

-- The whole getter is proved for every context and caller; no concrete argument appears.
private theorem getter_body {κ : Ctx} :
    SemSafeCtxA (instanceBodyCtx κ ⟨"Beta", "Beta", "get"⟩ fields) [] fields getter.body .bool
      (instanceBodyCtx κ ⟨"Beta", "Beta", "get"⟩ fields) [] fields := SemSafeCtxA.ivarRead

private theorem beta_mem {κ : Ctx} (h : κ.classes = base.classes) : beta ∈ κ.classes := by
  rw [h]; change beta ∈ beta :: _; simp
private theorem getter_mem : getter ∈ beta.methods := by change getter ∈ [getter]; simp
private theorem consts {κ : Ctx} (h : κ.consts = []) (x : String) :
    constGet? (instanceBodyCtx κ ⟨"Beta", "Beta", "get"⟩ fields) x = constGet? κ x := by
  rw [constGet?_empty h]
  exact constGet?_empty (κ := instanceBodyCtx κ ⟨"Beta", "Beta", "get"⟩ fields) h x

theorem cross_class_call :
    SemSafeCtxA caller localEnv callerFields otherGet .bool caller localEnv callerFields :=
  (SemSafeCtxA.var (κ := caller) (Γ := localEnv) (I := callerFields) (x := "other") rfl rfl).instanceCall_at
    (ps := []) .nil rfl (beta_mem (κ := caller) rfl) getter_mem
    (by decide) (directSendNameB_sound (by decide)) rfl (by simp) rfl rfl getter_body
    (reframeTypesB_sound (by decide)) rfl (callWorldB_sound (by decide)) (consts rfl)
    (by simp [localEnv, fields, FirstOrder, stripAlias])

-- Observe the caller's differently typed field after returning from the Boolean getter.
theorem cross_class_then_read : SemSafeCtxA caller localEnv callerFields
    (.seq [otherGet, .var .ivar "@tag"]) .int caller localEnv callerFields :=
  cross_class_call.seq SemSafeCtxA.ivarRead

theorem self_vcall : SemSafeCtxA selfCaller [] fields (.vcall "get") .bool selfCaller [] fields :=
  SemSafeCtxA.instanceVcall (κ := selfCaller) (Γ := []) (I := fields)
    rfl (beta_mem (κ := selfCaller) rfl) getter_mem (by decide)
    (directSendNameB_sound (by decide)) rfl rfl rfl getter_body
    (reframeTypesB_sound (by decide)) rfl (callWorldB_sound (by decide)) (consts rfl) (by simp)

theorem self_implicit : SemSafeCtxA selfCaller [] fields
    (.send none "get" [] none) .bool selfCaller [] fields :=
  SemSafeCtxA.instanceImplicit (κ := selfCaller) (Γ := []) (I := fields) (ps := [])
    rfl .nil (beta_mem (κ := selfCaller) rfl) getter_mem (by decide)
    (directSendNameB_sound (by decide)) rfl (by simp) rfl rfl getter_body
    (reframeTypesB_sound (by decide)) rfl (callWorldB_sound (by decide)) (consts rfl) (by simp)

theorem self_explicit : SemSafeCtxA selfCaller [] fields
    (.send (some .self') "get" [] none) .bool selfCaller [] fields :=
  (SemSafeCtxA.selfRead (κ := selfCaller) (Γ := []) (I := fields) rfl).instanceCall_at (ps := [])
    .nil rfl (beta_mem (κ := selfCaller) rfl) getter_mem
    (by decide) (directSendNameB_sound (by decide)) rfl (by simp) rfl rfl getter_body
    (reframeTypesB_sound (by decide)) rfl (callWorldB_sound (by decide)) (consts rfl) (by simp)

#guard callWorldB caller && callWorldB selfCaller && callWorldB ctx0
-- Lexical owner and receiver names need not coincide, but both need retained sites.
#guard callWorldB (instanceBodyCtx base ⟨"Beta", "Alpha", "relay"⟩ fields)
#guard !callWorldB (instanceBodyCtx base ⟨"Missing", "Alpha", "relay"⟩ fields)
#guard !callWorldB (instanceBodyCtx base ⟨"Beta", "Missing", "relay"⟩ fields)
#guard !callWorldB (classBodyCtx base "Beta")
#guard !callWorldB { caller with scope := { caller.scope with selfTy := none } }
#guard !callWorldB { ctx0 with pos := { ctx0.pos with mainWorld := false } }

private def program (read : Ratchet.Expr) : Ratchet.Expr := .seq [
  .class' "Beta" none (.seq [
    .def' "initialize" [.req "flag"] (.vasgn .ivar "@value" (.var .lvar "flag")),
    .def' getter.name getter.params getter.body, .def' "relay" [] read]),
  .class' "Alpha" none (.seq [
    .def' "initialize" [.req "tag"] (.vasgn .ivar "@tag" (.var .lvar "tag")),
    .def' "relay" [.req "other"] (.seq [otherGet, .var .ivar "@tag"])]),
  .vasgn .lvar "b" (.send (some (.const "Beta")) "new" [.tru] none),
  .send (some (.var .lvar "b")) "relay" [] none,
  .send (some (.send (some (.const "Alpha")) "new" [.int 42] none)) "relay"
    [.var .lvar "b"] none]

#guard [.vcall "get", .send none "get" [] none, .send (some .self') "get" [] none].all fun read =>
  match Interp.run 300 (evalFrom bootMachine (program read)) with
  | .value (.int 42) _ => true
  | _ => false

#print axioms cross_class_then_read
#print axioms self_vcall
#print axioms self_implicit
#print axioms self_explicit
end Ratchet.Denote.Typed.InstanceCallerControls
