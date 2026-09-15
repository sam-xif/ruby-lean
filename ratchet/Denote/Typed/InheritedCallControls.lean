import Denote.Typed.InstanceResolvedRun
import Denote.Typed.ClassHeaderControls
import Denote.Typed.ConstructorLookup
import Denote.Typed.MethodChecked
import Denote.Sem.ClassFreshness
import Denote.Sem.ClassGuards
import Denote.Sem.MemberDeclared

/-! Independent receiver/owner annotations and the missing inherited-lookup premise.
The full-state omission witness does not expose an accepted unsafe program: present calls
require an own positive row. Inherited calls will also need proof of no earlier override. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed.InheritedCallControls
open RubyCore Ratchet Ratchet.Denote

private def labelFields : Ty := .ivarCons "@label" (.cls "String") .ivar0
private def echo : Defn := ⟨"echo", [.req "flag"], .var .lvar "flag"⟩
private def echoCtx (κ : Ctx) : Ctx := instanceBodyCtx κ ⟨"Satellite", "Depot", "echo"⟩ labelFields
private def echoParams : Env := [("flag", .bool)]

-- Full annotation-domain checking still precedes a call, including unused bodies.
#guard (checkMethodBody 30 (echoCtx ctx0) labelFields echo
  (.defDecl "echo" echoParams .bool (.var .lvar "flag"))).isSome
#guard (checkMethodBody 30 (echoCtx ctx0) labelFields echo
  (.defDecl "echo" [("flag", .nilable .bool)] .bool (.var .lvar "flag"))).isNone
#guard (checkMethodBody 30 (echoCtx ctx0) labelFields echo
  (.defDecl "echo" echoParams .int (.var .lvar "flag"))).isNone

/-- Every Boolean argument uses the same full body proof, with Satellite self and Depot
scope. Actual lookup/native-prefix evidence is deliberately required, not guessed. -/
theorem inherited_echo_run {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine} {r k : ObjId}
    {md : MethodDef} {recv : Value} (hm : StateOk κ Γ I m) (ht : ReframeFO κ I)
    (ha : κ.asms = []) (hw : CallWorld κ) (hkont : m.kont = [])
    (rs : InstanceSite κ "Satellite" r m.heap) (os : InstanceSite κ "Depot" k m.heap)
    (code : InstanceMethodCode k "echo" md) (hu : md.undefined = false)
    (hp : md.params = [.req "flag"]) (hb : md.body = .var .lvar "flag")
    (hl : lookup m.heap recv "echo" = some (k, md))
    (hv : denM (.inst "Satellite" labelFields) m recv)
    (hk : ∀ x, constGet? (echoCtx κ) x = constGet? κ x)
    (hΓ : ∀ p ∈ Γ, FirstOrder (stripAlias p.2) = true)
    (hshadow : Interp.crubyShadow m.heap
      ((ancestors m.heap (classOf m.heap recv)).takeWhile (· != k)) "echo" = none) (b : Bool) :
    ∃ n, Interp.finishSend m recv .explicit "echo" [.bool b] .none = .next n ∧
      RunSpec m n Γ .bool κ I :=
  resolved_instance_run (fr := ⟨"Satellite", "Depot", "echo"⟩) (e := echo.body)
    (ps := echoParams) (Γb := echoParams)
    hp hb (by simp [echoParams, FirstOrder, isAliasTy]) rfl (SemSafeCtxA.var rfl rfl)
    hm ht ha rs os hw hkont code hu hl rfl hv rfl (by simp [echoParams, DenAll, denM, isBoolV]) hk hΓ
    (fun _ _ => Or.inr (directSendNameB_sound (by decide))) (by decide) hshadow

private def setup : Ratchet.Expr := .seq [
  .class' "Depot" none (.seq [
    .def' "initialize" [.req "label"] (.vasgn .ivar "@label" (.var .lvar "label")),
    .def' echo.name echo.params echo.body]),
  .class' "Satellite" (some (.const "Depot")) .nil,
  .send (some (.const "Satellite")) "new" [.str "Rex"] none]

-- Real inherited definition/new/lookup/entry/call. The old exact-owner self type is false.
#guard match Interp.run 200 (evalFrom bootMachine setup) with
  | .value (.ref o) m => match lookup m.heap (.ref o) "echo", classNamed? m.heap "Depot" with
    | some (k, md), some parent => k == parent && instanceMethodCodeB k "echo" md &&
      match Interp.enterUserMethod m (.ref o) "echo" md [.bool true] none with
      | .next n => n.currentFrame.defmod == k && n.currentFrame.cref == [k, Boot.objectId] &&
        isExactInst n.heap n.currentFrame.self "Satellite" &&
        !isExactInst n.heap n.currentFrame.self "Depot" &&
        (match Interp.run 30 n with | .value (.bool true) _ => true | _ => false)
      | _ => false
    | _, _ => false
  | _ => false

/-- Full current conformance permits a method omitted at its heap owner whenever its name
is already globally reserved. This is why positive ancestor rows do not prove lookup. -/
theorem unrecorded_shadow_preserves_state {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine}
    {cls : ObjId} {name : String} {md : MethodDef}
    (hm : StateOk κ Γ I m) (ht : ReframeFO κ I)
    (hΓ : ∀ p ∈ Γ, FirstOrder (stripAlias p.2) = true) (ha : κ.asms = [])
    (hn : nameFreeN κ name = false) (hnew : "new" ≠ name)
    (hmiss : "method_missing" ≠ name) (hquiet : "method_added" ≠ name)
    (hc : cls ≠ Boot.objectId)
    (hrows : ∀ c ∈ κ.classes, classNamed? m.heap c.name = some cls →
      ∀ d ∈ c.methods, d.name ≠ name) :
    StateOk κ Γ I { m with heap := defineMethod m.heap cls name md } :=
  StateOk_methodWrite hm ht hΓ ha hn hmiss hquiet (ClassesOk_methodWrite_old hm.classes hrows)
    (DefsOk_methodWrite_other hm.defs hc) (hm.declCls.methodWrite hnew hmiss)

private def sourceDecl : Defn := ⟨"answer", [], .int 1⟩
private def sourceCtx : Ctx := topDeclCtx ctx0 sourceDecl
private def sourceMachine : Machine := installMethod bootMachine "answer" [] (.int 1)
private def childCtx : Ctx := classHeaderCtx (classBodyCtx sourceCtx "Child") "Child"
private def badMethod (k : ObjId) : MethodDef :=
  { owner := k, params := [], body := .fls, cref := [k, Boot.objectId] }

private theorem source_state (hb : bootOkB = true) : StateOk sourceCtx [] .ivar0 sourceMachine := by
  have hm := stateOk_boot hb
  have ready := hm.runtime rfl
  have h := StateOk_defineTopMethod (d := sourceDecl)
    (md := definedMethod bootMachine "answer" [] (.int 1))
    (StateOk_reserveName hm "answer") (ReframeFO.empty rfl rfl rfl rfl)
    (by simp) rfl rfl (by decide) (by decide) (by decide) ready.classLive
    (by simp [ctx0, Ctx.defs]) rfl rfl rfl
    (definedMethod_code ready.owner ready.cref ready.phase)
  simpa only [sourceMachine, installMethod, ready.owner, sourceCtx, sourceDecl,
    topDeclCtx, reserveNameCtx] using h

example : SemSafeCtxA (topBodyCtx ctx0 sourceDecl) [] .ivar0 sourceDecl.body .int
    (topBodyCtx ctx0 sourceDecl) [] .ivar0 := SemSafeCtxA.intLit

/-- A boot-grounded full-StateOk witness: Child's declared own table is empty, but its
actual answer overrides the retained Object#answer annotation with a Boolean body. -/
theorem full_state_unrecorded_shadow (hb : bootOkB = true) :
    ∃ n k, StateOk childCtx [] .ivar0 n ∧ classNamed? n.heap "Child" = some k ∧
      Interp.methodOn n.heap k "answer" = some (k, badMethod k) := by
  have hm := source_state hb
  obtain ⟨m, _, hm⟩ := class_entry_header (name := "Child") (body := .nil) hm
    rfl rfl rfl rfl (ClassTablesFrame.empty rfl rfl) (by decide)
    (hm.freshClassName (by decide)) (by decide) (by decide)
    (by constructor <;> decide) (by decide) (by decide)
  obtain ⟨k, site⟩ := hm.classSites.of_class
    (show classHeader "Child" ∈ childCtx.classes from by change _ ∈ [_]; simp)
  have hc : k ≠ Boot.objectId := declared_not_object hm site.named (by decide)
  have hn := unrecorded_shadow_preserves_state (name := "answer") (md := badMethod k) hm
    (reframeTypesB_sound (by decide)) (by simp) rfl (by decide)
    (by decide) (by decide) (by decide) hc (by
      intro c hc _ d hd
      have he : c = classHeader "Child" := by simpa [childCtx, classHeaderCtx, Ctx.classes,
        classBodyCtx, sourceCtx, topDeclCtx, ctx0] using hc
      subst c
      cases hd)
  refine ⟨_, k, hn, ?_, ?_⟩
  · rw [classNamed?_defineMethod]; exact site.named
  · obtain ⟨rest, hr⟩ := classFrontB_sound site.front
    exact methodOn_own_first (by rw [Proof.ancestors_defineMethod]; exact hr)
      (ownMethod_defineMethod_self m.heap k "answer" (badMethod k) (namedClass_payload site.named))

#guard (classHeader "Child").methods.isEmpty
#guard !nameFreeN childCtx "answer"

-- The same omission matters on a real non-root inheritance chain: keep the ancestor's
-- row and the chain, insert an unrecorded child override, and the annotated use fails.
private def inheritance : Ratchet.Expr := .seq [
  .class' "Parent" none (.def' "answer" [] (.int 1)),
  .class' "Child" (some (.const "Parent")) .nil]
private def useAnswer : Ratchet.Expr := .send (some (.send
  (some (.send (some (.const "Child")) "new" [] none)) "answer" [] none)) "+" [.int 1] none
private def parentRow (m : Machine) (parent : ObjId) : Bool :=
  (Interp.methodOn m.heap parent "answer").any fun (k, md) => k == parent &&
    instanceMethodCodeB parent "answer" md && md.params.isEmpty &&
    (match md.body with | .int 1 => true | _ => false)

#guard match Interp.run 100 (evalFrom bootMachine inheritance) with
  | .value _ m => match classNamed? m.heap "Child", classNamed? m.heap "Parent" with
    | some child, some parent =>
      let n := { m with heap := defineMethod m.heap child "answer" (badMethod child) }
      (Interp.methodOn m.heap child "answer").any (fun (k, _) => k == parent) &&
      parentRow m parent && parentRow n parent &&
      ancestors m.heap child == ancestors n.heap child &&
      (Interp.methodOn n.heap child "answer").any (fun (k, _) => k == child) &&
      (match Interp.run 100 (evalFrom m useAnswer) with | .value (.int 2) _ => true | _ => false) &&
      Semantics.typeStuck (Interp.run 100 (evalFrom n useAnswer))
    | _, _ => false
  | _ => false

#print axioms inherited_echo_run
#print axioms full_state_unrecorded_shadow
end Ratchet.Denote.Typed.InheritedCallControls
