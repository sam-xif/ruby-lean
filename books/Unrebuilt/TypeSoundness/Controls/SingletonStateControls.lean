import Books.TypeSoundness.Rules.Singleton.SingletonState
import Books.TypeSoundness.Rules.Instance.MemberInstall
import Books.TypeSoundness.Controls.ClassHeaderControls
import Books.TypeSoundness.Conformance.Class.ClassGuards
import Books.TypeSoundness.Rules.Singleton.SingletonRun
import Books.TypeSoundness.Rules.Method.MethodChecked

/-! Full boot-grounded publication followed by an ordinary write with the same selector. -/
set_option autoImplicit false
namespace Checker.Soundness.Typed.SingletonStateControls
open RubyCore Checker Checker.Soundness

private def copyDef : Defn := ⟨"copy", [.req "value"], .var .lvar "value"⟩
private def body : Checker.Expr := .defs .self' copyDef.name copyDef.params copyDef.body
private def before : Ctx := classHeaderCtx (classBodyCtx ctx0 "Point") "Point"
private def after : Ctx := singletonDeclCtx before (classHeader "Point") copyDef
private def instanceDef : Defn := ⟨"copy", [], .tru⟩
private def c : Cls := classWithSingleton (classHeader "Point") copyDef
private def copyCtx : Ctx := singletonBodyCtx after "Point" "copy"
private def cert : Deriv := .defDecl "copy" [("value", .int)] .int (.var .lvar "value")
private def checked : CheckedBody copyCtx .ivar0 copyDef :=
  (checkMethodBody 100 copyCtx .ivar0 copyDef cert).get (by decide)

theorem boot_state (hb : bootOkB = true)
    (hn : constOwn bootMachine.heap Boot.objectId "Point" = none) :
    ∃ m n, Interp.stepFn (evalFrom bootMachine (.class' "Point" none body)) = .next m ∧
      Interp.stepFn m = .next n ∧ StateOk after [] .ivar0 n := by
  obtain ⟨m, step, hm⟩ := boot_point_header hb hn body
  obtain ⟨ep, he, hs⟩ := stepFn_class_fresh (body := body) (stateOk_boot hb) rfl hn (by decide)
  have hctl : m.ctl = .eval (toRuby body) := by rw [hs] at step; cases step; rfl
  obtain ⟨n, hn, hs⟩ := step_singleton_state (d := copyDef) (c := classHeader "Point") hm
    (by change _ ∈ [_]; simp) rfl rfl (reframeTypesB_sound (by decide)) (by simp) rfl
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hctl
  exact ⟨m, n, step, hn, hs⟩

theorem same_selector_state {m : Machine} (hm : StateOk after [] .ivar0 m) :
    StateOk (instanceDeclCtx after c instanceDef) [] .ivar0
      (installMethod m "copy" [] .tru) := by
  exact StateOk_install_member hm rfl (by change c ∈ [c, _]; simp)
    (reframeTypesB_sound (by decide)) (by simp) rfl (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

theorem retained_singleton {m : Machine} (hm : StateOk after [] .ivar0 m) :
    ∃ k e md, classNamed? m.heap "Point" = some k ∧
      lookup (installMethod m "copy" [] .tru).heap (.ref k) "copy" = some (e, md) ∧
      md.params = [.req "value"] ∧ md.body = .var .lvar "value" ∧
      md.undefined = false ∧ SingletonMethodCode k e md := by
  have hn := same_selector_state hm
  obtain ⟨k, e, md, hk, rest⟩ := classesOk_singleton_lookup (c := c) (d := copyDef)
    hn.classes hn.classSites (by change c ∈ [_, c, _]; simp) (by change _ ∈ [_]; simp)
  exact ⟨k, e, md, by simpa only [installMethod, classNamed?_defineMethod, c,
    classWithSingleton, classHeader] using hk, rest⟩

/-- The boot_state theorem above supplies this full incoming state. One checked body
covers every Integer argument at actual singleton entry. -/
theorem annotated_singleton_body {m : Machine} (hm : StateOk after [] .ivar0 m) (v : Int) :
    ∃ k md n, classNamed? m.heap "Point" = some k ∧
      Interp.enterUserMethod m (.ref k) "copy" md [.int v] none = .next n ∧
      n.ctl = .eval (toRuby copyDef.body) ∧ StateOk copyCtx [("value", .int)] .ivar0 n ∧
      RunSpec n (evalFrom n copyDef.body) [("value", .int)] .int copyCtx .ivar0 := by
  have hc : c ∈ after.classes := by change c ∈ [c, _]; simp
  obtain ⟨k, hk, _, rows⟩ := hm.classes c hc
  obtain ⟨e, md, he, _, _, hparams, hbody, _, code⟩ := rows copyDef (by change _ ∈ [_]; simp)
  obtain ⟨_, scope⟩ := hm.classRuntime "Point" rfl
  obtain ⟨n, hn, hnctl, hs⟩ := singleton_enterUserMethod_state
    (name := "copy") (ps := [("value", .int)]) (args := [.int v]) hm (reframeTypesB_sound (by decide)) rfl
    (hm.classSites.at_class hc hk) he code scope.phase rfl
    (by simp [DenAll, denM, isIntV]) (by simp [FirstOrder, isAliasTy])
    (fun x => (constGet?_empty (κ := copyCtx) rfl x).trans (constGet?_empty rfl x).symm) hparams
  exact ⟨k, md, n, hk, hn, hnctl.trans (congrArg Ctl.eval hbody), hs,
    checked_body_context checked n hs⟩

/-- The previous control establishes this caller at real entry. A second singleton call
executes the checked body and restores the caller's scope and typed local environment. -/
theorem nested_copy_call {m : Machine} (hm : StateOk copyCtx [("value", .int)] .ivar0 m)
    (hkont : m.kont = []) (v : Int) :
    ∃ k next, classNamed? m.heap "Point" = some k ∧
      Interp.finishSend m (.ref k) .explicit "copy" [.int v] .none = .next next ∧
      RunSpec m next [("value", .int)] .int copyCtx .ivar0 := by
  have hc : c ∈ copyCtx.classes := by change c ∈ [c, _]; simp
  obtain ⟨k, hk, _, rows⟩ := hm.classes c hc
  obtain ⟨e, md, he, _, row, hparams, hbody, hu, code⟩ := rows copyDef (by change _ ∈ [_]; simp)
  have site := hm.classSites.at_class hc hk
  obtain ⟨tail, ha⟩ := classFrontB_sound (site.eigen_front he)
  have hl : lookup m.heap (.ref k) copyDef.name = some (e, md) :=
    lookup_own_first (by simpa only [classOf, he] using ha) row
  obtain ⟨next, hnext, hr⟩ := resolved_singleton_run (κ := copyCtx) (cn := "Point")
    (name := "copy") (site := .explicit)
    (ps := [("value", .int)]) (args := [.int v]) hparams hbody (by simp [FirstOrder, isAliasTy]) rfl
    (checked_body_context checked) hm (reframeTypesB_sound (by decide)) rfl site he
    (callWorldB_sound (by decide)) hkont code hu hl rfl
    (by simp [DenAll, denM, isIntV]) (fun _ => rfl) (by simp [FirstOrder, stripAlias])
    (directSendNameB_sound (by decide))
  exact ⟨k, next, hk, hnext, hr⟩

#guard (checkMethodBody 100 copyCtx .ivar0 copyDef cert).isSome
#guard (checkMethodBody 100 copyCtx .ivar0 copyDef
  (.defDecl "copy" [("value", .bool)] .int (.var .lvar "value"))).isNone
#guard (checkMethodBody 100 copyCtx .ivar0 copyDef
  (.defDecl "copy" [("value", .int)] .bool (.var .lvar "value"))).isNone
#guard callWorldB copyCtx
#guard !callWorldB { copyCtx with scope := { copyCtx.scope with runtimeSingleton := some "Wrong" } }
#guard !frameIsB copyCtx "Point" "Point" "copy"

#guard singletonFreshB before.classes copyDef
#guard !singletonFreshB after.classes copyDef
#guard singletonFreshB [{ classHeader "Point" with methods := [copyDef] }] copyDef
#guard singletonTableFrameB before.classes (classHeader "Point") copyDef
-- A stale snapshot changes the already-recorded superclass chain.
#guard !singletonTableFrameB
  [{ classHeader "Point" with super? := some "Parent" }, classHeader "Parent"]
  (classHeader "Point") copyDef

#print axioms boot_state
#print axioms same_selector_state
#print axioms retained_singleton
#print axioms annotated_singleton_body
#print axioms nested_copy_call
end Checker.Soundness.Typed.SingletonStateControls
