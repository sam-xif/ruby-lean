import Denote.Rules.Singleton.SingletonState
import Denote.Rules.Instance.MemberInstall
import Denote.Controls.ClassHeaderControls
import Denote.Sem.Class.ClassGuards

/-! Full boot-grounded publication followed by an ordinary write with the same selector. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed.SingletonStateControls
open RubyCore Ratchet Ratchet.Denote

private def copyDef : Defn := ⟨"copy", [.req "value"], .var .lvar "value"⟩
private def body : Ratchet.Expr := .defs .self' copyDef.name copyDef.params copyDef.body
private def before : Ctx := classHeaderCtx (classBodyCtx ctx0 "Point") "Point"
private def after : Ctx := singletonDeclCtx before (classHeader "Point") copyDef
private def instanceDef : Defn := ⟨"copy", [], .tru⟩
private def c : Cls := classWithSingleton (classHeader "Point") copyDef

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
end Ratchet.Denote.Typed.SingletonStateControls
