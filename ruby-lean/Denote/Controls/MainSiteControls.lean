import Denote.Rules.Instance.MainReturn
import Denote.Rules.Instance.InstanceCall
import Denote.Controls.ClassStateControls

/-! Heap-only main facts survive other scopes. A builtin's presence is not bare-name absence. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem retained_main_after_class (hb : bootOkB = true) {name : String}
    (hq : FreshClass.nativeFrameB ctx0 name = true)
    (hn : constOwn bootMachine.heap Boot.objectId name = none) (hne : name.isEmpty = false) :
    ∃ n, Interp.stepFn (evalFrom bootMachine (.class' name none .nil)) = .next n ∧
      StateOk (classBodyCtx ctx0 name) [] .ivar0 n ∧ MainSite ctx0 n.heap := by
  obtain ⟨n, hs, hm⟩ := boot_class_state hb hq hn hne
  exact ⟨n, hs, hm, hm.mainSite rfl⟩

private def builtinX : MethodDef :=
  { owner := Boot.objectId, params := [], body := .nil, builtin := some "Object#nil?" }

/-- Even retained value/field framing and MainReady do not imply bare-name absence.
This is a component countermodel, not a claim that the old full StateOk accepted the heap. -/
theorem builtin_breaks_bare_main {κ : Ctx} {m : Machine} (hr : MainReady m)
    (hf : nameFreeN κ "x" = true) :
    Framed m { m with heap := defineMethod m.heap Boot.objectId "x" builtinX } ∧
      MainReady { m with heap := defineMethod m.heap Boot.objectId "x" builtinX } ∧
      ¬ MainSite κ (defineMethod m.heap Boot.objectId "x" builtinX) := by
  refine ⟨Framed_defineMethod .., hr.methodWrite _ _ _ (by decide), ?_⟩
  intro bad
  have hx : lookup (defineMethod m.heap Boot.objectId "x" builtinX) (.ref Boot.mainId) "x" =
      some (Boot.objectId, builtinX) := by
    rw [lookup, Proof.classOf_defineMethod, Proof.ancestors_defineMethod, hr.chain]
    exact Proof.lookup_go_defineMethod_self _ _ _ _ hr.classLive _
  have hnone := bad.bare "x" .x hf
  rw [hx] at hnone
  cases hnone

#guard (ctxEq? ctx0 { ctx0 with pos := { ctx0.pos with mainWorld := false } }).isNone
#guard match Interp.run 30 (evalFrom
    { bootMachine with heap := defineMethod bootMachine.heap Boot.objectId "x" builtinX }
    (.send none "x" [] none)) with
  | .value (.bool false) _ => true
  | _ => false

#print axioms retained_main_after_class
#print axioms builtin_breaks_bare_main
end Ratchet.Denote.Typed
