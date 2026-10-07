import Checker.Check.Check
import Books.TypeSoundness.Registry.AuditBridge
import Books.TypeSoundness.Conformance.Core.Boot

/-! The actual validator's end-to-end safety theorem under the active clink
registry. validateD carries enabled-rule evidence, so this bridge needs only
active clinks and their dependencies. The traced judgments cover every authoring
constructor; raw-DJudge completeness is retained in Soundness/Full.lean. -/
set_option autoImplicit false
namespace Checker.Soundness.Typed
open RubyCore Checker Checker.Soundness

/-- Every accepted traced judgment crosses the active registry. -/
theorem validateD_certified {p : Checker.Expr} {d : Deriv}
    (h : validateD p d = true) :
    ∃ τ Γ' κ' I', (DJudgeC dclinks).judge [] p τ Γ' ctx0 .ivar0 κ' I' := by
  obtain ⟨c, _, he⟩ := validateD_enabled h
  refine ⟨c.ty, c.out, c.ctx, c.spine, ?_⟩
  intro F hF
  exact Audited.DJudge.certified c.judged F hF he

/-- Every accepted program is safe at every fuel from any conformant top-level
machine. The hypothesis remains the actual executable validator's verdict. -/
theorem validateD_safe {p : Checker.Expr} {d : Deriv}
    (h : validateD p d = true)
    {m : Machine} (hm : StateOk ctx0 [] .ivar0 m) : StuckFree m p := by
  obtain ⟨_, _, _, _, hj⟩ := validateD_certified h
  exact dregistry_safe hj hm

theorem validateD_safe_boot {p : Checker.Expr} {d : Deriv}
    (h : validateD p d = true) (hb : bootOkB = true) :
    StuckFree bootMachine p := validateD_safe h (stateOk_boot hb)

/-- The final theorem concerns the actual model runner, for arbitrary fuel. -/
theorem validateD_safe_run {p : Checker.Expr} {d : Deriv}
    (h : validateD p d = true) (hb : bootOkB = true) (fuel : Nat) :
    Semantics.typeStuck (Semantics.run fuel (toRuby p)) = false := by
  have hs : Semantics.typeStuck (Interp.run fuel (evalFrom bootMachine p)) = false :=
    validateD_safe_boot h hb fuel
  unfold bootMachine at hs
  unfold Semantics.run
  -- The boot result is abstracted before the case split. The prelude is a term now, so
  -- the boot is something `simp` and `rfl` can *run*; left in the goal, they try to.
  generalize Semantics.bootedMachine = booted at hs ⊢
  cases booted with
  | error msg => rfl
  | ok m => exact hs

#print axioms validateD_certified
#print axioms validateD_safe
#print axioms validateD_safe_boot
#print axioms validateD_safe_run
end Checker.Soundness.Typed
