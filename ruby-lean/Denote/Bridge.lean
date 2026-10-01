import Ratchet.Check.Check
import Denote.Clink.AuditBridge
import Denote.Sem.Core.Boot

/-! The actual validator's end-to-end safety theorem under the active clink
registry. validateD carries enabled-rule evidence, so this bridge needs only
active clinks and their dependencies. The traced judgments cover every authoring
constructor; raw-DJudge completeness is retained in Bridge/Full.lean. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

/-- Every accepted traced judgment crosses the active registry. -/
theorem validateD_certified {p : Ratchet.Expr} {d : Deriv}
    (h : validateD p d = true) :
    ∃ τ Γ' κ' I', (DJudgeC dclinks).judge [] p τ Γ' ctx0 .ivar0 κ' I' := by
  obtain ⟨c, _, he⟩ := validateD_enabled h
  refine ⟨c.ty, c.out, c.ctx, c.spine, ?_⟩
  intro F hF
  exact Audited.DJudge.certified c.judged F hF he

/-- Every accepted program is safe at every fuel from any conformant top-level
machine. The hypothesis remains the actual executable validator's verdict. -/
theorem validateD_safe {p : Ratchet.Expr} {d : Deriv}
    (h : validateD p d = true)
    {m : Machine} (hm : StateOk ctx0 [] .ivar0 m) : StuckFree m p := by
  obtain ⟨_, _, _, _, hj⟩ := validateD_certified h
  exact dregistry_safe hj hm

theorem validateD_safe_boot {p : Ratchet.Expr} {d : Deriv}
    (h : validateD p d = true) (hb : bootOkB = true) :
    StuckFree bootMachine p := validateD_safe h (stateOk_boot hb)

/-- The final theorem concerns the actual model runner, for arbitrary fuel. -/
theorem validateD_safe_run {p : Ratchet.Expr} {d : Deriv}
    (h : validateD p d = true) (hb : bootOkB = true) (fuel : Nat) :
    Semantics.typeStuck (Semantics.run fuel (toRuby p)) = false := by
  have hs := validateD_safe_boot h hb fuel
  cases hboot : Semantics.bootedMachine with
  | error msg => simp only [Semantics.run, hboot, Semantics.typeStuck]
  | ok m => simpa only [Semantics.run, bootMachine, hboot, evalFrom, Machine.initOn] using hs

#print axioms validateD_certified
#print axioms validateD_safe
#print axioms validateD_safe_boot
#print axioms validateD_safe_run
end Ratchet.Denote.Typed
