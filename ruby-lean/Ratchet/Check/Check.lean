import Ratchet.Check.Raw
import Ratchet.Audit.Raw
import Ratchet.Audit.Permissions
import Ratchet.ClinkPolicy

/-! The production acceptance boundary. The traced checker is generated from
Raw and its body/cache helpers. Its result contains a constructor-indexed proof
and the computational trace of every rule used. Acceptance checks that trace
against the shared registry policy, with no expression-specific allowlist. -/
set_option autoImplicit false
namespace Ratchet

def fuelD : Nat := 200

def DTyped (p : Expr) : Prop := ∃ τ Γ' κ' I', DJudge [] p τ Γ' ctx0 .ivar0 κ' I'

/-- Parameterized acceptance for policy controls. The production entry point
below supplies the same policy used by the semantic registry. -/
def validateDWith (enabled : String → Bool) (p : Expr) (d : Deriv) : Bool :=
  match Audit.check fuelD [] p d with
  | none => false
  | some c => Audit.rulesEnabled enabled c.rulesUsed

/-- **The ladder's verdict.** Every rule in the actual checked derivation must
be enabled, including companion rules and retained/rechecked body premises. -/
def validateD (p : Expr) (d : Deriv) : Bool := validateDWith clinkEnabled p d

/-- Acceptance yields the traced checker result and permission for all of its
constructor-derived rule uses. No untrusted certificate supplies this evidence. -/
theorem validateD_enabled {p : Expr} {d : Deriv} (h : validateD p d = true) :
    ∃ c : Audit.Certified [] p,
      Audit.check fuelD [] p d = some c ∧ Audit.rulesEnabled clinkEnabled c.rulesUsed = true := by
  unfold validateD validateDWith at h
  cases hc : Audit.check fuelD [] p d with
  | none => simp [hc] at h
  | some c => exact ⟨c, rfl, by simpa only [hc] using h⟩

theorem validateD_typed {p : Expr} {d : Deriv} (h : validateD p d = true) : DTyped p := by
  obtain ⟨c, _, _⟩ := validateD_enabled h
  exact ⟨c.ty, c.out, c.ctx, c.spine, Audit.DJudge.toRaw c.judged⟩
end Ratchet
