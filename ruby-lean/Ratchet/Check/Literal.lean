import Ratchet.Check.Check
import Ratchet.Check.LiteralEvidence

/-! A profile-parameterized restriction of `validateD` to literal rules. The
ordinary checker still checks the exact certificate payload. This module knows
no semantic registry: the bridge supplies its active rule policy. -/
set_option autoImplicit false
namespace Ratchet

def validateLiteralD (enabled : String → Bool) (p : Expr) (d : Deriv) : Bool :=
  match literalHint? p d with
  | none => false
  | some c => enabled c.rule && validateD p d

/-- Acceptance carries source-rule evidence, active-policy membership, and
ordinary validator acceptance. No untrusted hint can supply these facts. -/
theorem validateLiteralD_typed {enabled : String → Bool} {p : Expr} {d : Deriv}
    (h : validateLiteralD enabled p d = true) :
    ∃ τ rule, LiteralJudge p τ rule ∧ enabled rule = true ∧ validateD p d = true := by
  unfold validateLiteralD at h
  cases hc : literalHint? p d with
  | none => simp [hc] at h
  | some c =>
    rw [hc] at h
    obtain ⟨he, hv⟩ := Bool.and_eq_true_iff.mp h
    exact ⟨c.ty, c.rule, c.judged, he, hv⟩

theorem validateLiteralD_validated {enabled : String → Bool} {p : Expr} {d : Deriv}
    (h : validateLiteralD enabled p d = true) : validateD p d = true :=
  (validateLiteralD_typed h).choose_spec.choose_spec.2.2

end Ratchet
