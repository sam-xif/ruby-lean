import Ratchet.Check.Check

/-! A profile-parameterized restriction of `validateD` to literal rules. The
ordinary checker still checks the exact certificate payload. This module knows
no semantic registry: the bridge supplies its active rule policy. -/
set_option autoImplicit false
namespace Ratchet

/-- Source evidence for a literal and the exact authoring-rule name it uses. -/
inductive LiteralJudge : Expr → Ty → String → Prop where
  | intLit {n : Int} : LiteralJudge (.int n) .int "intLit"
  | fltLit {bits : UInt64} : LiteralJudge (.flt bits) .float "fltLit"
  | strLit {s : String} : LiteralJudge (.str s) (.cls "String") "strLit"
  | symLit {s : String} : LiteralJudge (.sym s) .sym "symLit"
  | truLit : LiteralJudge .tru .bool "truLit"
  | flsLit : LiteralJudge .fls .bool "flsLit"
  | nilLit : LiteralJudge .nil .nilT "nilLit"

theorem LiteralJudge.judged {p : Expr} {τ : Ty} {rule : String}
    (h : LiteralJudge p τ rule) {Γ : Env} {κ : Ctx} {I : Ty} :
    DJudge Γ p τ Γ κ I := by
  cases h
  · exact .intLit
  · exact .fltLit
  · exact .strLit
  · exact .symLit
  · exact .truLit
  · exact .flsLit
  · exact .nilLit

structure LiteralHint (p : Expr) where
  ty : Ty
  rule : String
  judged : LiteralJudge p ty rule

/-- Only direct literal hints qualify. Payload equality remains `validateD`'s
job; a flow wrapper cannot bypass the rule gate by containing a literal. -/
def literalHint? (p : Expr) (d : Deriv) : Option (LiteralHint p) :=
  match p, d with
  | .int _, .intLit _ => some ⟨.int, "intLit", .intLit⟩
  | .flt _, .fltLit _ => some ⟨.float, "fltLit", .fltLit⟩
  | .str _, .strLit _ => some ⟨.cls "String", "strLit", .strLit⟩
  | .sym _, .symLit _ => some ⟨.sym, "symLit", .symLit⟩
  | .tru, .truLit => some ⟨.bool, "truLit", .truLit⟩
  | .fls, .flsLit => some ⟨.bool, "flsLit", .flsLit⟩
  | .nil, .nilLit => some ⟨.nilT, "nilLit", .nilLit⟩
  | _, _ => none

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
