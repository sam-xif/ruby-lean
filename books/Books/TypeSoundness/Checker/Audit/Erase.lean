import Books.TypeSoundness.Checker.Audit.Judgments

/-! What the traced checker needs about the traced judgments beyond their
declarations (`Judgments.lean`): erasure facts and the trace a derivation carries. -/
namespace Checker.Audit

theorem DJudge.plainArg {used : List String} {κ κ' : Ctx} {I I' : Ty}
    {Γ Γ' : Env} {e : Checker.Expr} {τ : Ty}
    (h : DJudge (used := used) Γ e τ Γ' κ I κ' I') : plainArgB e = true :=
  (DJudge.toRaw h).plainArg

def DJudge.rules {used : List String} {κ κ' : Ctx} {I I' : Ty}
    {Γ Γ' : Env} {e : Checker.Expr} {τ : Ty}
    (_h : DJudge (used := used) Γ e τ Γ' κ I κ' I') : List String := used

/-- Existential trace metadata for an optional uniform ordinary-body witness. -/
structure TraceLift (P : List String → Prop) where
  {used : List String}
  down : P used
def TraceLift.up {P : List String → Prop} {used : List String} (down : P used) : TraceLift P := ⟨down⟩
end Checker.Audit
