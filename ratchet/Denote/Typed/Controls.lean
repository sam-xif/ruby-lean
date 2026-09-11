import Denote.Typed.Clink

/-!
# `Denote/Typed/Controls.lean` — derivations in the certified judgment, and the gate

A separate module from `Denote/Typed/Clink.lean` for a mundane reason worth recording: the
registry `dclinks` is declared *by a command* in that file, and `simp` cannot realize a
same-module generated constant's equations (`enableRealizationsForConst`). From here it is an
ordinary import and `simp [dclinks]` decides membership.

`Denote/Clink/Controls.lean` held the old registry's versions of these and went with it
(clink 68). They matter more here, because the soundness theorem is now about a statement
with progress content.
-/

set_option autoImplicit false

namespace Ratchet.Denote.Typed

open RubyCore Ratchet Ratchet.Denote

/-! ## Derivations

A derivation is a term polymorphic in the family, so it never mentions `DJudgeC`'s definition
and never needs a closure lemma (`Denote/Clink/Spec.lean` §3). Membership in the registry is
the only side condition, and `simp` decides it against the list. -/

/-- The leaf: `hF c hc` *is* the rule, at whatever family the consumer picked. -/
theorem derivD_intLit {Γ : Env} {n : Int} :
    (DJudgeC dclinks).judge Γ (.int n) .int Γ := by
  intro F hF
  exact hF DClink.intLit (by simp [dclinks])

/-- **The loop, closed, on a statement with progress content.** A derivation using only
registered rules is answer-typed semantically true: for *every* run that reaches an answer —
value or escape — the answer is in the type or the escape is not type-stuck. -/
theorem derivD_intLit_sem {Γ : Env} {n : Int} : SemJudgeA Γ (.int n) .int Γ :=
  dregistry_sound derivD_intLit

/-- And a local read, which is the rule whose premise the certificate cannot supply. -/
theorem derivD_var_sem {Γ : Env} {x : String} {τ : Ty} (hget : envGet? Γ x = some τ)
    (halias : isAliasTy τ = false) : SemJudgeA Γ (.var .lvar x) τ Γ :=
  dregistry_sound (by intro F hF; exact hF DClink.var (by simp [dclinks]) hget halias)

/-! ### The refusal

`DJudge.vasgn` is a real rule — `Ratchet/Check.lean` types every assignment with it and the
corpus ladder reaches rung 018 through it — and it has no answer-typed proof, because it is
behind `RunAPushK`. Under a discipline where rules are authored and justified separately that
would be a line in a report. Here it makes `register_dclink` fail, and the failure is what
this control checks: if the gate ever stops refusing, this file goes red. -/

/-- error: register_dclink: Ratchet.DJudge.vasgn has no answer-typed proof.
Write `theorem Ratchet.Denote.Typed.SemA.vasgn : SemJudgeA …` in Denote/Typed/JudgeA.lean first.
A rule with no proof is not a rule (Denote/Clink/Spec.lean).
-/
#guard_msgs in
register_dclink DJudge.vasgn

/-! ### …and a proof of a different rule does not stand in for it

The two `rfl`s say what the kernel enforces at the point of registration: both field types are
**computed from the rule**, so `sem := SemA.truLit` in `intLit`'s position is a type error.
Stated as `rfl` rather than as a captured type error on purpose — an error message carries
metavariable numbers and elaborator phrasing, and a control that goes red when Lean rewords a
diagnostic is a control that gets deleted. -/

example : DClink.intLit.form dsemFam =
    (∀ {Γ : Env} {n : Int}, SemJudgeA Γ (.int n) .int Γ) := rfl

example : DClink.intLit.form dsynFam =
    (∀ {Γ : Env} {n : Int}, DJudge Γ (.int n) .int Γ) := rfl

#print axioms derivD_intLit
#print axioms derivD_intLit_sem
#print axioms derivD_var_sem


end Ratchet.Denote.Typed
