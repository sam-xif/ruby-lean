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
  dregistry_semJudge derivD_intLit

/-- …and the **safety** half, which is the end of the chain: from any conformant machine, the
program never reaches a type-stuck outcome, at any fuel. -/
theorem derivD_intLit_safe {Γ : Env} {n : Int} {m : Machine}
    (hm : StateOk Ratchet.ctx0 Γ .ivar0 m) : StuckFree m (.int n) :=
  dregistry_safe derivD_intLit hm

/-- The invariant form the safety above is an instance of — and the thing the old
whole-program `SafeJudge` could not say: safety at a machine whose continuation is **not**
empty is available as soon as `DKontOk` has a frame clause for it. Stated here at the one
continuation `DKontOk` admits today, so the shape is on file before the frames arrive. -/
theorem derivD_intLit_safeUnder {Γ : Env} {n : Int} :
    SafeUnder Γ (.int n) .int Γ := dregistry_safeUnder derivD_intLit

/-- And a local read, which is the rule whose premise the certificate cannot supply. -/
theorem derivD_var_sem {Γ : Env} {x : String} {τ : Ty} (hget : envGet? Γ x = some τ)
    (halias : isAliasTy τ = false) : SemJudgeA Γ (.var .lvar x) τ Γ :=
  dregistry_semJudge (by intro F hF; exact hF DClink.var (by simp [dclinks]) hget halias)

/-! ### The refusal

`DJudge.if'` is a real, used rule — `Ratchet/Check.lean` types every conditional with it and
the corpus ladder reaches rung 018 through it — and it has no answer-typed proof. Under a
discipline where rules are authored and justified separately that would be a line in a report.
Here it makes `register_dclink` fail, and the failure is what this control checks: if the gate
ever stops refusing, this file goes red.

(It named `vasgn` until clink 72, when `vasgn` acquired its proof and the control had to move
to a rule that still lacks one. That is the control doing its job.) -/

/-- error: register_dclink: Ratchet.DJudge.if' has no answer-typed proof.
Write `theorem Ratchet.Denote.Typed.SemA.if' : SemJudgeA …` in Denote/Typed/JudgeA.lean first.
A rule with no proof is not a rule (Denote/Clink/Spec.lean).
-/
#guard_msgs in
register_dclink DJudge.if'

/-! ### …and a rule whose premise escapes the family is refused *before* its proof is asked for

`if'` above is refused for the ordinary reason — nobody has proved it. `seq` and `prim` are
refused for a **stronger** one, and the order of the two checks is the point: writing
`SemA.seq` would not help, because the statement it would have to prove is the wrong one.

`ruleForm` rewrites only the heads in `dFamField`. `DJudge.seq`'s premise is `DJudgeSeq`,
which is not one, so the derived form would be

    fun F => ∀ …, DJudgeSeq Γ es τ Γ' → F.judge Γ (.seq es) τ Γ'

— a premise that is the **syntactic** relation rather than the family's. At `dsemFam` that
obligation reads *"a sequence is safe given a raw sub-derivation"*, and a raw sub-derivation
may be built from the three rules with no semantic proof at all. The registry's whole claim is
that `DJudgeC dclinks` means "derivable using only registered rules"; this is the side door
out of it. Compare `vasgn`, whose premise *is* rewritten (`F.judge Γ e τ Γ₁`) and whose
obligation is therefore compositional.

Refused mechanically, by reading the constructor's premises — not by trusting that nobody
types `register_dclink DJudge.seq`. See `found-issues.md` §F31. -/

/-- error: register_dclink: Ratchet.DJudge.seq's premises reach Ratchet.DJudgeSeq, which DFam does not carry.
`ruleForm` would leave that premise as the raw inductive, so the clink's obligation would quantify over derivations built from UNREGISTERED rules -- the registry's discipline, escaped through a side door.
Give DFam a field for it (and `dFamField` a row) before registering this rule (Denote/Typed/Clink.lean, header).
-/
#guard_msgs in
register_dclink DJudge.seq

/-- error: register_dclink: Ratchet.DJudge.prim's premises reach Ratchet.DJudgeAll, which DFam does not carry.
`ruleForm` would leave that premise as the raw inductive, so the clink's obligation would quantify over derivations built from UNREGISTERED rules -- the registry's discipline, escaped through a side door.
Give DFam a field for it (and `dFamField` a row) before registering this rule (Denote/Typed/Clink.lean, header).
-/
#guard_msgs in
register_dclink DJudge.prim

/-! ### …and a proof of a different rule does not stand in for it

The two `rfl`s say what the kernel enforces at the point of registration: both field types are
**computed from the rule**, so `sem := SemA.truLit` in `intLit`'s position is a type error.
Stated as `rfl` rather than as a captured type error on purpose — an error message carries
metavariable numbers and elaborator phrasing, and a control that goes red when Lean rewords a
diagnostic is a control that gets deleted. -/

example : DClink.intLit.form dsemFam =
    (∀ {Γ : Env} {n : Int}, SemSafeA Γ (.int n) .int Γ) := rfl

/-- …and `SemSafeA` really is the pair, so "registered" means both obligations were proved. -/
example {Γ : Env} {n : Int} :
    SemSafeA Γ (.int n) .int Γ = (SemJudgeA Γ (.int n) .int Γ ∧ SafeUnder Γ (.int n) .int Γ) :=
  rfl

example : DClink.intLit.form dsynFam =
    (∀ {Γ : Env} {n : Int}, DJudge Γ (.int n) .int Γ) := rfl

#print axioms derivD_intLit
#print axioms derivD_intLit_sem
#print axioms derivD_intLit_safe
#print axioms derivD_intLit_safeUnder
#print axioms derivD_var_sem


end Ratchet.Denote.Typed
