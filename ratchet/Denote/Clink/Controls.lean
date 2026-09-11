import Denote.Clink.Registry

/-!
# `Denote/Clink/Controls.lean` — the gate, exercised in both directions

`found-issues.md` §F24 vs §F25: **run the control.** A registry that accepted everything
would satisfy `registry_sound` just as well, and a refusal proves nothing unless the same
command *accepts* something. So this file does four things, all at build time:

| § | control | what it pins |
|---|---|---|
| 1 | a derivation in `JudgeC clinks`, and `SemJudge` out of it | the loop closes: registered rules compose, and the semantic reading falls out |
| 2 | `register_clink` on a rule with no proof **fails**, with its message captured | the gate is a build failure, not a report line |
| 3 | a `Clink` whose `sem` proves a *different* rule **fails to typecheck** | `Clink.sem`'s type is computed from the rule, so it cannot be weakened by renaming |
| 4 | the positive control for §2/§3 | the failures in §2 and §3 are about the proof, not about the command being broken |

§2 and §3 use `#guard_msgs`, so the *refusal itself* is checked by the build: if the gate ever
stops refusing, this file goes red.
-/

set_option autoImplicit false

namespace Ratchet.Denote

open RubyCore Ratchet

/-! ## §1 A derivation, and its semantic consequence

A derivation is a term polymorphic in the family, so it never mentions `JudgeC`'s definition
and never needs a closure lemma (`Spec.lean` §4). Membership in the registry is the only
side condition, and it is decided by `simp` against the list. -/

/-- The leaf. `hF c hc` *is* the rule, at whatever family the consumer picked. -/
theorem derivC_intLit {κ : Ctx} {Γ : Env} {I : Ty} {n : Int} :
    (JudgeC clinks).judge κ Γ I (.int n) .int (κ.afterStmt (.int n) .int) Γ I := by
  intro F hF
  exact hF Clink.Judge.intLit (by simp [clinks])

/-- Two rules composed: `x = 1`. The premise is the sub-derivation applied at the *same*
family, which is the whole content of the Church encoding — and the reason an unregistered
rule has nothing to compose with. -/
theorem derivC_vasgn_int {κ : Ctx} {Γ : Env} {I : Ty} {x : String} {n : Int}
    (hcap : capStale x .int .int = false) (hctx : capStaleCtx x .int κ = false) :
    (JudgeC clinks).judge κ Γ I (.vasgn .lvar x (.int n)) .int
      (κ.afterStmt (.vasgn .lvar x (.int n)) .int)
      (envSet (killClosOver (killAliasesTo Γ x) x .int) x .int) (killClosOverSpine I x .int) := by
  intro F hF
  exact hF Clink.Judge.vasgn (by simp [clinks]) (derivC_intLit F hF) hcap hctx rfl

/-- **The loop, closed.** A derivation that used only registered rules is semantically true,
with no hypothesis about the registry and no induction over a rule list. This is the theorem
the old two-ladder framing could never state: `AdequacyHyps → AdequacyTarget` needed all 83,
so it was never available at any size. -/
theorem derivC_vasgn_sem {κ : Ctx} {Γ : Env} {I : Ty} {x : String} {n : Int}
    (hcap : capStale x .int .int = false) (hctx : capStaleCtx x .int κ = false) :
    SemJudge κ Γ I (.vasgn .lvar x (.int n)) .int
      (κ.afterStmt (.vasgn .lvar x (.int n)) .int)
      (envSet (killClosOver (killAliasesTo Γ x) x .int) x .int) (killClosOverSpine I x .int) :=
  registry_sound (derivC_vasgn_int hcap hctx)

/-- And it is a `Judge` derivation too, from the other field of the same clinks. -/
theorem derivC_vasgn_syn {κ : Ctx} {Γ : Env} {I : Ty} {x : String} {n : Int}
    (hcap : capStale x .int .int = false) (hctx : capStaleCtx x .int κ = false) :
    Judge κ Γ I (.vasgn .lvar x (.int n)) .int
      (κ.afterStmt (.vasgn .lvar x (.int n)) .int)
      (envSet (killClosOver (killAliasesTo Γ x) x .int) x .int) (killClosOverSpine I x .int) :=
  registry_syn (derivC_vasgn_int hcap hctx)

/-! ## §2 The refusal: a rule with no proof does not enter the judgment

`Judge.if'` is a real, used, corpus-climbing rule — `Ratchet/Validate.lean` types every
conditional in the corpus with it — and it has no semantic proof on file. Under the old
discipline that made it one line of a 48/83 report. Here it makes `register_clink` fail, and
the failure is what this control checks. -/

/-- error: register_clink: Ratchet.Judge.if' has no semantic proof.
Write `theorem Ratchet.Denote.Sem.Judge.if' : Ratchet.Denote.Obl.Judge.if' := …` in Denote/Rules/ first.
A rule with no proof is not a rule (Denote/Clink/Spec.lean).
-/
#guard_msgs in
register_clink Judge.if'

/-! ## §3 …and a proof of a *different* rule does not stand in for it

The other half of the gate, and the one the old `Denote/Ladder.lean` had to enforce with an
`isDefEq` check *inside the report*: naming a theorem after a rule does not make it about
that rule. Here the two field types are **computed from the rule**, so the kernel enforces it
at the point of registration — and the two `rfl`s below are the statement of exactly what it
enforces, which is a more stable control than matching an error message.

Stated as `rfl` rather than as a captured type error on purpose: an error message carries
metavariable numbers and elaborator phrasing, and a control that goes red when Lean rewords a
diagnostic is a control that will be deleted. These go red only if the derivation changes. -/

/-- The `sem` field's type **is** the derived obligation — the same `Prop`
`Denote/Sem/Obligations.lean` produces for this rule, which is the one
`Denote/Rules/Lit.lean` proved. So `Sem.Judge.truLit` in that position is a type error, and
so is anything else proving something weaker. -/
example : Clink.Judge.intLit.form semFam = Obl.Judge.intLit := rfl

/-- And the `syn` field's type is the constructor's own type, which is why `syn := Judge.intLit`
is the only thing that goes there. The two `rfl`s together are "authored once, read twice". -/
example : Clink.Judge.intLit.form synFam =
    (∀ {κ : Ctx} {Γ : Env} {I : Ty} {n : Int},
      Judge κ Γ I (.int n) .int (κ.afterStmt (.int n) .int) Γ I) := rfl

/-- The same for a rule with premises, where there is something to get wrong: `vasgn`'s
obligation has the premise as a `SemJudge` and the conclusion as a `SemJudge`, and the
side conditions untouched. -/
example : Clink.Judge.vasgn.form semFam = Obl.Judge.vasgn := rfl

/-! ## §4 The positive control

§2's refusal must be about the missing proof rather than about the command being broken, so
the same shape is exercised with a rule that has one. A hand-written `form` is used here and
only here — `register_clink` derives it (`Derive.lean` §"Why not accept a hand-written form")
— and the last `rfl` is the check that the hand-written one and the derived one agree. -/

def clinkHonest : Clink synFam semFam :=
  { name := "Judge.intLit"
    form := fun F => ∀ {κ : Ctx} {Γ : Env} {I : Ty} {n : Int},
      F.judge κ Γ I (.int n) .int (κ.afterStmt (.int n) .int) Γ I
    syn := Judge.intLit
    sem := Sem.Judge.intLit }

example : clinkHonest.form = Clink.Judge.intLit.form := rfl

#print axioms derivC_intLit
#print axioms derivC_vasgn_int
#print axioms derivC_vasgn_sem
#print axioms derivC_vasgn_syn

end Ratchet.Denote
