import Denote.Sem.Judge

/-!
# `Denote/Clink/Spec.lean` — a rule is one object with two readings, and the semantic one carries its proof

**The pitfall this is built to make impossible.** Until now `Ratchet.Judge` was an
independent inductive that could grow freely, and the semantic side was a *report*: 83
derived obligations, 48 with proofs on file, the gap printed by `lake exe semladder`. Three
things went wrong with that, and they are all the same thing:

1. **A rule could be authored, used by `validate`, and counted as a climbed rung with no
   semantic justification at all.** The ladder said so, in a number, at the bottom of a
   report — and a number is not a gate.
2. **Seven of the undischarged rules turned out to be false as stated** (`found-issues.md`
   §F19/§F23/§F24, `AGENTS.md` §Semantic ratchet status). They were already in the judgment,
   already reachable by a certificate, before anyone knew.
3. **Adequacy was all-or-nothing** — one mutual induction over 83 constructors, so it could
   only ever close at 83/83, which meant it never closed, which meant nothing forced the
   pairing. The EMERGENCY EXIT (`implementation-notes.md`, clink 64) is what that dead end
   looks like from inside.

The reshape: **a rule enters the judgment only as a `Clink`, and a `Clink` cannot be
constructed without the proof.** Not by convention — by typing.

## The device

A rule is written **once**, with the judgment family abstracted:

```
form : Fam → Prop
```

`Fam` is the eight-member family of `Ratchet/Judge.lean` as a *record of predicates*, so a
rule's premises and conclusion are stated against a parameter rather than against a
particular relation. Instantiating that one `form` twice gives the two readings, and they
cannot drift because there is only one of them:

| reading | instantiation | who supplies it |
|---|---|---|
| syntactic | `form synFam` | the `Judge` constructor itself |
| semantic | `form semFam` | **a proof, and it is a field** |

`Clink` bundles the two, and `Clink.sem`'s *type* is `form semFam`. There is no partial
`Clink`, no `sorry`ed one, and no way to name one after a rule and give it a weaker
statement: the type is computed from the rule.

This is `Denote/Sem/Obligations.lean`'s substitution, reified. That file derived
`Obl.<Family>.<rule>` by replacing one constant with another inside the constructor's type;
here the replacement is by a *projection of a parameter*, which is the same operation made
first-class, and `Denote/Clink/Derive.lean` performs it.

## The judgment is then generated from the registry

```
JudgeC R  =  the least family closed under every rule in R
```

written impredicatively — `∀ F : Fam, (∀ c ∈ R, c.form F) → F.judge …` — which is the
Böhm–Berarducci encoding of the inductive family, available because `Prop` is impredicative.
Three consequences, and they are the whole point:

* **Soundness is unconditional and one line.** `judgeC_sem` instantiates `F := semFam` and
  discharges the closure hypothesis from the clinks' own `sem` fields. It holds for *any*
  registry, at every size, today. There is no terminal clink, no 83/83, nothing to wait for.
* **An unregistered rule is not in the judgment.** It is not an undischarged obligation, not
  a rung owed: it is simply not a rule. So the failure mode of §1 above is not "reported
  better", it is gone — and the failure mode of §2 cannot happen, because a rule that is
  false as stated has no `sem` field and therefore no `Clink`.
* **A derivation is a term, polymorphic in `F`.** You build one by using the rules you are
  given (`hF c hmem`), so a derivation *is* a witness that only registered rules were used.
  §4's examples are one line each.

## What this does not claim

* **`Judge → JudgeC` is false**, and deliberately so: `Judge` has rules with no clink. The
  provable direction is `judgeC_syn` (`JudgeC R → Judge`), which says the registry is a
  *certified sub-judgment* of the authoring surface. `Denote/Clink/Registry.lean` reports the
  difference as **coverage**, which is what it is.
* **No generic closure lemma**, and there cannot be one: a Horn rule mentions the judgment
  *contravariantly* in its premises, so `c.form` is not monotone in `F` and
  `Closed R (JudgeC R)` has no proof that is uniform in `c`. It is not needed — see §4, where
  the Church-encoded derivations use `hF` directly and never mention closure.
-/

set_option autoImplicit false

namespace Ratchet.Denote

open RubyCore Ratchet

/-! ## §1 The family, as a parameter

One field per member of `Ratchet/Judge.lean`'s mutual family, at exactly that member's
signature. A field's signature differing from its syntactic twin's would be caught the moment
a `form` is instantiated at `synFam`, i.e. when the `Clink`'s `syn` field is kernel-checked
against the constructor. -/

structure Fam where
  judge : Ctx → Env → Ty → Ratchet.Expr → Ty → Ctx → Env → Ty → Prop
  all : Ctx → Env → Ty → List Ratchet.Expr → List Ty → Env → Ty → Prop
  kw : Ctx → Env → Ty → List Ratchet.KwEntry → List (String × Ty) → Env → Ty → Prop
  pairs : Ctx → Env → Ty → List (Ratchet.Expr × Ratchet.Expr) → Ty → Ty → Env → Ty → Prop
  seq : Ctx → Env → Ty → List Ratchet.Expr → Ty → Ctx → Env → Ty → Prop
  rescues : Ctx → Env → Ty →
    List (List Ratchet.Expr × Option (Ratchet.TargetKind × String) × Ratchet.Expr) → Ty → Prop
  consts : Ctx → List (String × Ratchet.Expr) → Prop
  nested : Ctx → String → Ratchet.Nested → Prop

/-- The syntactic reading: `Ratchet/Judge.lean`'s own relations. -/
def synFam : Fam :=
  { judge := Judge, all := JudgeAll, kw := JudgeKw, pairs := JudgePairs, seq := JudgeSeq,
    rescues := JudgeRescues, consts := JudgeConsts, nested := JudgeNested }

/-- The semantic reading: `Denote/Sem/Judge.lean`'s denotational relations, at the same
signatures (which is what made `Obligations.lean`'s substitution well-typed and is what makes
this one well-typed). -/
def semFam : Fam :=
  { judge := SemJudge, all := SemJudgeAll, kw := SemJudgeKw, pairs := SemJudgePairs,
    seq := SemJudgeSeq, rescues := SemJudgeRescues, consts := SemJudgeConsts,
    nested := SemJudgeNested }

/-- A rule, with the judgment abstracted. Both readings are instantiations of one of these.

Generic in the family **record type**, not just in the two instances: `Ratchet/Check.lean`'s
typed ladder has its own three-member family (`Denote/Typed/Clink.lean`'s `DFam`) and reuses
`Clink`/`Closed` unchanged. Only `JudgeC` below is specific to `Fam`, because it *constructs*
one. -/
abbrev RuleF (F : Type) := F → Prop

/-! ## §2 The clink

**The unit of growth.** `Denote/Clink/Derive.lean`'s `register_clink` is the only intended
way to build one, and it computes `form` from the `Judge` constructor rather than accepting a
hand-written one — so `syn` is the constructor, `sem` is a proof of the derived obligation,
and neither can be about a different rule than the other.

**Parameterised by both families, deliberately** (Norm A, `answer-typed-schema.md` §1). The
committed registry is `Clink synFam semFam`, but the semantic reading is *going* to be
restated — `answer-typed-schema.md` §3.1 replaces `SemJudge` with the answer-typed
`SemJudgeA` — and when it is, the restatement is a **new registry at a new target family**,
not a rewrite of this file. What that costs is then visible and per-rule: every clink whose
`sem` field does not carry over stops building, by name, instead of a report continuing to
say "48 discharged" about a superseded statement. -/

structure Clink {F : Type} (S T : F) where
  /-- `"Judge.vasgn"` — for the report only; nothing depends on it. -/
  name : String
  /-- The rule, authored once. -/
  form : RuleF F
  /-- The rule holds of the **source** family: for `S = synFam` this is the `Judge`
      constructor itself. -/
  syn : form S
  /-- **The rule holds of the target family, and this field is why a rule cannot be
      registered early.** Its type is computed from `form`, so it cannot be weakened by
      renaming. For `T = semFam` it is exactly `Denote/Sem/Obligations.lean`'s derived
      `Obl.<Family>.<rule>`. -/
  sem : form T

variable {F : Type} {S T : F}

/-- A family `G` is **closed** under a registry when every registered rule holds of it. The
one hypothesis every derivation is parameterised by. -/
def Closed (R : List (Clink S T)) (G : F) : Prop := ∀ c ∈ R, c.form G

/-- The **target** family is closed under any registry, because every clink says so. This is
the whole soundness argument; everything below is `Closed` applied. -/
theorem closed_target (R : List (Clink S T)) : Closed R T := fun c _ => c.sem

/-- The **source** family likewise, from the other field. -/
theorem closed_source (R : List (Clink S T)) : Closed R S := fun c _ => c.syn

/-! ## §3 The certified judgment

The least family closed under `R`, impredicatively. Eight members, each the intersection over
all closed families — which is exactly "derivable from the registered rules and nothing
else". -/

def JudgeC {S T : Fam} (R : List (Clink S T)) : Fam where
  judge κ Γ I e τ κ' Γ' I' := ∀ F : Fam, Closed R F → F.judge κ Γ I e τ κ' Γ' I'
  all κ Γ I es τs Γ' I' := ∀ F : Fam, Closed R F → F.all κ Γ I es τs Γ' I'
  kw κ Γ I es kws Γ' I' := ∀ F : Fam, Closed R F → F.kw κ Γ I es kws Γ' I'
  pairs κ Γ I ps kr vr Γ' I' := ∀ F : Fam, Closed R F → F.pairs κ Γ I ps kr vr Γ' I'
  seq κ Γ I es τ κ' Γ' I' := ∀ F : Fam, Closed R F → F.seq κ Γ I es τ κ' Γ' I'
  rescues κ Γ I rs τ := ∀ F : Fam, Closed R F → F.rescues κ Γ I rs τ
  consts κ cs := ∀ F : Fam, Closed R F → F.consts κ cs
  nested κ pfx nst := ∀ F : Fam, Closed R F → F.nested κ pfx nst

/-! ### Soundness, unconditional, at every registry size

Sixteen theorems, each one line: eight taking a `JudgeC` derivation to the **target** family
(soundness) and eight to the **source** (admissibility — the registry is a sub-judgment of
the authoring surface). Nothing here is conditional on the registry being complete, because
completeness is not a thing a registry can fail to be: every rule in it is proved, and a rule
not in it is not a rule.

`Denote/Clink/Registry.lean` §2 specialises the ones a consumer actually calls at
`S := synFam`, `T := semFam`, where the target reads as `SemJudge` on the nose. -/

section Sound
variable {S T : Fam} {R : List (Clink S T)}

theorem judgeC_target {κ Γ I e τ κ' Γ' I'} (h : (JudgeC R).judge κ Γ I e τ κ' Γ' I') :
    T.judge κ Γ I e τ κ' Γ' I' := h T (closed_target R)

theorem judgeC_target_all {κ Γ I es τs Γ' I'} (h : (JudgeC R).all κ Γ I es τs Γ' I') :
    T.all κ Γ I es τs Γ' I' := h T (closed_target R)

theorem judgeC_target_kw {κ Γ I es kws Γ' I'} (h : (JudgeC R).kw κ Γ I es kws Γ' I') :
    T.kw κ Γ I es kws Γ' I' := h T (closed_target R)

theorem judgeC_target_pairs {κ Γ I ps kr vr Γ' I'} (h : (JudgeC R).pairs κ Γ I ps kr vr Γ' I') :
    T.pairs κ Γ I ps kr vr Γ' I' := h T (closed_target R)

theorem judgeC_target_seq {κ Γ I es τ κ' Γ' I'} (h : (JudgeC R).seq κ Γ I es τ κ' Γ' I') :
    T.seq κ Γ I es τ κ' Γ' I' := h T (closed_target R)

theorem judgeC_target_rescues {κ Γ I rs τ} (h : (JudgeC R).rescues κ Γ I rs τ) :
    T.rescues κ Γ I rs τ := h T (closed_target R)

theorem judgeC_target_consts {κ cs} (h : (JudgeC R).consts κ cs) : T.consts κ cs :=
  h T (closed_target R)

theorem judgeC_target_nested {κ pfx nst} (h : (JudgeC R).nested κ pfx nst) :
    T.nested κ pfx nst := h T (closed_target R)

theorem judgeC_source {κ Γ I e τ κ' Γ' I'} (h : (JudgeC R).judge κ Γ I e τ κ' Γ' I') :
    S.judge κ Γ I e τ κ' Γ' I' := h S (closed_source R)

theorem judgeC_source_seq {κ Γ I es τ κ' Γ' I'} (h : (JudgeC R).seq κ Γ I es τ κ' Γ' I') :
    S.seq κ Γ I es τ κ' Γ' I' := h S (closed_source R)

end Sound

/-! ## §4 A derivation is a term, and it never mentions closure

The Church encoding pays for itself here. To use a registered rule you are *handed* it: `hF`
is the closure hypothesis, `hF c hc` is the rule at whatever family the consumer chose, and
the premises are the sub-derivations applied at the same family. No monotonicity, no closure
lemma, no induction — and a derivation that used an unregistered rule would have nothing to
apply, which is the sense in which growth is sound by construction.

The two examples below are stated over an **arbitrary** registry containing the clink, not
over the committed one (Norm A, `answer-typed-schema.md` §1): a derivation is valid in any
registry that has the rules it uses. -/

/-- The shape, concretely, at an arbitrary registry: a premise-free rule applied.
Membership is the only hypothesis, and it is *decidable data* about the registry rather than
a proof obligation about the rule. -/
example {S T : Fam} {R : List (Clink S T)} {c : Clink S T} (hc : c ∈ R)
    (hform : ∀ F : Fam, c.form F → ∀ κ Γ I (n : Int), F.judge κ Γ I (.int n) .int κ Γ I) :
    ∀ κ Γ I (n : Int), (JudgeC R).judge κ Γ I (.int n) .int κ Γ I := by
  intro κ Γ I n F hF
  exact hform F (hF c hc) κ Γ I n

end Ratchet.Denote
