import Denote.Sem.Framed

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

A judgment's relations, bundled as a **record of predicates**, so that a rule's premises and
conclusion can be stated against a parameter rather than against a particular relation. The
record itself is supplied by whoever is registering rules — `Denote/Typed/Clink.lean`'s
`DFam` is the one instance today — and everything in this file is generic in it.

The instance that used to live here was `Fam`, the eight-member record mirroring
`Ratchet/Judge.lean`'s mutual family, together with `JudgeC` and sixteen soundness theorems
over it. It went with that judgment (clink 68). What is left is the mechanism, which was
always the part worth having. -/

/-- A rule, with the judgment abstracted. Both readings are instantiations of one of these.

Generic in the family **record type**: `Denote/Typed/Clink.lean`'s `DFam` is the instance, and
`Clink`/`Closed` below never mention it. -/
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

/-! ## §3 The certified judgment, and why it is not here

`JudgeC R` — the least family closed under `R`, written impredicatively as
`∀ F, Closed R F → F.judge …` — has to *construct* a family record, so it is the one part of
the mechanism that cannot be generic in the record type. Each judgment defines its own; it is
three lines. `Denote/Typed/Clink.lean` §3 is the instance, with its one-line soundness
theorem, and reading it is the fastest way to see what `Closed` buys:

```lean
def DJudgeC (R : List (Clink dsynFam dsemFam)) : DFam where
  judge Γ e τ Γ' := ∀ F : DFam, Closed R F → F.judge Γ e τ Γ'

theorem dregistry_sound (h : (DJudgeC dclinks).judge Γ e τ Γ') : SemJudgeA Γ e τ Γ' :=
  h dsemFam (closed_target dclinks)
```

**A derivation is a term, and it never mentions closure.** To use a registered rule you are
*handed* it: `hF` is the closure hypothesis, `hF c hc` is the rule at whatever family the
consumer chose, and the premises are sub-derivations applied at the same family. No
monotonicity, no closure lemma, no induction — and a derivation that used an unregistered rule
would have nothing to apply, which is the sense in which growth is sound by construction.

No generic closure lemma exists and there cannot be one: a Horn rule mentions the judgment
**contravariantly** in its premises, so `c.form` is not monotone in `F` and `Closed R (JudgeC R)`
has no proof uniform in `c`. It is not needed — see the worked derivations in
`Denote/Typed/Clink.lean` §5. -/

end Ratchet.Denote
