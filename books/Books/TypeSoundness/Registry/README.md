# `Registry/` — no typing rule without its proof

A typing rule is written once, with the judgment family abstracted. Instantiated
one way it is the syntactic rule the checker uses (a constructor of `DJudge`).
Instantiated the other way it is a proof obligation over the real machine. The
registry pairs the two in a structure, `Clink`, whose proof is a field, so a rule
cannot be registered without it.

| File | Contents |
|---|---|
| `Spec.lean` | `Clink`, and the soundness theorems for a registry of them |
| `Family.lean` | `DFam`: the judgment families a rule is abstracted over |
| `Form.lean` | `ruleForm`: from a rule's constructor to its abstract form |
| `Target.lean` | The semantic family, built from the contracts that the imported proofs supply |
| `Registration.lean` | The `register_dclink` command and its checks |
| `ActiveProofs.lean` | Imports the proof of every enabled rule |
| `Registry.lean` | The registry of enabled rules, each with its proof |
| `Policy.lean`, `GateStatus.lean` | Which rules are enabled (from `Checker/ClinkPolicy.lean`), and a count that needs no proof imports |
| `GateControls.lean`, `Controls.lean` | Controls: registering a rule with no proof is refused, and the refusal is itself checked; worked derivations in the certified judgment |
| `Certify.lean`, `AuditBridge.lean` | From a derivation `validateD` accepted to a derivation in the certified judgment |
| `SoundnessAudit.lean` | Rejects any axiom in the soundness theorems beyond Lean's three |

## Enabling a rule

1. Add the rule's constructor name to `clinkProfile` in
   `ruby-lean/Checker/ClinkPolicy.lean`, for example `var`, `DJudgeAll.cons` or
   `DFlow.call`. Enable the companion and body rules its derivations use as
   well.
2. Import the file that proves it in `ActiveProofs.lean`.
3. From `books/`, run `./scripts/check-soundness.sh --proofs-only`. An enabled
   rule with a missing or mistyped proof fails the build.

A rule that is not enabled is refused by `validateD`, so the soundness theorem
never speaks about it. The checker and the certification are generated from the
constructors; enabling a rule needs no new case in either.

[Adding a typing rule](../../../../docs/contributing.md#adding-a-typing-rule)
covers the rest: the rule itself, the derivation emitter and the corpus.
