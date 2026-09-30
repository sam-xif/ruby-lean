# Rebuilding the clink registry

The active registry starts with the seven literal rules. The other 92 authoring
rules are explicitly gated out. `intLit` remains the non-vacuity anchor.

From `ruby-lean/`, run:

```sh
./scripts/run_typed_ratchet.sh --clink-rebuild
```

This checks isolation, the profile census, registration refusal controls, every
active clink's semantic proof, registry soundness, the actual validateD and
Bridge.lean's final model-runner safety theorem.
It reports **CLINK REBUILD CHECKS PASS** when those checks pass. It does not claim
that the full checker or corpus is certified. The ordinary typed gate refuses a
partial profile before the historical full-coverage corpus audit. Its
coverage, corpus floors, agreement checks and negative controls remain intact.

## Re-enable a rule

1. Add its exact constructor suffix to `Ratchet/ClinkPolicy.lean`'s `clinkProfile` list, such
   as `var`, `DJudgeAll.cons` or `DFlow.call`.
2. Add its proof-provider import to `ActiveProofs.lean`. The former complete
   import set is retained in `FullProofs.lean` as a reference.
3. Repair the selected rule and its necessary dependencies. Extend the validator
   evidence and its Bridge certification case when admitting a new expression
   rule, including evidence for every premise/body rule it uses. Then rerun the
   rebuild command. Enabled rules with missing or mistyped proofs fail the build.

These names identify rules, rather than the chronological clink numbers in the
working notes. Unknown names and duplicates fail; the full authoring census is
still fixed at 99. `dRegisteredRules` contains checked active rules; `dGatedRules`
contains excluded ones; `dUnregisteredRules` is reserved for missing enabled
proofs, which prevent the registry from building. Neither automatic discovery
nor an explicit `register_dclink` can admit a gated rule merely because its proof
is imported.

`Family.lean` retains all seventeen syntactic projections. `Target.lean` uses
the same canonical semantic contracts for imported projections. Unavailable
projections are `False`, and registration refuses every enabled constructor
whose conclusion **or premise** mentions one. Thus the partial profile avoids
importing disabled proof families without weakening any active rule's contract.
Every admitted clink is still kernel-checked against its constructor-derived
form. The ordinary registry safety statements are unchanged.

The complete registry profile is `clinkProfile := none` with
`Denote.Clink.FullProofs` imported by `ActiveProofs.lean`. Restoring complete
admission additionally requires rebuilding the validator evidence/certification
for compound rules and bodies; merely enabling their proofs does not admit them.
Every proof must build before the full typed gate can pass. No production floor
is reset during this rebuild.

`GateControls.lean` tests the mechanism with a separate syntactic fixture. That
fixture contributes no clinks to the real registry and makes no Ruby safety
claim. `scripts/probes/clink-rebuild.lean` checks the real safety witness.

## The actual validator and bridge

`validateD` itself now requires an enabled rule, source evidence for the current
rebuild fragment, and ordinary `check` success (including exact payload matching).
The shared policy lives in `Ratchet/ClinkPolicy.lean`, preserving isolation;
`Denote/Clink/Policy.lean` exports the same definitions for registry clients.
There is no separate acceptance policy for the production validator.

`Denote/Bridge.lean` proves the original `validateD_safe`, `validateD_safe_boot`
and `validateD_safe_run` statements from that enabled evidence. The final theorem
states, for any fuel:

```lean
validateD p d = true → bootOkB = true →
  Semantics.typeStuck (Semantics.run fuel (toRuby p)) = false
```

Its proof references only active clinks. Disabled literal cases are discharged
by their contradictory policy hypothesis; Lean kernel-checks both paths.
Its imports contain the actual checker, active registry and boot facts with
transitive dependencies, excluding the complete authoring-rule certifier and
examples. `Bridge/Full.lean` retains the optional raw-DJudge completeness helpers
for the complete registry. `Bridge/Literal.lean` is now a compatibility wrapper
around the original validator/theorems.

The current evidence supports the seven direct literal rules. Gated literals,
flow wrappers and compound programs are rejected by `validateD`, including in
`ratchetd` and `validate-one`. Raw internal `check` still reconstructs the broader
syntactic judgments; its success alone cannot bypass the enabled acceptance
boundary. Compound admission requires extending restricted evidence for the rule,
its companion premises and any checked/rechecked bodies. Adding its clink name
alone does not yet provide that evidence. The full historical corpus audit and
its production floors remain separate from this rebuilding profile.
