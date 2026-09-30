# Rebuilding the clink registry

The active registry starts with the seven literal rules. The other 92 authoring
rules are explicitly gated out. `intLit` remains the non-vacuity anchor.

From `ruby-lean/`, run:

```sh
./scripts/run_typed_ratchet.sh --clink-rebuild
```

This checks isolation, the profile census, registration refusal controls, every
active clink's semantic proof, registry soundness and a real model-safety witness.
It reports **CLINK REBUILD CHECKS PASS** when those checks pass. It does not claim
that the full checker or corpus is certified. The ordinary typed gate refuses a
partial profile before building the unrestricted checker safety bridge. Its
coverage, corpus floors, agreement checks and negative controls remain intact.

## Re-enable a rule

1. Add its exact constructor suffix to `Policy.lean`'s `clinkProfile` list, such
   as `var`, `DJudgeAll.cons` or `DFlow.call`.
2. Add its proof-provider import to `ActiveProofs.lean`. The former complete
   import set is retained in `FullProofs.lean` as a reference.
3. Repair the selected rule and its necessary dependencies, then rerun the
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

To restore the complete profile, set `clinkProfile := none` and import
`Denote.Clink.FullProofs` in `ActiveProofs.lean`. Every proof must then build again
before the full typed gate can pass. No production floor is reset during this
rebuild.

`GateControls.lean` tests the mechanism with a separate syntactic fixture. That
fixture contributes no clinks to the real registry and makes no Ruby safety
claim. `scripts/probes/clink-rebuild.lean` checks the real safety witness.
