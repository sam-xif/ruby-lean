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
3. Repair the selected rule and its necessary dependencies. Enable every companion
   and body rule needed by the desired derivation, then rerun the rebuild command.
   Enabled rules with missing or mistyped proofs fail the build. The validator and
   Bridge certification are generated from the constructors; no new acceptance
   case needs to be written.

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
admission requires every semantic proof to build before the full typed gate
can pass. No production floor
is reset during this rebuild.

`GateControls.lean` tests the mechanism with a separate syntactic fixture. That
fixture contributes no clinks to the real registry and makes no Ruby safety
claim. `scripts/probes/clink-rebuild.lean` checks the real safety witness.

## The actual validator and bridge

`validateD` runs a proof-producing checker, then checks that every rule in its
result's trace is enabled. The trace is an index of the checked judgment: a
constructor fixes its own rule name and appends the traces of its judgment
premises. This includes companion rules, initializers, retained/rechecked cache
bodies and uniformly quantified callback bodies. A hint cannot supply or forge
the trace. Exact payload/type/guard checks remain in the checker.

The shared policy lives in `Ratchet/ClinkPolicy.lean`, preserving isolation;
`Denote/Clink/Policy.lean` exports those same definitions. `validateDWith` permits
explicit policies in checker controls; the production `validateD` always uses
the registry's policy.

`Denote/Clink/AuditBridge.lean` derives certification for all seventeen indexed
judgments from their constructor metadata. Each enabled case applies its actual
active clink to the certified premises. Each gated case is impossible because
its trace contains a disabled rule. The generated proofs are kernel checked.
`Denote/Bridge.lean` then proves the original `validateD_safe`,
`validateD_safe_boot` and `validateD_safe_run` statements, including:

```lean
validateD p d = true → bootOkB = true →
  Semantics.typeStuck (Semantics.run fuel (toRuby p)) = false
```

Only active semantic proofs and their transitive dependencies are imported.
`Bridge/Full.lean` retains optional completeness helpers for the unrestricted
raw authoring judgments. The former literal-specific validator/evidence/bridge
modules have been removed.

### Updating the checker

`Ratchet/Check/Raw.lean` and its body/cache helper modules are the authored
computational implementation. The checker modules under `Ratchet/Audit/` are
generated projections using constructor-indexed judgments and explicit trace
metadata. After changing an authored checker source, run:

```sh
python3 scripts/generate_audited_checker.py
```

Both gate modes run `--check` to reject stale generated sources. Judgment,
erasure and certification declarations are generated by Lean from the actual
constructor types. A generation error can fail compilation or cost acceptance;
the safety proof still must check against the real active clinks.

The initial profile continues to admit seven direct literals and reject
compounds. The mechanism already supports compound admission: for a sequence
of Integer literals, enable `seq`, `DJudgeSeq.last`, `DJudgeSeq.cons` and `intLit`,
with their semantic proof providers. Any disabled premise rule causes rejection
in `validateD`, `ratchetd` and `validate-one`. Historical corpus floors remain
separate from this rebuild profile.
