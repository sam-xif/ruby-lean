# Rebuilding the clink registry

The active registry admits literals, locals, sequences, primitive sends, branches,
bare names, Array/Hash literals, ordinary definitions/calls, scoped recursion, fresh class declarations/constants/member defs/default and initialized construction/instance calls/ivar reads and their companions (54/99 rules). `intLit` remains the
non-vacuity anchor.

From `books/`, run:

```sh
./scripts/run_typed_ratchet.sh                  # active soundness + corpus progress
./scripts/run_typed_ratchet.sh --clink-rebuild  # proofs/controls only
```

The default gate checks isolation, profile/registration refusal controls,
generated-checker freshness, active semantic proofs and the actual `validateD`
runner-safety theorem. The axiom audit rejects `sorryAx` and project axioms.
It builds fresh corpus outputs, retains Sorbet/upstream/negative controls and
CRuby agreement, and reports **RATCHET GREEN** when those checks pass. Missing
coverage from disabled rules is work remaining, not a soundness failure.

`Books/TypeSoundness/Report/Active.lean` counts only certified enabled clinks and corpus
programs the production `validateD` accepts. It lists disabled dependencies from
the verified checker trace, including companion and body premises. Negative
controls are reported separately and never count as climbed through rejection.
Filtered runs use fresh output by default so cached rungs cannot inflate counts.

`--clink-rebuild` runs the proof/controls subset without corpus progress and
reports **CLINK REBUILD CHECKS PASS**. The original complete-registry, coverage,
corpus-floor and worked-theorem audit (`--full-corpus`) is in `books/Unrebuilt/`:
its script, its report executable and the worked theorems it reads have not been
rebuilt against the current model. None of those historical floors is reset for
the active gate.

## Climbing the ratchet

Climbing a rule includes adding its exact constructor suffix to `clinkProfile`
so `clinkEnabled rule = true`, importing its semantic proof provider, and passing
the active registry/Bridge gate with the required proof dependencies. Enable
all companion and body rules used by the desired derivation as well. The ascent
commit carries this admission together with the proof and positive/negative
controls. A positive corpus rung is climbed when the production `validateD`
accepts it under that committed profile. A proved but gated rule remains
unclimbed in the active ratchet; a temporary test profile does not change that.

## Re-enable a rule

1. Add its exact constructor suffix to `Checker/ClinkPolicy.lean`'s `clinkProfile` list, such
   as `var`, `DJudgeAll.cons` or `DFlow.call`.
2. Add its proof-provider import to `ActiveProofs.lean`. The former complete
   import set is retained in `books/Unrebuilt/TypeSoundness/Registry/FullProofs.lean` as a
   reference.
3. Repair the selected rule and its necessary dependencies. Enable every companion
   and body rule needed by the desired derivation, then rerun the rebuild command.
   Sequence and its two companions are supplied together by
   `Books.TypeSoundness.Rules.Expr.Sequence`; importing that provider does not enable its rules.
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
`FullProofs` (now `books/Unrebuilt/TypeSoundness/Registry/FullProofs.lean`) imported by
`ActiveProofs.lean`. Restoring complete
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

The shared policy lives in `Checker/ClinkPolicy.lean`, preserving isolation;
`Books/TypeSoundness/Registry/Policy.lean` exports those same definitions. `validateDWith` permits
explicit policies in checker controls; the production `validateD` always uses
the registry's policy.

`Books/TypeSoundness/Registry/AuditBridge.lean` derives certification for all seventeen indexed
judgments from their constructor metadata. Each enabled case applies its actual
active clink to the certified premises. Each gated case is impossible because
its trace contains a disabled rule. The generated proofs are kernel checked.
`Books/TypeSoundness/Soundness.lean` then proves the original `validateD_safe`,
`validateD_safe_boot` and `validateD_safe_run` statements, including:

```lean
validateD p d = true → bootOkB = true →
  Semantics.typeStuck (Semantics.run fuel (toRuby p)) = false
```

Only active semantic proofs and their transitive dependencies are imported.
`Soundness/Full.lean` retains optional completeness helpers for the unrestricted
raw authoring judgments. The former literal-specific validator/evidence/bridge
modules have been removed.

### Updating the checker

`Checker/Check/Raw.lean` and its body/cache helper modules are the authored
computational implementation. The checker modules under `Checker/Audit/` are
generated projections using constructor-indexed judgments and explicit trace
metadata. After changing an authored checker source, run:

```sh
python3 ../ruby-lean/scripts/generate_audited_checker.py
```

Both gate modes run `--check` to reject stale generated sources. Judgment,
erasure and certification declarations are generated by Lean from the actual
constructor types. A generation error can fail compilation or cost acceptance;
the safety proof still must check against the real active clinks.

The initial profile admitted seven direct literals. The active profile now admits
sequences as well: for a sequence
of Integer literals, enable `seq`, `DJudgeSeq.last`, `DJudgeSeq.cons` and `intLit`,
with their semantic proof providers. Any disabled premise rule causes rejection
in `validateD`, `ratchetd` and `validate-one`. Historical corpus floors remain
separate from this rebuild profile.

The generic path was also checked with temporary sequence-enabled profiles.
With both companions enabled, one- and two-element sequences pass the actual
validator and runner-safety bridge. Disabling `DJudgeSeq.cons` preserves the
one-element accept and rejects the two-element program. The checked-in profile
now enables both sequence companions.
