# The Sorbet corpus (tier 4)

Hand-written Sorbet-annotated programs, one specific probe each. The taxonomy is by
**which part of Sorbet's design** a program exercises (§A of
[`../../../docs/semantics/types-and-preservation.md`](../../../docs/semantics/types-and-preservation.md)),
not by Ruby construct — the object of study is the type system.

| Category | Probes |
|---|---|
| `sig-basic` | plain sigs; both halves quiet, or both firing on one defect (§A.5) |
| `narrowing` | flow-sensitive/occurrence typing and its documented limits (§A.2) |
| `assertions` | the `T.let`/`T.cast`/`T.must`/`T.unsafe` static-vs-runtime table (§A.3) |
| `untyped-boundary` | `T.untyped`, the no-sig boundary, and blame (§A.5, §B.5) |
| `escape-hatches` | the unsoundness catalogue: holes Sorbet accepts by design (§A.3) |
| `structs-enums` | `T::Struct` / `T::Enum`, incl. the checked/unchecked asymmetry (§A.1) |
| `generics` | runtime-erased generics — statically checked, no runtime backstop (§A.6) |

## The sidecar contract

Every `NNN.rb` has an `NNN.json` declaring what *both halves* of Sorbet do with it:

```json
{
  "tier": 4,
  "category": "untyped-boundary",
  "description": "…what this program probes and why it matters…",
  "sigil": "true",
  "static_expect": "clean",          // clean | errors                  (srb tc)
  "runtime_expect": "ruby_error",    // value | sorbet_error | ruby_error (CRuby)
  "doc_ref": "types-and-preservation.md A.5"
}
```

`sorbet_error` means sorbet-runtime's enforcement fired (the "blame" outcome);
`ruby_error` means a genuine Ruby-level error escaped, i.e. Sorbet provided no backstop.
The declarations are **enforced** by `difftest sorbet check`, which exits 1 on any
mismatch — so a Sorbet version bump that moves a verdict fails loudly instead of quietly
invalidating the taxonomy.

## What belongs here

Programs where the properties under test are **expected to hold**: the corpus carries a
0-violation ratchet for the gradual-guarantee probe, matching the discipline of the rest
of the engine. A program known to *violate* a probed property lives in the test suite as
a detection self-test instead (see implementation-notes N33), so that "0 violations"
keeps meaning something.

Off-diagonal *findings* — Sorbet accepting a program that reaches a type-stuck outcome —
do belong here. They are the point: `sorbet check` collects them as the unsoundness
catalogue, and they are findings, not failures.

## Adding a program

1. Write it self-contained, deterministic, terminating, `require "sorbet-runtime"` at the
   top, `# typed:` sigil on line 1.
2. Write the sidecar with your *predicted* outcomes.
3. Run `uv run python -m difftest sorbet check`. If the prediction was wrong, that is the
   interesting part — work out which of you is confused before editing either file.
4. Run `uv run python -m difftest run --tier 4 --sut sig-strip`; a `disagree` means you
   found a gradual-guarantee violation, which does not belong in this corpus (N33).
