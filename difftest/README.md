# difftest — differential test engine for Ruby

A multi-tier engine that generates Ruby test programs, runs each under **CRuby
(the control)** and an arbitrary **system under test (SUT)** — eventually the
in-Lean semantics — and reports where they differ. Methodology per
[`../docs/semantics/05-differential-testing.md`](../docs/semantics/05-differential-testing.md);
tier-1 design realizes [`../harness/desugar-dt/prong2-design.md`](../harness/desugar-dt/prong2-design.md).
Picking this up fresh? Read [`HANDOFF.md`](HANDOFF.md).

## Setup

```sh
cd difftest
uv sync                 # Python 3.12+, hypothesis, anthropic
# oracle: Homebrew CRuby (auto-resolved); override with DIFFTEST_RUBY=/path/to/ruby
# tier 3 only: export ANTHROPIC_API_KEY=...
```

## Usage

```sh
uv run python -m difftest run --tier 1 -n 200 --sut identity --seed 42
uv run python -m difftest run --tier 1 -n 300 --sut desugar --inject-bug   # detection self-test
uv run python -m difftest run --tier 0 --sut desugar                       # bootstraptest corpus (all; -n samples)
uv run python -m difftest run --tier 1.5 -n 300 --sut desugar               # eval-order probes (recv/arg sequencing)
uv run python -m difftest run --mix tier1=0.9,tier0=0.05,tier3=0.05 -n 200 --sut desugar
uv run python -m difftest gen3 --category eval-order -n 5                  # costs API tokens
uv run python -m difftest replay corpus/tier3 --sut identity
uv run pytest
```

Reports land in `reports/<timestamp>-<label>/` (gitignored): `cases.jsonl`
(one record per case: source, both observations, verdict, reason, timings),
`summary.json`, and a human `report.md`. Exit code 1 iff any DISAGREE.

## The tiers

| Tier | Source | Status |
|---|---|---|
| 0 | conformance corpora — first source: MRI's `bootstraptest`, harvested by the desugar harness (`difftest/sources.py`) | built |
| 1 | Hypothesis AST fuzzing (`difftest/tiers/tier1/`) | built |
| 2 | mutation of scraped real-world Ruby | **stub** — future generator slot |
| 3 | Anthropic-API-generated adversarial programs (`difftest/tiers/tier3/`) | built |
| 4 | Sorbet-annotated corpus (`corpus/sorbet/`) — see [Sorbet](#sorbet-tier-4) | built |

**Tier 0** replays MRI's own `bootstraptest` suite — ~1300 self-contained
single-file programs harvested by `../harness/desugar-dt/bin/harvest_bootstraptest`
(the corpus is not vendored; the source errors with the harvest recipe when it
is missing). No pre-filter: the run-time control gate excludes unusable cases
with reasons. This is the quick-initial-confidence corpus a new SUT meets first.

**Tier 1** generates a *surface* AST under scope-aware strategies (an
environment of bound locals/methods/**classes**/**modules**/**instances**/
**procs** threads through generation, so names resolve and dispatch fires). The
vocabulary covers scalars/arrays/hashes/**ranges**, control flow, first-order
methods, **method parameters in full variety** (required, **optional defaults**,
**keyword** `k:`/`k: v`, `*rest`, `**kwrest`, **`...` forwarding**, **destructuring**
`|(a, b)|`, with call sites generated compatibly), **control flow** (`if`, `while`,
`times`, **`for`** (scope-leaking index), **do-while**, **`redo`**, bounded),
the **object model** (`class`/ivars, inheritance `< Super` + `super`,
`module` + `include`/`prepend`, `def self.m`, **`class << self`**, `C.new`,
instance/class-method sends, **`method_missing`**), **constant paths** (`A::B`
read + assign), **metaprogramming as heap mutation** (`send`/`public_send`,
`respond_to?`, `instance_variable_get`/`set`, `attr_accessor`, `define_method`/
`define_singleton_method`, `alias`/`alias_method`, `undef`, class reopening),
**writer-calls + multiple assignment** (`a[i] = v`, `a[i] ||= v`, `obj.attr = v`,
`a, *b = …`), and **rich exceptions** (typed/multiple `rescue`, `else`, `ensure`,
bounded **`retry`**, `raise Klass, msg`). Termination is by construction (bounded
loops/collections, pure constructors, a strict class/method DAG, monotonic-guard
`redo`/`retry` gadgets); see implementation-notes N12–N13, N15–N22. The campaign is
a Hypothesis property asserting agreement — any disagreement is **automatically
shrunk** and the minimal reproducer saved to `corpus/regressions/`.

**Tier 3** prompts Claude (default `claude-opus-4-8`, structured JSON output)
for adversarial programs per semantic category (dispatch, blocks/jumps,
eval-order, exceptions, namespaces, kwargs, metaprogramming — see
`tiers/tier3/prompts.py`). Every program passes a validation gate (parses,
terminates, deterministic under a double run) before entering
`corpus/tier3/<category>/NNN.rb` with a `.json` sidecar; rejects are logged
with reasons. The corpus is committed and replayed for free thereafter.

**Mixed campaigns** (`run --mix tier1=0.9,tier0=0.05,tier3=0.05`) sample each
case from a weighted arm: fresh generation from a **generative arm** (`tier1`, or
`tier1.5` for eval-order probes — e.g. `--mix tier1.5=0.9,tier0=0.1`) or a
persisted **corpus arm** (`tier0`/`tier3`). The
campaign remains a single Hypothesis property, so tier-1 disagreements still
shrink to minimal reproducers; a disagreeing corpus draw is reported by its
corpus id instead (it is already small and persisted). Non-critical
implementation choices are recorded in
[`implementation-notes.md`](implementation-notes.md).

## What is compared (`Observation`)

`obs = (stdout, result_repr, exception[class, message])`, normalized on both
sides: `0x…` object addresses are rewritten to allocation-order indices,
`RUBY_HASH_SEED=0` is pinned. Identical deterministic *errors* count as
agreement. Programs that don't parse, time out, or are nondeterministic under
the control are excluded as `CONTROL_INVALID` — always with a reason, never
silently.

Known v1 wrapper limits (see `difftest/control.py`): writes to the `STDOUT`
constant bypass capture; heap projection is deferred.

## The SUT interface (how the Lean model plugs in)

```python
class SystemUnderTest(Protocol):
    name: str
    def run(self, source: str) -> Observation | Unsupported: ...
```

`Unsupported(reason)` is the fragment gate — a SUT that models a subset
declares out-of-fragment programs instead of failing on them. Built-in SUTs:

- `stub` — supports nothing; the original placeholder.
- `identity` — CRuby again; pipeline smoke test (must be 100% AGREE).
- `desugar` — adapter over `../harness/desugar-dt/` (desugar → render → CRuby);
  with `--inject-bug` its known-buggy `&&`/`||` desugar produces real
  disagreements, which is the engine's end-to-end detection self-test.
- `lean` — **the Lean model** (`../lean/`): desugar → RubyCore JSON →
  `rubycore` binary (build it first: `cd ../lean && lake build`). Composes
  two fragment gates (desugar's and the model's L0); binary exit 3 =
  Unsupported, exit 1 = model bug (surfaced as `MODEL-BUG:` reasons, never
  silently).

## Sorbet (tier 4)

Scaffolding for the Sorbet-soundness work
([`../docs/semantics/types-and-preservation.md`](../docs/semantics/types-and-preservation.md),
[`type-judgments.md`](../docs/semantics/type-judgments.md)). Setup:

```sh
gem install sorbet sorbet-runtime      # srb lands in $(gem environment gemdir)/bin
export DIFFTEST_SRB=/path/to/srb       # only if it is not on PATH
```

**The corpus** (`corpus/sorbet/`, 18 programs) is organized by *which part of Sorbet's
design* a program probes — `sig-basic`, `narrowing`, `assertions`, `untyped-boundary`,
`escape-hatches`, `structs-enums`, `generics` — because the object of study is the type
system, not the language. Each program's sidecar declares the expected outcome of **both**
halves (`static_expect`, `runtime_expect`), and those declarations are enforced, not
decorative.

**Two probes, neither needing Lean:**

```sh
uv run python -m difftest sorbet check             # static oracle vs actual behavior
uv run python -m difftest run --tier 4 --sut sig-strip   # the gradual-guarantee probe
```

`sorbet check` runs `srb tc` and CRuby over each program and reports the **two-by-two** of
static verdict against runtime outcome. `srb` is an oracle, not truth — Sorbet is unsound
by design, so acceptance is not a safety claim. The informative cells are off-diagonal:
`unsoundness-witness` (srb accepted a program that reaches an uncaught
NoMethodError/ArgumentError/TypeError — type-stuck in the sense of
`lean/RubyCore/Proof/TypeSafety.lean`'s `typeErrorFamily`) and `conservative-rejection`
(srb rejected a program that runs fine — the DRuby false-positive family). Current
standing: **4 witnesses, 2 conservative rejections, 0 declaration mismatches**. Exit 1 on
a declaration mismatch only; witnesses are findings, not failures.

`--sut sig-strip` is the **gradual guarantee** as a metamorphic relation: the control runs
the annotated program, the SUT runs the sig-stripped one (`ruby/sig_strip.rb`, a Prism
transform), and changing only annotation *precision* must not change behavior except by
trapping more errors. The licensed weakening is established by a third run of the
annotated program with enforcement neutralized, which *attributes* any difference to
runtime checking — necessary because a program can rescue its own sig violation, leaving
no exception to key off (implementation-notes N30). Current standing: **10 agree, 5
licensed weakenings (`agree_weakened`), 3 gated, 0 violations**.

**Known limits, stated rather than hidden:**

- The two-by-two sees only *errors*. Quiet holes — `.checked(:never)`, the unchecked
  `T::Struct` getter — let a wrong-typed value through with no error and land in
  `accepted-and-safe`. Catching those needs conformance against a *declared* discipline,
  i.e. the Lean typing layer (§5 of `../type-safety-by-reachability.md`).
- sig-strip **gates** structural constructs (`T::Struct`, `T::Enum`, `T.absurd`) rather
  than mangling them: removing those yields a different program, not a less precise one.
- The Lean SUT false-disagrees on all of tier 4 (`NameError: uninitialized constant T`)
  because the model's `require` returns true for a library it does not have. See
  implementation-notes **N34** — do not add the `sorbet` arm to a mixed campaign against
  `--sut lean` until that is fixed.

## Deferred (deliberately)

Tier 0/2 generators; heap projection in `obs`; three-way triangulation
(TruffleRuby/JRuby); coverage-guided generation steering; Batches API bulk
tier-3 generation; parallel oracle execution.
