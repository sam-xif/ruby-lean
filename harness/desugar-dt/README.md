# desugar-dt — differential-testing harness for `desugar`

A runnable prototype of the desugar-first testing approach in
[`../../docs/semantics/06-desugaring-and-its-testing.md`](../../docs/semantics/06-desugaring-and-its-testing.md).
It builds trust in `desugar : Surface → RubyCore` **before** RubyCore has any semantics,
using CRuby as the sole oracle. Design decisions are recorded in
[`implementation-choices.md`](implementation-choices.md).

## The idea in one line

For a surface program `P`, check that `P` and `render_core(desugar(parse(P)))` produce the
**same observation under CRuby** — where the observation includes an **evaluation-order
trace** (stdout), not just the final value. No RubyCore interpreter is involved.

```
  P ──parse──▶ Prism AST ──desugar──▶ RubyCore ──render_core──▶ Ruby′
  obs⁺_CRuby(P)   ≟   obs⁺_CRuby(Ruby′)          (+ pure checks: is_core, normal-form)
```

## Layout

| Path | Role |
|------|------|
| `lib/rubycore.rb` | RubyCore node set (tagged S-expressions) + `is_core?`/`explain` |
| `lib/desugar.rb`  | `Prism AST → RubyCore`, with per-rule coverage tracking |
| `lib/linearize.rb`| hoist unconditional control-flow jumps out of operand position ([design](../../docs/semantics/linearization.md)) |
| `lib/render.rb`   | `RubyCore → Ruby` (over-parenthesized, re-parseable) |
| `lib/observe.rb`  | `obs⁺`: run under CRuby subprocess, capture (stdout, value, exc), normalize |
| `lib/roundtrip.rb`| the round-trip + `is_core` + normal-form checks + disagreement triage |
| `bin/run`         | driver over a corpus; agreement + coverage report |
| `bin/desugar`     | inspect one program: source, rules fired, rendered RubyCore, AST |
| `bin/coverage`    | fragment-coverage % + blocker histogram + ratchet |
| `bin/harvest_bootstraptest` | prong-1 corpus harvester from MRI `bootstraptest/` |
| `corpus/seeds/`   | hand-written self-contained seeds (incl. eval-order adversarial) |

## Usage

```sh
RUBY=$(brew --prefix ruby)/bin/ruby      # a modern CRuby with +PRISM

$RUBY bin/run                 # run all corpus programs
$RUBY bin/run --verbose       # also print the rendered RubyCore for each
$RUBY bin/run corpus/seeds    # run a specific dir or file
$RUBY bin/run --bug           # inject the naive &&/|| desugaring (demo, see below)
```

Exit status is non-zero if any program disagrees or errors.

## Why the evaluation-order trace matters (built-in demo)

`&&`/`||` must evaluate their left operand **exactly once**. The naive desugaring
`a && b ⇒ if a then b else a` re-evaluates `a`. A value-only oracle misses this — the
*result* is unchanged — but the trace does not. `--bug` injects the naive form:

```
$ $RUBY bin/run --bug
[XX ] seeds/03_and_falsy_order.rb  [trace]
      stdout: "a=nil" vs "aa=nil"
[XX ] seeds/04_or_truthy_order.rb  [trace]
      stdout: "a=5" vs "aa=5"
```

The value is identical on both sides; only the stdout trace exposes the double evaluation.
This is the concrete payoff of augmenting `obs` with the trace (artifact 06 §2).

## Coverage & triage

- The driver reports **desugaring-rule coverage** (artifact 06 §5): which of
  `Desugar::RULES` fired across the corpus, and which are still uncovered.
- Disagreements are triaged into buckets (artifact 06 §6): `trace` (evaluation order /
  once-only broken), `value_exc` (meaning changed), `render` (`is_core`/printer bug),
  `obs_normalizer`. There is deliberately **no "model bug" bucket** — that's the point of
  testing desugar first.

## Growing the fragment

The plan for expanding what `desugar` handles — toward full (in-scope) bootstraptest
coverage, prioritized by measured blocker impact — is in
[`fragment-expansion-strategy.md`](fragment-expansion-strategy.md) (batches M1–M5).

## Modeled fragment (this slice)

Literals (`int`/`str`/`sym`/`true`/`false`/`nil`), `self`, local read/write, `send`
(operators + blocks with simple positional params), `def` (simple positional params),
arrays, `if`/`while`, sequencing — plus the desugarings `unless→if`, `until→while`,
`&&`/`||`/`and`/`or → if` (single-evaluation), `x ||= / &&= e`, and string interpolation.
Anything else makes `desugar` raise `Unsupported`, and the driver marks the program
**out-of-fragment** (skipped with a reason) rather than failing. Grow the fragment by
adding rules; don't handle all of Ruby at once (implementation-choices.md C3).

## Corpus prongs (artifact 06 §4)

1. **bootstraptest** — `bin/harvest_bootstraptest /path/to/ruby/bootstraptest` harvests
   self-contained programs (+ expected values for an `obs` cross-check). See the script
   header for a sparse-clone recipe.
2. **Superion-style fuzzing** — not yet implemented; design/feasibility in
   [`prong2-design.md`](prong2-design.md). The driver already consumes any `.rb` under
   `corpus/`, so a generator drops in without code changes.
3. **AI-agent targeted examples** — the hand-written adversarial seeds are the seed of
   this prong; extend per the obligation list in artifact 06 §4.
