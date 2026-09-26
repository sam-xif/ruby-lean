# desugar/ — Ruby to RubyCore

Translates Ruby source into RubyCore, the smaller language the Lean model runs,
and outputs it as JSON. The model never parses Ruby itself; everything it runs
comes through here.

This directory is also the test harness for that translation. For each program
`P`, it renders `desugar(P)` back into Ruby and checks that CRuby produces the
same output for both, including the order in which side effects happen. That
means the translation is tested with CRuby alone, without depending on the model.

## Usage

Needs a recent CRuby with Prism (`brew install ruby`).

```sh
RUBY=$(brew --prefix ruby)/bin/ruby

echo 'puts 1 + 2' | $RUBY bin/export-json   # Ruby on stdin -> RubyCore JSON (what the model reads)
$RUBY bin/desugar some_program.rb           # show the rules fired and the rendered RubyCore
$RUBY bin/run                               # round-trip every corpus program; non-zero exit on disagreement
$RUBY bin/run corpus/seeds --verbose        # one directory, printing the rendered RubyCore
$RUBY bin/coverage                          # how much of bootstraptest is supported, and what blocks the rest
```

## Files

| Path | What it does |
|---|---|
| `lib/desugar.rb` | Prism AST → RubyCore, recording which rewrite rules fired |
| `lib/rubycore.rb` | The list of RubyCore node types (`HEADS`). `ruby-lean/RubyCore/Syntax.lean` mirrors it exactly |
| `lib/linearize.rb` | Moves `break`/`next`/`return` out of positions where Ruby can't parse them |
| `lib/render.rb` | RubyCore → Ruby source, for the round-trip |
| `lib/export.rb` | The versioned JSON format the Lean side reads (`Export::VERSION`) |
| `lib/observe.rb` | Runs a program under CRuby and captures stdout, result and exception |
| `lib/roundtrip.rb` | The round-trip check and the triage of disagreements |
| `bin/harvest_bootstraptest` | Extracts test programs from a checkout of MRI's `bootstraptest/` |
| `corpus/seeds/` | Hand-written test programs, including ones that check evaluation order |
| `implementation-choices.md` | Numbered design decisions (C1, C2, …) cited from the code |

Programs that use something `desugar` doesn't support are reported as out of
fragment with a reason, not as failures. Currently 1227 of 1299 parseable
bootstraptest programs are supported (`coverage-baseline.json`).

## More

- [The round-trip method](../docs/front-end/method.md): why this testing approach
  works and what it checks. Code comments cite it as *"artifact 06 §N"*.
- [Growing the fragment](../docs/front-end/growing-the-fragment.md): how to add
  support for a new Ruby feature.
- [Linearization](../docs/front-end/linearization.md): the one rewrite that needs
  control-flow reasoning.
