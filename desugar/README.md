# desugar/ — Ruby to the model's core language

Translates Ruby source into RubyCore, the small language the model runs, and
writes it as JSON. The model never parses Ruby; everything it runs comes through
here.

```sh
echo 'puts 1 + 2' | ruby bin/export-json    # Ruby on stdin, core JSON on stdout
ruby bin/desugar some_program.rb            # the core program, readably, and the rewrite rules that fired
```

It needs CRuby 4.0 (for the Prism parser) and nothing else. A program that uses
something the desugarer does not support is reported as such, with the reason,
and `export-json` exits with status 3.

## Testing the translation

A wrong translation would make the model run the wrong program, so the
translation is tested on its own, with CRuby alone. For each program `P`, the
harness prints `desugar(P)` back as Ruby and checks that CRuby behaves the same
on both, including the order in which side effects happen.

```sh
make desugar-test desugar-coverage    # from the repository root; what `make check` runs
ruby bin/run corpus/seeds --verbose   # one directory, printing each rendered core program
ruby bin/run --bug                    # inject a known-wrong rewrite and watch the tests catch it
ruby bin/coverage --full              # what blocks each unsupported bootstraptest program
```

`coverage-baseline.json` records how many of CRuby's `bootstraptest` programs
the desugarer supports. `bin/coverage` fails if the number falls;
`bin/coverage --save` records an improvement.

[How the model is tested](../docs/testing.md#the-desugarer) explains why the
test observes evaluation order and not only values.

## Files

| Path | Contents |
|---|---|
| `lib/desugar.rb` | Prism syntax tree to RubyCore, recording which rewrite rules fired |
| `lib/rubycore.rb` | The list of RubyCore node types (`HEADS`). `ruby-lean/RubyCore/Syntax.lean` mirrors it exactly |
| `lib/linearize.rb` | Moves `break`, `next` and `return` out of positions where Ruby cannot parse them |
| `lib/render.rb` | RubyCore back to Ruby source, for the round-trip test |
| `lib/export.rb` | The versioned JSON format the model reads |
| `lib/observe.rb` | Runs a program under CRuby and captures its output, result and exception |
| `lib/roundtrip.rb` | The round-trip check and the classification of a disagreement |
| `bin/harvest_bootstraptest` | Extracts test programs from a checkout of CRuby's `bootstraptest/` |
| `corpus/seeds/` | Hand-written test programs, including ones that observe evaluation order |

[Adding Ruby to the model](../docs/contributing.md#adding-ruby-to-the-model)
describes how to extend it.
