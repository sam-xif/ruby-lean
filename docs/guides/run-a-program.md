# Run a program

`bin/ruby-lean` runs a Ruby program on the model. Build it first with
`make run`.

```console
$ cat sum.rb
total = [1, 2, 3].map { |x| x * 2 }.sum
puts total
total

$ bin/ruby-lean sum.rb
12
=> 12
```

The program's output comes first. The last line is the value of the program's
final expression, as `inspect` would print it. A program can also be piped in:
`echo 'puts 1 + 2' | bin/ruby-lean`.

An uncaught exception is a normal outcome of a run, and is reported with its
class and message:

```console
$ echo '1 + nil' | bin/ruby-lean
uncaught TypeError: nil can't be coerced into Integer
```

## Compare with CRuby

`--compare` runs the same program under CRuby and compares what was printed and
how the run ended:

```console
$ bin/ruby-lean --compare sum.rb
12
=> 12
AGREE  the model and CRuby print the same and end the same way
```

If this ever prints `DIFFER` for a program the model accepts, that is a bug in
the model; please report it. The [differential tests](../testing.md) make the
same comparison, more precisely, over thousands of programs.

## When the model declines a program

The model does not implement all of Ruby. When a program uses something it does
not cover, the run stops with exit status 3 and the reason:

```console
$ echo 'eval("1 + 2")' | bin/ruby-lean
ruby-lean: the desugarer does not support this program:
  eval of string (out of scope, Semantics 00 §6)
```

The model declines; it never guesses. A feature that CRuby has and the model
lacks produces this message, not a wrong answer.
[Supported Ruby](../semantics/supported-ruby.md) lists what is covered.

## Options

| Option | Effect |
|---|---|
| `--compare` | Also run under CRuby and compare |
| `--json` | Print the raw observation: `stdout`, `result_repr`, `exception` |
| `--fuel N` | Stop after `N` machine steps. The default is 5,000,000 |
| `--steps` | Print how many machine steps the program takes |
| `--trace [N]` | Print the first `N` machine states as JSON, one per step |
| `--trace-from N`, `--trace-at TEXT` | Start the trace at step `N`, or at the first step whose control contains `TEXT` |
| `--fragment` | Say whether the program is in the typed fragment, without running it |
| `--sigs` | Print the Sorbet signatures the program declares, without running it |

## Exit status

| Status | Meaning |
|---|---|
| 0 | The program ran. It may have ended in an uncaught exception |
| 1 | With `--compare`: the model and CRuby differ. Otherwise: an internal error |
| 2 | The tools are not built |
| 3 | The program uses Ruby that the desugarer or the model does not support |

## Watching it step

The [playground](../playground.md) shows a run one machine transition at a
time, with the control state, the frames and their locals, the continuation
stack and the output so far.

## The pieces, by hand

`bin/ruby-lean` is two commands joined by a pipe:

```sh
ruby desugar/bin/export-json prog.rb | ruby-lean/.lake/build/bin/rubycore
```

`export-json` prints the program in the model's core language as JSON, and
`rubycore` reads that and prints the observation. `ruby desugar/bin/desugar
prog.rb` shows the core program in readable form, with the rewrite rules that
produced it.
