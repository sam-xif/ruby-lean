# Supported Ruby

The model covers a large part of core Ruby and declines the rest. Declining is a
defined outcome: `rubycore` exits with status 3 and prints the reason. It never
substitutes a guess.

The measure of coverage is CRuby's own `bootstraptest` suite: 1287 small
self-contained programs at the pinned release. `make conformance` runs all of
them under CRuby and under the model. At the recorded baseline
(`difftest/coverage-baseline.json`):

| Outcome | Programs |
|---|---|
| The model and CRuby agree | 1087 |
| The model declines | 194 |
| Not compared: CRuby itself rejects the program (deliberate syntax errors) | 6 |
| The model and CRuby disagree | 0 |

The build fails if a program disagrees, if fewer agree, or if more are declined.

## What runs

**Core language.** Literals; local, instance, class and global variables;
method calls with every kind of parameter (required, optional, `*rest`, keyword,
`**kwrest`, `&blk`, destructuring) and every form of keyword argument at the
call site; `if`, `unless`, `while`, `until`, `for`, `case`/`when`;
`begin`/`rescue`/`else`/`ensure`/`retry`; `return`, `break`, `next`, `redo`;
`defined?`; `alias` and `undef`; constant paths.

**Blocks, procs and lambdas.** Literal blocks and `yield`, `block_given?`,
`&blk` parameters, `&expr` and `&:sym` arguments, `proc`, `lambda`, `->`,
`Proc.new`, and non-local `next`/`break`/`return` with the differences between
procs and lambdas. `catch` and `throw`.

**The object model.** `class` and `module` bodies; `new` and `initialize`;
constants scoped by lexical nesting; `super` with and without arguments;
singleton methods and eigenclasses; `include`, `extend` and `prepend`;
`attr_reader`, `attr_writer`, `attr_accessor`; `method_missing`; `private`,
`protected`, `public`, `module_function` and `private_class_method`, enforced at
the call site. `Kernel` and `Comparable` sit in the real ancestor chain, so
`ancestors` prints what CRuby prints.

**Reflection.** `define_method`, `define_singleton_method`, the block forms of
`class_eval`, `module_eval`, `instance_eval` and `instance_exec`,
`alias_method`, `singleton_class`, `instance_variable_get`/`set`,
`const_get`/`const_set`, `remove_method`, `undef_method`, `Class.new`,
`Module.new`, `send`, `public_send`, `respond_to?`, `is_a?`. Definition and
constant callbacks (`method_added`, `inherited`, `const_added` and the rest).

**The core library.** `Integer`, `Float`, `Rational` and `Complex` arithmetic
with CRuby's exact formatting; `String` and `Symbol`; `Array` and `Hash`,
including mutation during iteration; `Range`; `Regexp` and `MatchData` for a
practical subset of patterns; `Enumerable` and `Comparable`; internal and
external `Enumerator`s; `Struct`; the standard exception hierarchy; seeded
`Random`; `dup`, `clone` and `freeze`.

**Libraries on `require`.** Partial models of `json`, `uri`, `forwardable` and
`pathname`, and a model of `sorbet-runtime`.

## What is declined

**Out of scope by design.**

* `eval` of a string, and the string forms of `instance_eval` and `class_eval`.
  The model has no parser.
* Threads, fibers as a public API, processes, signals, `ObjectSpace`, GC.
* Files, sockets and the rest of I/O beyond writing to standard output.
* `TracePoint`, `RubyVM`, `Binding` objects.

**Not modeled yet.** `Method` and `UnboundMethod` objects; `private_constant`;
refinements; pattern matching with `case`/`in`; regular
expression features outside the supported subset; most of the standard library.

**Declined to stay correct.** The model knows the name of every built-in method
of CRuby 4.0.5 (`Generated/CRubyNames.lean`). When a program calls a method that
CRuby defines and the model does not implement, the model declines. It does not
raise `NoMethodError`, which is what a model that simply lacked the method would
do, and which would be a wrong answer.

## Finding out about one program

```sh
bin/ruby-lean --compare prog.rb     # runs it, or prints why it was declined
ruby desugar/bin/coverage --full    # what blocks each unsupported bootstraptest program
```

After `make conformance`, `.make/conformance/cases.jsonl` has one record per
program with the verdict and, for a declined program, the reason.
