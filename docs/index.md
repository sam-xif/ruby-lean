# ruby-lean

`ruby-lean` is a model of the Ruby language written in Lean 4. The model is a
program: it runs Ruby, and its behavior is checked against CRuby on every build.
It is also a mathematical object, so you can prove things about what a Ruby
program does.

## What you can do with it

| You want to | Read |
|---|---|
| Run a Ruby program on the model and compare it with CRuby | [Run a program](guides/run-a-program.md) |
| Show that a Sorbet-annotated program can never raise a `NoMethodError`, `ArgumentError` or `TypeError` | [Prove a program type-safe](guides/prove-type-safety.md) |
| Prove what a program computes, for every input | [Prove a program correct](guides/prove-a-program.md) |
| Understand what the model says Ruby means | [The semantics](semantics/index.md) |
| See exactly what has been proved and what it rests on | [What is proved](proofs/index.md) |

Start with [Getting started](getting-started.md) to install the tools and build.

## A two-minute example

A Ruby program, with Sorbet signatures:

```ruby
# typed: true
require "sorbet-runtime"

class Point
  extend T::Sig

  sig { params(x: Integer, y: Integer).void }
  def initialize(x, y)
    @x = x
    @y = y
  end

  sig { returns(Integer) }
  def x
    @x
  end
end

Point.new(1, 2).x
```

Run it on the model:

```console
$ bin/ruby-lean point.rb
=> 1
```

Ask whether it can raise a type error:

```console
$ bin/ruby-lean-check point.rb
ACCEPTED  point.rb
  validateD accepted this program. By validateD_safe_run, running it on the
  model never ends in an uncaught NoMethodError, ArgumentError or TypeError.
```

`ACCEPTED` is the output of a Lean function, `validateD`. A Lean theorem,
[`validateD_safe_run`](proofs/type-soundness.md), says that whenever that
function returns `true` the program is safe in the sense printed. The theorem is
proved once, for every program; checking your program is then a function call.

## How the pieces fit

```
                 desugar/                 ruby-lean/RubyCore/
  Ruby source ──────────────▶ core JSON ──────────────────────▶ output, value, exception
                                  │              ▲
                                  │              │ proofs are about this
                                  ▼              │
                       the type checker       books/
                       accepts or declines    theorems
```

* **The model** (`ruby-lean/RubyCore/`) is a small-step abstract machine. One
  function, `stepFn`, takes a machine state to the next one.
* **The desugarer** (`desugar/`) turns Ruby source into the small core language
  the model runs. The model never parses Ruby.
* **The books** (`books/`) hold every proof: facts about the model, proofs
  about individual Ruby programs, and the type-soundness book.
* **The checker** (`books/Books/TypeSoundness/Checker/`) is a type checker for
  a fragment of Sorbet-annotated Ruby, and is part of the type-soundness book.
  It imports nothing from the model; the proof around it is where they meet.
* **The tests** (`difftest/`) run the model and CRuby side by side on thousands
  of programs and fail on any difference.

## What the results mean, and what they do not

Every theorem here is about the model. The model is tested against CRuby, and
that testing is thorough, but it is testing: it does not prove that the model and
CRuby agree on every program. [What you have to trust](proofs/trust.md) lists
each assumption between a theorem and a claim about real Ruby.

The model does not cover all of Ruby, and the checker covers less than the
model. When either meets something it does not support it says so and stops. It
does not guess. [Supported Ruby](semantics/supported-ruby.md) lists what is in
and what is out.
