# Prove a program type-safe

This guide takes a Ruby program with Sorbet signatures and establishes that it
can never raise a `NoMethodError`, `ArgumentError` or `TypeError`. You write no
Lean. You run one command, and a theorem that is already proved does the rest.

## 1. Write the program with signatures

The checker reads Sorbet's `sig` annotations. Start the file with
`# typed: true` and give every method a signature:

```ruby
# typed: true
require "sorbet-runtime"

class Counter
  extend T::Sig

  sig { params(start: Integer).void }
  def initialize(start)
    @count = start
  end

  sig { params(by: Integer).returns(Integer) }
  def bump(by)
    @count = @count + by
    @count
  end
end

c = Counter.new(10)
c.bump(5)
```

`require "sorbet-runtime"` is what makes `T::Sig` exist when the program runs,
under CRuby and on the model alike (`bin/ruby-lean --compare counter.rb` prints
`=> 15`). The checker does not need it.

## 2. Check it

```console
$ make run          # once, to build the tools
$ bin/ruby-lean-check counter.rb
ACCEPTED  counter.rb
  validateD accepted this program. By validateD_safe_run, running it on the
  model never ends in an uncaught NoMethodError, ArgumentError or TypeError.
```

The exit status is 0 for `ACCEPTED` and 1 for `NOT ACCEPTED`.

## 3. What `ACCEPTED` means

`ACCEPTED` means the Lean function `validateD` returned `true` for your program.
The theorem that gives that meaning is in
`books/Books/TypeSoundness/Soundness.lean`:

```lean
theorem validateD_safe_run {p : Checker.Expr} {d : Deriv}
    (h : validateD p d = true) (hb : bootOkB = true) (fuel : Nat) :
    Semantics.typeStuck (Semantics.run fuel (toRuby p)) = false
```

Read it as: if `validateD` accepts program `p`, then running `p` on the model,
from the booted core library, for any number of steps `fuel`, never ends in an
uncaught `NoMethodError`, `ArgumentError` or `TypeError`.

Three things to notice.

* **The hypothesis is the function's output.** The theorem is about the code
  that ran when you typed the command, not about a specification that the code
  is separately claimed to implement.
* **`d` is a hint.** `d` is a typing derivation that an ordinary Ruby script
  proposes. The theorem holds for every `d`, so a wrong derivation can only make
  `validateD` return `false`.
* **`bootOkB = true`** says that the machine the core library boots into
  satisfies the proof's invariant. It is a closed boolean and the build
  evaluates it.

The guarantee is about those three exception classes. It does not say the
program terminates, and it does not rule out other exceptions such as
`ZeroDivisionError`. [What is proved](../proofs/type-soundness.md) has the
details, and [What you have to trust](../proofs/trust.md) lists what stands
between this theorem and a claim about CRuby.

## 4. When the answer is `NOT ACCEPTED`

Five stages run in order and the first one that declines is reported.

| Stage | It declines when | What to do |
|---|---|---|
| `sorbet` | Sorbet reports a type error | Fix the error. Sorbet's message is printed |
| `strip` | The annotations cannot be removed | Report it; this should not happen for valid Ruby |
| `desugar` | The program uses Ruby the desugarer does not support | See [Supported Ruby](../semantics/supported-ruby.md) |
| `derivation` | No typing rule covers some construct | Rewrite that construct, or [add a rule](../contributing.md#adding-a-typing-rule) |
| `checker` | `validateD` returned `false` | The proposed derivation was wrong or incomplete |

For example:

```console
$ bin/ruby-lean-check lambdas.rb
NOT ACCEPTED  lambdas.rb
  stage:  derivation -- The program is outside the typed fragment: no typing rule covers it yet.
  reason: closure-valued call results are outside the fragment
```

Only the last stage is trusted. Sorbet, the stripper, the desugarer and the
derivation script can each be wrong, and the worst a mistake in any of them can
do is turn an `ACCEPTED` into a `NOT ACCEPTED`.

`NOT ACCEPTED` does not mean the program is unsafe. It means this checker could
not show that it is safe.

## What the checker covers

The typed fragment is smaller than the model. It currently covers:

* integer, float, string, symbol, boolean, `nil` and regexp literals; local
  variables; sequences; `if` and `while`
* arithmetic, comparison and the other built-in operators on those types
* narrowing a nilable or union type with `nil?`, `is_a?`, `===`, truthiness and
  `&&`
* Array and Hash literals
* top-level methods with required, optional, rest and keyword parameters, and
  recursion
* classes, subclasses and modules; `initialize`; instance variables; instance
  and singleton methods; `super` in `initialize`
* blocks passed to `each` and `map`, and methods that `yield` once

Not yet covered: lambdas passed as arguments or returned, blocks with more than
one parameter, `select`/`inject`/`sort_by` blocks, `include`/`extend`/`prepend`,
`method_missing`, explicit `return`, and `T.untyped`.

`books/corpus/` holds 267 small typed programs, and `make soundness` reports
which of them the checker accepts and why it declines the others. Reading a few
that are close to your program is the quickest way to see what is accepted.

## More output

```sh
bin/ruby-lean-check --json counter.rb        # the verdict and each stage, as JSON
bin/ruby-lean-check --keep out/ counter.rb   # keep the stripped program, the
                                             # signatures, the core JSON and the derivation
```

The [playground](../playground.md) runs the same five stages in a browser and
lets you edit the program and the derivation and check again.
