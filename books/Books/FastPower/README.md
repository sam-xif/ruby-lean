# `Books/FastPower/` — a Ruby program proved correct

A *program book* is a Ruby program together with a statement of what it computes
and a Lean proof of that statement against the model's `stepFn`. This is the
worked example. [Prove a program correct](../../../docs/guides/prove-a-program.md)
is the guide to writing another one, starting from `bin/new-book`.

```bash
make books          # from the repository root; or `lake build` in books/
```

## What a book proves

The program ([`fast_power.rb`](fast_power.rb)) is exponentiation by
squaring, done by a small stateful object:

```ruby
class Power
  def initialize(base)
    @base = base
    @steps = 0
  end

  def steps
    @steps
  end

  def raise_to(exponent)
    result = 1
    square = @base
    left = exponent
    while left > 0
      if left % 2 == 1
        result = result * square
      end
      square = square * square
      left = left / 2
      @steps = @steps + 1
    end
    result
  end
end

power = Power.new(3)
answer = power.raise_to(13)
puts answer
[answer, power.steps]
```

With the two literals replaced by arbitrary integers `b` and `n`:

```lean
theorem fast_power_correct (b n : Int) :
    ∃ v m', Runs (program b n) v m' ∧
      m'.out = toString (b ^ n.toNat) ++ "\n" ∧
      IsArray m'.heap v [.int (b ^ n.toNat), .int (bitLength n.toNat)]
```

For every base and exponent, the program, run the way `rubycore` runs it
(prelude booted first), terminates normally, prints `b ** n` on a line of its
own, and has the value `[b ** n, s]`, where `s` is the number of loop iterations
and equals the bit length of `n`. A negative exponent behaves as `0`.
`fast_power_run` restates it per fuel: the run is either unfinished or has
returned exactly that. It never raises, never leaves the modeled fragment and
never gets stuck.

That is the whole observation the differential tests compare (stdout, result,
exception), proved for all inputs. The proof depends on `propext`,
`Classical.choice` and `Quot.sound` only.

## How a proof works

The Lean kernel can evaluate `stepFn`, method dispatch included, on a machine
whose integer inputs are variables. A straight-line stretch of execution is
therefore proved by asking the kernel to run it:

```lean
theorem setup (b n : Int) :
    stepN 61 (start (program b n)) = some (loopHead b n 1 b n 0) := by kernel_rfl
```

That line covers booting the prelude, defining `Power`, `Power.new(b)` running
`initialize`, the call to `raise_to(n)` and its first three assignments, for all
`b` and `n`.

The kernel stops where the machine branches on a value that depends on a
variable, such as `left > 0`. Those are the only places a proof has to say
anything. For `FastPower` that comes to:

| Part | What it is | Size |
|---|---|---|
| States | The machine at the loop test as a function of `result`, `square`, `left`, `@steps`, and the two branch points inside an iteration | 3 definitions |
| Segments | The stretches between those states, each `by kernel_rfl` | 10 one-line proofs |
| Arithmetic | `result * square ^ left = b ^ n` is preserved; what `>`, `%`, `==`, `/` compute | about 30 lines, no Ruby in it |
| Loop | Strong induction on `left` joining the above | about 35 lines |

A state is not written out in full. `loopHead` takes everything the loop leaves
alone (the booted heap, class `Power`, the four frames) from the machine the
kernel computes, and spells out only what the loop changes.

## Writing a book

Each book is a directory under `Books/` holding the Ruby file, its exported
JSON, and three Lean files.

1. **`Program.lean`: the program as a term.** The exporter's AST with the
   inputs abstracted and the subterms the proof mentions given names.
   `Check.lean` has a `#guard` that decoding the JSON
   (`ruby desugar/bin/export-json < prog.rb > prog.json`) gives exactly that
   term.
2. **Look at a concrete run.** `#eval trace 400 (start (program 3 2))` prints
   every transition with the stack, frame-store size and heap size. This is
   where the frame and object numbers come from.
3. **Find the stop points.**
   `#kernel_steps 400 fun (b n : Int) => start (program b n)` runs the kernel
   on symbolic inputs and reports how far it got and what it could not decide.
4. **`Proof.lean`: states, segments, arithmetic, induction.** Define the states
   at the loop head and at each stop point and prove the segments between them
   with `kernel_rfl`. A wrong state or step count is rejected by the kernel.
   Resolve each stop with a lemma about the builtin's result.
5. **`Check.lean`: the JSON guard and the axiom audit.**

Two habits keep proofs fast. Establish arithmetic facts before any fact about a
machine is in context, because `omega` times out trying to read one. And prefer
`h ▸ …` or a helper lemma to `rw … at` on a hypothesis that mentions a machine.

### [`Books/Lib/`](../Lib/)

| File | Contents |
|---|---|
| `Exec.lean` | `stepN`, `Reaches`, `Returns` and their algebra; `kernel_rfl`; `#kernel_steps`, `#kernel_whnf` |
| `Boot.lean` | `start p`, the prelude-booted machine `rubycore` runs `p` on, with `boot_ok`; `Runs`; `IsArray` |
| `Trace.lean` | `trace` and `showState`, for looking at concrete runs |

## What is proved and what is tested

| Link | Status |
|---|---|
| `program b n`, booted and run as `rubycore` does, prints and returns `b ^ n` | Proved, all `b`, `n` |
| `fast_power.rb` desugars to `program 3 13` | Tested at build time (`#guard`), for the literals in the file |
| CRuby does the same as the model | Tested by `check.rb` on 72 inputs (`make book-checks`) |

The second link is a test because the JSON decoder is a `partial` function. The
third is the model's standing obligation to agree with CRuby, which the
[differential tests](../../../docs/testing.md) check on every build.

## Limits

- **A user-defined method called inside a loop.** Activation frames are never
  reclaimed, so the frame store grows each iteration and the loop state stops
  being a closed term the kernel can evaluate. This needs a framing lemma for
  the frame store, which has not been written.
- **Blocks and iterators** (`each`, `times`, `map`). They live in the prelude,
  and each call pushes frames, so they meet the same problem.
- **Strings, Arrays and Hashes as symbolic inputs.** Only integer inputs are
  symbolic so far. Building an Array from symbolic integers works.
- **Abstracting the inputs automatically.** `bin/new-book` generates
  `Program.lean` for the literal program; replacing literals with variables is
  done by hand, and the `#guard` is what makes that safe.
