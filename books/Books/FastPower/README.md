# `Books/FastPower/` — two programs, one specification

A *program book* is a Ruby program together with a statement of what it computes
and a Lean proof of that statement against the model's `stepFn`. This is the
worked example. [Prove a program correct](../../../docs/guides/prove-a-program.md)
is the guide to writing another one, starting from `bin/new-book`.

```bash
make books          # from the repository root; or `lake build` in books/
```

## What the book proves

**The specification** ([`Spec.lean`](Spec.lean)) says what it is to compute a
power, and nothing about how:

```lean
def PowerResult (b : Int) (n : Nat) (v : Value) (m' : Machine) : Prop :=
  v = .int (b ^ n) ∧ m'.out = toString (b ^ n) ++ "\n"

def ComputesPower (program : Int → Nat → Expr) : Prop :=
  ∀ (b : Int) (n : Nat), ∃ v m', Runs (program b n) v m' ∧ PowerResult b n v m'
```

For every base `b` and exponent `n`, the program, run the way `rubycore` runs
it (prelude booted first), terminates normally, prints `b ** n` on a line of
its own and has the value `b ** n`. Normally means no exception, nothing the
model does not support, no stuck state.

**Two programs meet it.** [`slow_power.rb`](slow_power.rb) multiplies `n` times:

```ruby
def raise_to(exponent)
  result = 1
  left = exponent
  while left > 0
    result = result * @base
    left = left - 1
  end
  result
end
```

[`fast_power.rb`](fast_power.rb) squares:

```ruby
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
  end
  result
end
```

Both are a method of a small `Power` class, called as
`Power.new(b).raise_to(n)`, whose result is printed and returned. With the two
literals in each file replaced by arbitrary `b` and `n`
([`Faster.lean`](Faster.lean)):

```lean
theorem slow_computes_power : ComputesPower Slow.program
theorem fast_computes_power : ComputesPower Fast.program
```

**The fast one is faster.** Running time is the number of machine transitions.

```lean
theorem Slow.computes_power : ComputesPowerIn Slow.program Slow.cost   -- cost n = 24 * n + 65
theorem Fast.computes_power : ComputesPowerIn Fast.program Fast.cost

theorem le_fast_cost (n : Nat) : 36 * bitLength n + 69 ≤ Fast.cost n
theorem fast_cost_le (n : Nat) : Fast.cost n ≤ 43 * bitLength n + 69

theorem fast_is_faster (b : Int) (n : Nat) (h : 6 ≤ n)
    (hs : RunsIn (Slow.program b n) slow v m) (hf : RunsIn (Fast.program b n) fast v' m') :
    fast < slow
```

The simple loop takes exactly `24 * n + 65` transitions. The squaring loop takes
between 36 and 43 per binary digit of `n`, so its running time is logarithmic in
the exponent. From `n = 6` on it takes strictly fewer transitions; the
threshold is exact, because `slow_cost_lt_fast_cost` proves the simple loop
takes fewer up to `n = 5`, where it does less work per iteration.

Two things this measure does not say. It does not depend on the base: a
transition that multiplies two integers counts as one however many digits they
have, so this counts operations, not the time the arithmetic takes. And it is
the model's transition count, which is not CRuby's instruction count.

Every theorem depends on `propext`, `Classical.choice` and `Quot.sound` only.

## How the proofs are written

Each program is proved by **one inductive invariant over the machine**
([`Lib/Invariant.lean`](../Lib/Invariant.lean)). A program's *cut points* are
its start and the head of each loop. The invariant says which cut point the
machine is at, what the loop invariant says about the machine's own frame
there, and how many transitions remain. For the fast program:

```lean
inductive Inv (b : Int) (n : Nat) : Nat → Machine → Prop
  | start : Inv b n (cost n) (start (program b n))
  | loop (result square : Int) (left : Nat) (h : result * square ^ left = b ^ n) :
      Inv b n (loopCost left) (loopHead b n result square left)
```

`loopHead b n result square left` is the machine at the loop test with those
values in `raise_to`'s frame. Everything the loop leaves alone (the booted heap,
class `Power`, the other frames) is taken from the machine the kernel computes
and is not written out.

The invariant is *inductive* when every machine it holds of either

- runs on, in at least one transition, to another machine it holds of, with the
  count reduced by exactly that many; or
- finishes in exactly the count, in a state `PowerResult` accepts.

`Inductive.returnsIn` turns an inductive invariant into the theorem: from the
start the program terminates, in exactly `cost n` transitions, with the
specified result. The count is the termination measure, since every advance
spends at least one transition, so correctness and running time come from the
same argument.

Proving the invariant inductive takes one case per path between cut points. The
fast program has four: start to loop, an odd iteration, an even iteration, and
exit. Each case has two ingredients.

**Execution** is checked by the kernel. The Lean kernel can evaluate `stepFn`,
method dispatch included, on a machine whose integer inputs are variables, so a
straight-line stretch is proved by asking it to run:

```lean
theorem setup (b : Int) (n : Nat) :
    stepN 51 (start (program b n)) = some (loopHead b n 1 b n) := by kernel_rfl
```

That line covers booting the prelude, defining `Power`, `Power.new(b)` running
`initialize`, and the call to `raise_to(n)` up to the loop, for all `b` and `n`.
The kernel stops only where the machine branches on a value that depends on a
variable (`left > 0`, `left % 2 == 1`), and a lemma about what the builtin
computed resolves each of those.

**Arithmetic** shows the loop invariant is re-established, for instance
`result * square * (square * square) ^ (left / 2) = result * square ^ left` when
`left` is odd. It is about integers and has no Ruby in it.

| File | Contents |
|---|---|
| [`Spec.lean`](Spec.lean) | `ComputesPower`, and `ComputesPowerIn` for a running time |
| [`Slow/`](Slow/), [`Fast/`](Fast/) | For each program: `Program.lean`, the program as a term; `Proof.lean`, its states, segments and invariant |
| [`Faster.lean`](Faster.lean) | Both meet the specification; the bounds on the fast program; the comparison |
| [`Check.lean`](Check.lean) | The terms are the exported programs; the axiom audit |
| [`check.rb`](check.rb) | The theorems against CRuby and the model's binary |

## What is proved and what is tested

| Link | Status |
|---|---|
| `Slow.program b n` and `Fast.program b n`, booted and run as `rubycore` does, print and return `b ^ n`, in the stated number of transitions | Proved, all `b`, `n` |
| `slow_power.rb` and `fast_power.rb` desugar to `program 3 13` | Tested at build time (`#guard`), for the literals in the files |
| CRuby prints and returns the same, and the model's binary takes the stated number of transitions | Tested by `check.rb` on 80 inputs per program (`make book-checks`) |

The second link is a test because the JSON decoder is a `partial` function. The
third is the model's standing obligation to agree with CRuby, which the
[differential tests](../../../docs/testing.md) check on every build.

## Limits

- **The exponent is a natural number.** The specification quantifies over
  `n : Nat`. Both loops leave a negative exponent's `result` at 1, which is not
  Ruby's `b ** n` there, and the book makes no claim about it.
- **A user-defined method called inside a loop.** Activation frames are never
  reclaimed, so the frame store grows each iteration and the loop state stops
  being a closed term the kernel can evaluate. This needs a framing lemma for
  the frame store, which has not been written.
- **Blocks and iterators** (`each`, `times`, `map`). They live in the prelude,
  and each call pushes frames, so they meet the same problem.
- **Strings, Arrays and Hashes as symbolic inputs.** Only integer inputs are
  symbolic so far.
- **Abstracting the inputs automatically.** `bin/new-book` generates
  `Program.lean` for the literal program; replacing literals with variables is
  done by hand, and the `#guard` is what makes that safe.
