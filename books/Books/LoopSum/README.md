# `Books/LoopSum/` — a loop invariant, proved at every visit

The program ([`loop_sum.rb`](loop_sum.rb)) sums the integers below 100:

```ruby
x = 0
y = 0
while x < 100
  # HERE
  y += x
  x += 1
end
puts y
y
```

The claim is the loop invariant: every time control reaches `HERE`, `y` is the
sum of the integers in `0...x` (upper bound exclusive). With the bound `100`
replaced by an arbitrary integer `n`:

```lean
theorem invariant (n : Int) (k : Nat) (m : Machine)
    (hk : stepN k (start (program n)) = some m) (hm : atHere m = true) :
    Invariant n m
```

`stepN k (start (program n)) = some m` says `m` is the machine after `k`
transitions of the run `rubycore` makes. `atHere m` says the machine is about to
evaluate `y += x`. `Invariant n m` says the running frame's `x` holds an
integer in `0...n` and its `y` holds `sumBelow x`, the sum of `List.range x`.
`loop_sum_invariant` is the same statement for `program 100`.

The invariant is a statement about every state of the run, so it would hold
trivially of a run that never reached `HERE`. Two more theorems rule that out:

| Theorem | Statement |
|---|---|
| `here_visited` | For each `x` in `0...n` the run reaches a state at `HERE` with that `x` and `y = sumBelow x` |
| `loop_sum_correct` | The program terminates normally, prints `sumBelow n` and returns it (a negative `n` behaves as `0`) |
| `loop_sum_100` | For `loop_sum.rb` itself, that is `4950` |

All of them depend on `propext`, `Classical.choice` and `Quot.sound` only.

## How the proof works

It follows [`FastPower`](../FastPower/README.md): states at the loop test, at
`HERE` and after the test, written as functions of `x` and `y`; straight-line
segments between them checked by the kernel running `stepFn` (`kernel_rfl`);
the arithmetic of `<` and `+`; and induction on the iterations left.

To cover every visit and not only the states the proof builds, it adds one
step. `clearFor c m` runs `c` transitions from `m` and checks that none of the
states it passes is at `HERE`. The kernel evaluates it on each segment, for all
`x` and `y`. Because `stepN` is a function, a run from the start of a segment
either stops inside it, where `clearFor` applies, or passes its end
(`AtHereAlways.segment`). The only states at `HERE` are then the ones the
segments start from, and those satisfy the invariant by construction.

One detail of the model shows up in the states: assigning a local moves it to
the front of the frame's list, so the locals read `[y, x]` before the first
iteration and `[x, y]` after it. The states take a flag `first` for this.

| File | Contents |
|---|---|
| `Program.lean` | The program as a Lean term, `program n`, with its subterms named |
| `Proof.lean` | The theorems above |
| `Check.lean` | Build-time checks: `program 100` is `loop_sum.json`, and the theorems use no extra axioms |
| `check.rb` | Compares the model with CRuby on this program. `make book-checks` runs it |

```sh
cd books && lake build LoopSum
```
