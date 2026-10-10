# Prove a program correct

This guide proves a statement about what a Ruby program computes. The proof is
checked by Lean against the model's step function, so it is a statement about
every step of the run: the program terminates, it does not raise, and it prints
and returns what the theorem says.

A proof about one program lives in a *program book*: a directory under
`books/Books/` with the program, the program as a Lean term, and the proof.
[`Books/FastPower/`](https://github.com/sam-xif/ruby-lean/tree/main/books/Books/FastPower)
is a complete one. It states what it means to compute `b ** n`, proves that a
simple loop and an exponentiation-by-squaring loop both do, and proves that the
second takes fewer steps.

## 1. Start a book

Take a program and check that the model runs it and agrees with CRuby:

```ruby
# gcd.rb
def gcd(a, b)
  while b != 0
    a, b = b, a % b
  end
  a
end

puts gcd(48, 18)
gcd(48, 18)
```

```console
$ bin/ruby-lean --compare gcd.rb
6
=> 6
AGREE  the model and CRuby print the same and end the same way
```

Create the book:

```console
$ bin/new-book Gcd gcd.rb
created books/Books/Gcd/ and registered it in books/lakefile.toml
next:   cd books && lake build Gcd
```

It contains:

| File | Contents |
|---|---|
| `gcd.rb`, `gcd.json` | The program, and the program in the model's core language |
| `Program.lean` | The core program as a Lean term, `program : Expr` |
| `Proof.lean` | A first theorem, already proved |
| `Check.lean` | Build-time checks: `Program.lean` is `gcd.json`, and the theorems use no extra axioms |
| `check.rb` | Compares the model with CRuby on `gcd.rb`. `make book-checks` runs it |

## 2. The theorem you get for free

```console
$ cd books && lake build Gcd
```

`Proof.lean` already states and proves this:

```lean
theorem runs : ∃ v m', Runs program v m' ∧ m'.out = "6\n"
```

`Runs program v m'` says that the program, started the way `rubycore` starts it
(on the heap the core library boots), terminates normally with value `v` in
machine state `m'`. Normally means: no exception, nothing the model does not
support, no stuck state. `m'.out` is everything the program printed.

Nobody wrote a proof of that by hand. The Lean kernel can evaluate `stepFn`, so
the proof is "run it":

```lean
def steps : Nat := 335
def final : Machine := (stepN steps (start program)).getD default

theorem reaches_final : stepN steps (start program) = some final := by kernel_rfl
```

`stepN k m` applies `stepFn` `k` times. `kernel_rfl` asks the kernel to compute
both sides and compare them. If the step count or the claimed state were wrong,
the kernel would reject the theorem.

This is a theorem about one run. It is the same fact a test establishes, except
that it is about the model's definition, not about a compiled binary, and it is
the starting point for the general statement.

## 3. Make the inputs variables

To prove something for every input, turn the literals into parameters. In
`Program.lean`, change

```lean
def program : Expr :=
  … RubyCore.Expr.send none "gcd" [RubyCore.Expr.int 48, RubyCore.Expr.int 18] none …
```

into

```lean
def program (a b : Int) : Expr :=
  … RubyCore.Expr.send none "gcd" [RubyCore.Expr.int a, RubyCore.Expr.int b] none …
```

and state the `#guard` in `Check.lean` for `program 48 18`. Giving names to the
subterms the proof will mention (the loop condition, the loop body) keeps the
states below readable; `FastPower/Fast/Program.lean` does this.

## 4. Find where the kernel stops

The kernel can still run the model when the inputs are variables. It stops only
where the machine has to branch on a value that depends on one:

```lean
#kernel_steps 400 fun (a b : Int) => start (program a b)
```

reports how many transitions the kernel ran and the test it could not decide.
For a loop that is the loop condition. Those points are the only places where
the proof has to say something.

To see what the machine looks like around them, print a concrete run:

```lean
#eval trace 400 (start (program 48 18))
```

Each line is one transition: the activation stack, the sizes of the frame store
and the heap, the control, and the continuation. This is where the frame and
object numbers in the next step come from.

## 5. Specification, states, segments, invariant

A proof about a loop has four parts. `FastPower/Fast/Proof.lean` is about 200
lines and is laid out in this order.

**Specification.** Say what the program must do without mentioning how. In
`FastPower/Spec.lean`:

```lean
def PowerResult (b : Int) (n : Nat) (v : Value) (m' : Machine) : Prop :=
  v = .int (b ^ n) ∧ m'.out = toString (b ^ n) ++ "\n"

def ComputesPower (program : Int → Nat → Expr) : Prop :=
  ∀ (b : Int) (n : Nat), ∃ v m', Runs (program b n) v m' ∧ PowerResult b n v m'
```

Any program can be measured against it. The book proves it of two.

**States.** Define the machine at the loop test as a function of the loop's
variables. Do not write it out in full. Take everything the loop leaves alone
(the booted heap, the classes, the frames) from the machine the kernel computes,
and spell out only what changes:

```lean
def entry (b : Int) (n : Nat) : Machine := (stepN 51 (start (program b n))).getD default

def loopHead (b : Int) (n : Nat) (result square left : Int) : Machine :=
  let m := entry b n
  { m with frames := …the locals of the loop's frame… }
```

**Segments.** Prove each straight stretch between two states by running it:

```lean
theorem setup (b : Int) (n : Nat) :
    stepN 51 (start (program b n)) = some (loopHead b n 1 b n) := by kernel_rfl

theorem odd_body (b : Int) (n : Nat) (r s e : Int) :
    stepN 26 (parity b n r s e true)
      = some (loopHead b n (r * s) (s * s) (Int.fdiv e 2)) := by kernel_rfl
```

Each is one line, and each holds for all values of the variables. The right-hand
side shows what Ruby's operators became: `left / 2` on integers is `Int.fdiv`.

**Invariant.** State one invariant over the machine and prove it inductive.
The program's *cut points* are its start and the head of each loop. The
invariant says which cut point the machine is at, what the loop invariant says
about the machine's own frame there, and how many transitions remain:

```lean
inductive Inv (b : Int) (n : Nat) : Nat → Machine → Prop
  | start : Inv b n (cost n) (start (program b n))
  | loop (result square : Int) (left : Nat) (h : result * square ^ left = b ^ n) :
      Inv b n (loopCost left) (loopHead b n result square left)
```

It is inductive (`Inductive` in `Lib/Invariant.lean`) when every machine it
holds of either runs on to another machine it holds of, spending exactly the
transitions it claims, or finishes in a state the specification accepts. Proving
that takes one case per path between cut points: the segments supply the
execution, and ordinary arithmetic shows the loop invariant is re-established.
`Inductive.returnsIn` then gives termination, the result, and the exact running
time at once; the remaining count is the termination measure.

```lean
theorem computes_power : ComputesPowerIn program cost := fun b n =>
  (inv_inductive b n).returnsIn .start
```

Because the invariant counts transitions, running times can be compared.
`FastPower/Faster.lean` proves the simple loop takes `24 * n + 65` transitions,
the squaring loop at most `43 * bitLength n + 69`, and so the second takes fewer
for every exponent from 6 up.

Two habits keep these proofs fast. Establish arithmetic facts before any fact
about a machine is in context, because `omega` is slow when it has to read one.
And prefer `h ▸ …` or a helper lemma to `rw … at` on a hypothesis that mentions
a machine.

## 6. What the theorem covers

| Link | Status |
|---|---|
| `program a b`, booted and run as `rubycore` does, does what the theorem says | Proved, for all inputs |
| `Program.lean` is the desugared `gcd.rb` | Checked at build time by the `#guard` in `Check.lean`, for the literals in the file |
| CRuby does what the model does on this program | Tested by `check.rb`, on the inputs it lists |

The second link is a build-time check and not a theorem because the JSON
decoder is not a function the kernel can evaluate. The third is the model's
standing obligation to agree with CRuby, which the
[differential tests](../testing.md) exist to check.

## The library

[`Books/Lib/`](https://github.com/sam-xif/ruby-lean/tree/main/books/Books/Lib)
is what every program book imports.

| File | Contents |
|---|---|
| `Exec.lean` | `stepN`, `Reaches`, `Returns` and their algebra; the `kernel_rfl` tactic; the `#kernel_steps` and `#kernel_whnf` commands |
| `Boot.lean` | `start p`, the booted machine `rubycore` runs `p` on, with `boot_ok`; `Runs`; `IsArray` |
| `Invariant.lean` | `Inductive`, an invariant at a program's cut points that counts transitions, and `Inductive.returnsIn`; `ReturnsIn`, `RunsIn` |
| `Trace.lean` | `trace` and `showState`, for looking at concrete runs |

## Limits

These are the shapes of program that have been proved this way so far:
straight-line code, method calls, object construction, instance variables, and
`while` loops over integers.

* **A user-defined method called inside a loop.** The model never reclaims
  activation frames, so the frame store grows on each iteration and the loop
  state is no longer a fixed term. This needs a framing lemma for the frame
  store, which has not been written.
* **Blocks and iterators** (`each`, `times`, `map`). They are defined in the
  prelude and each call pushes frames, so they meet the same obstacle.
* **Symbolic strings, arrays and hashes.** Only integers have been used as
  symbolic inputs. Building an array from symbolic integers works.
