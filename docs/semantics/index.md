# The semantics

The model is an abstract machine. A *configuration* holds the expression being
evaluated, a stack of continuations saying what to do with its value, the
activation frames, and the heap. One Lean function, `stepFn`, takes a
configuration to the next one. Running a program is applying `stepFn` until it
reports a final value or an uncaught exception.

```lean
def stepFn (m : Machine) : StepResult
def run (fuel : Nat) (m : Machine) : RunResult
```

Three choices shape everything else.

* **Small steps over an explicit configuration.** What Ruby programs can
  observe depends on the order of effects and on non-local exits: `ensure`
  ordering, `break` and `return` from blocks, exception propagation. A
  step-by-step machine with a visible continuation stack states all of that
  directly.
* **Everything is a method call.** `a + b`, `a[i]`, `x.y = z` and `-a` are all
  sends. So the semantics has one dispatch rule, and metaprogramming is ordinary
  mutation of the heap, not a set of extra evaluation rules.
* **Classes are objects in the heap.** Method tables, constants, the superclass
  pointer and included modules are fields of heap objects. Defining a method is
  a heap write, and looking one up is a pure function of the heap.

## Reading order

These pages state the semantics in prose and rules. Source comments cite them as
*Semantics NN §M*: for example, *Semantics 02 §5* is section 5 of
[Method dispatch](dispatch.md).

| Page | Covers |
|---|---|
| [00 — Notation and abstract syntax](syntax.md) | The configuration, the judgments, the core language, how surface Ruby desugars into it, what is excluded |
| [01 — Objects, values and the heap](objects.md) | Values, objects, classes and eigenclasses, identity and equality, mutation and freezing |
| [02 — Method dispatch](dispatch.md) | The ancestor chain, method lookup, `send`, `method_missing`, `super`, visibility |
| [03 — Variables, scope and constants](variables.md) | Locals, instance, class and global variables, and the two-phase constant lookup |
| [04 — Blocks, procs and control flow](control-flow.md) | Closures, arity, the unwinding model, `return`/`break`/`next`/`redo`/`retry`, exceptions, enumerators |
| [Design decisions](design.md) | Why the Lean definitions have the shape they do, and what earlier formalizations of Ruby contributed |
| [Supported Ruby](supported-ruby.md) | What the model runs and what it declines |

Claims on those pages carry a tag: **[V]** was verified against CRuby 4.0.5,
**[D]** comes from documentation or ISO 30170, and **[?]** is open.

Where a page and the code disagree, the code is the semantics. The pages are its
readable account.

## The code

Everything is under `ruby-lean/RubyCore/`. Read the files in this order.

| File | Contents |
|---|---|
| `Syntax.lean` | `Expr`, the core language, and the decoder for the JSON the desugarer writes |
| `Heap.lean` | `Value`, `Object`, `Heap`; the initial heap with `BasicObject`, `Object`, `Module`, `Class` and the other core classes; `classOf`, `ancestors`, method lookup and constant lookup as pure functions |
| `Machine.lean` | `Machine`, the configuration: control, the continuation stack, the frame store and the activation stack, output |
| `Repr.lean` | The default `inspect`, `to_s`, `==` and `eql?`, exact to the character |
| `Builtins.lean`, `Builtins/` | The methods implemented natively, one file per group of classes: `Objects`, `Numerics`, `Strings`, `Collections`, `Regex`, `Rationals`, `Complex`, `Modules`. `Support.lean` holds what they share |
| `Interp.lean`, `Interp/` | `stepFn` and `run`. `Interp.lean` is the top-level case split on the control; the files under `Interp/` are its parts, listed below |
| `Boot.lean` | Runs the prelude to produce the heap a program starts on |
| `Obs.lean` | What a finished run is observed as: output, the result's `inspect`, the exception's class and message |
| `Trace.lean` | Prints a run one configuration at a time. Used by `--trace` and the playground |

The parts of the interpreter, in `Interp/`:

| File | Contents |
|---|---|
| `Support.lean` | Parameter binding, splats, closure creation and invocation |
| `Dispatch.lean` | The ancestor walk, entering a method or a class body, eigenclasses, visibility, `method_missing` |
| `Send.lean` | `invoke`, `super`, and the evaluation of arguments, keywords and block arguments |
| `Kont.lean` | Applying a continuation to a value, and unwinding the stack for a jump or an exception |
| `Reflect.lean` | `define_method`, `class_eval`, `instance_eval`, `alias_method`, `const_get` and the rest of reflection |
| `Construct.lean`, `Copy.lean` | `new`, `allocate`, `initialize`; `dup` and `clone` |
| `Mutation.lean` | Method definition, removal and `undef`, with their callbacks |
| `BlockPass.lean` | `&blk`, `to_proc`, and destructuring of block parameters |
| `Enumerator.lean` | Internal and external enumerators |
| `Inspect.lean`, `Frozen.lean` | `inspect` of ordinary objects; `FrozenError` |
| `Require.lean`, `Forwardable.lean` | `require` of the modeled libraries |

Supporting libraries, which the builtins use and which say nothing about Ruby's
evaluation order:

| Directory | Contents |
|---|---|
| `Numeric/` | `Float#to_s` (shortest round-trip), the Mersenne Twister behind `Random`, `Rational`, `Complex` |
| `Regex/` | A regular-expression parser and a backtracking matcher |
| `Generated/` | Tables written by scripts: the prelude as Lean terms (`Prelude.lean`), the names of CRuby's built-in methods (`CRubyNames.lean`), Unicode character classes (`Unicode.lean`). `make gen` regenerates them and `make gen-check` fails if one is stale |
| `Sorbet/` | Reads `sig` declarations out of a program without running it (`rubycore --sigs`, `--fragment`) |

## The prelude

Much of Ruby's core library is written in Ruby. The model does the same:
`ruby-lean/prelude/prelude.rb` defines `Enumerable`, `Comparable`,
`Range#each`, `Integer#times` and about a hundred other methods in Ruby, and the
model runs that file to build the heap every program starts on. Only what cannot
be written in Ruby, such as integer addition or string concatenation, is a
native builtin in `Builtins/`.

`ruby-lean/prelude/features/` holds the libraries that load on `require`:
`json`, `uri`, `forwardable`, `pathname` and a model of `sorbet-runtime`.

## Two definitions of a step

`stepFn` is a function, which is what makes the model runnable and testable.
`books/Books/Metatheory/Machine/Step.lean` also defines an inductive relation
`Step m m'` for the control core of the language, and proves that the two agree
in both directions. See [the metatheory](../proofs/metatheory.md).
