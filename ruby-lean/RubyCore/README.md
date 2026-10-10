# RubyCore/ — the model

An abstract machine for Ruby. A `Machine` holds the expression being evaluated,
a stack of continuations, the activation frames and the heap. `stepFn` takes a
machine to the next one, and `run` applies it until the program finishes.

[The semantics](../../docs/semantics/index.md) states in prose and rules what
this code implements. Source comments cite those pages as *Semantics NN §M*:
*Semantics 02 §5* is section 5 of
[Method dispatch](../../docs/semantics/dispatch.md).

## Reading order

| File | Contents |
|---|---|
| `Syntax.lean` | `Expr`, the core language, and the decoder for the JSON the desugarer writes |
| `Heap.lean` | `Value`, `Object`, `Heap`; the initial heap; `classOf`, `ancestors`, method and constant lookup |
| `Machine.lean` | `Machine`: control, continuations, the frame store, output |
| `Repr.lean` | The default `inspect`, `to_s`, `==` and `eql?` |
| `Builtins.lean`, `Builtins/` | The methods implemented natively, one file per group of classes |
| `Interp.lean`, `Interp/` | `stepFn` and `run`. `Interp.lean` is the case split on the control; `Interp/` holds dispatch, sends, continuations, reflection and the rest |
| `Boot.lean` | Runs the prelude to produce the heap a program starts on |
| `Booted.lean` | Starts a program on that heap taken as a literal (`Generated/BootedHeap.lean`), without running the prelude. `rubycore` boots; proofs start here. Not imported by `RubyCore.lean` |
| `Obs.lean` | What a finished run is observed as: output, result, exception |
| `Trace.lean` | Prints a run one machine state at a time |

Libraries the semantics uses:

| Directory | Contents |
|---|---|
| `Numeric/` | `Float#to_s`, the Mersenne Twister behind `Random`, `Rational`, `Complex` |
| `Regex/` | A regular-expression parser and matcher |
| `Generated/` | Files written by scripts: the prelude as Lean terms, the names of CRuby's built-in methods, Unicode character classes. Do not edit; run `make gen`. `BootedHeap.lean`, the heap the prelude boot produces, is also written here, but as a build artifact that is not committed |
| `Sorbet/` | Reads `sig` declarations out of a program without running it |

`../RubyCore.lean` imports all of it. `../Main.lean` is the `rubycore`
executable.

## Two properties to keep

**The kernel can evaluate `stepFn`.** Proofs about programs
([`books/Books/FastPower/`](../../books/Books/FastPower/README.md)) work by
asking the Lean kernel to run the model. That requires the definitions on the
execution path to be total functions the kernel can unfold: structural or
fuel-bounded recursion, no `partial def`.

**The model declines; it does not approximate.** A program that uses something
the model does not implement gets `unsupported` with a reason, never a guess.
`Generated/CRubyNames.lean` lists every built-in method of CRuby so that a call
to one the model lacks is declined, where it would otherwise raise a
`NoMethodError` that CRuby does not.
