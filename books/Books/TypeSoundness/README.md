# `Books/TypeSoundness/` — accepted programs do not get type-stuck

This book is a type checker and the proof that its answer means something. The
checker ([`Checker/`](Checker/README.md)) decides whether a Sorbet-annotated
Ruby program is well typed. The rest of the book proves what that guarantees
when the model runs the program. The theorem is in
[`Soundness.lean`](Soundness.lean):

```lean
theorem validateD_safe_run {p : Checker.Expr} {d : Deriv}
    (h : validateD p d = true) (hb : bootOkB = true) (fuel : Nat) :
    Semantics.typeStuck (Semantics.run fuel (toRuby p)) = false
```

If the executable checker `validateD` accepts program `p`, with any derivation
`d`, then running `p` on the model from the booted core library, for any number
of steps, never ends in an uncaught `NoMethodError`, `ArgumentError` or
`TypeError`. `bootOkB = true` says the booted machine satisfies the invariant;
it is a closed boolean that the build evaluates, and it is what keeps the
theorem from holding vacuously. `validateD_safe` is the same statement from any
conformant machine, and `validateD_safe_boot` is the step between.

The hypothesis is the verdict of the code that runs, not a relation that the
code is separately claimed to implement.

The theorem is proved, with no `sorry` and no extra axioms, for every typing
rule the checker has enabled. Every file in this directory builds.

```sh
make soundness                                          # from the repository root
scripts/check-soundness.sh --proofs-only                # here: the proofs without the corpus
```

## How the proof is put together

The import graph runs one way, and this is the order to read in.

| Step | Directory | What a file here says |
|---|---|---|
| 0 | [`Checker/`](Checker/README.md) | **The checker**: the typing rules and the executable `validateD`. It imports nothing from the model or from the steps below |
| 1 | [`Denotation/`](Denotation/) | **What a type means**: for each checker type, the set of runtime values it describes on a real heap |
| 2 | [`Conformance/`](Conformance/) | **What it means for a machine to agree with the checker**: `StateOk`, and the lemmas that carry it across a `stepFn` transition. This is most of the book |
| 3 | [`Judgment/`](Judgment/) | **The semantic contract of a typing judgment** |
| 3 | [`Rules/`](Rules/) | **What one rule owes**: the proof, rule by rule, that each typing rule meets the contract |
| 4 | [`Registry/`](Registry/README.md) | **No rule without its proof**: each rule is paired with its proof, and `AuditBridge.lean` turns a derivation the checker accepted into a certified one |
| 5 | [`Soundness.lean`](Soundness.lean) | **The theorem**, composing the above in about forty lines |

[`Comparator/`](Comparator/) is the independent check of that theorem.
`Comparator/Challenge.lean` restates the three soundness theorems with `sorry`
for a proof, and `make comparator` has
[`leanprover/comparator`](https://github.com/leanprover/comparator) verify that
`Soundness.lean` proves exactly those statements, with Lean's three axioms only,
in a fresh kernel. To review what the book claims, read that file. Its `sorry`s
are deliberate and are the only ones in the book.

[`Semantics/Interp.lean`](Semantics/Interp.lean) is where the model's `stepFn`
is imported and `typeStuck` is defined.

## The corpus and the scripts

Everything the checker is measured with is in this directory too.

| Path | Contents |
|---|---|
| [`corpus/`](corpus/) | 267 Sorbet-annotated Ruby programs. Each `NNN-name.rb` has a `NNN-name.meta.json` saying what Sorbet and the checker are expected to answer. `accepted.txt` records which ones the checker accepts |
| `scripts/check-soundness.sh` | The whole check: what `make soundness` runs |
| `scripts/srb_sigs.py`, `read_sigs.rb`, `emit_deriv.rb` | The untrusted scripts in front of the checker: read the signatures (with Sorbet, or with Prism for the browser) and propose a typing derivation |
| `scripts/build_corpus.py`, `check_pipeline.py`, `record_baseline.py`, `cmp_sig_readers.py` | Run the corpus through those scripts; the pipeline's own controls; record expected answers; compare the two signature readers |
| `scripts/generate_audited_checker.py`, `check-isolation.sh` | Regenerate `Checker/Audit/`; check that the checker imports nothing outside itself |
| `scripts/run-comparator.sh` | What `make comparator` runs |
| `Report/` | The corpus report that `make soundness` prints, and its executable (`corpus-report`) |
| `Probes/AxiomAudit.lean` | Prints the axioms of the supporting lemmas and of a few worked end-to-end theorems; the check fails on any outside Lean's three |
| `build/` | Output of `build_corpus.py`. Not committed |

`Conformance/` is grouped by the part of the machine state a lemma is about:

| Directory | Contents |
|---|---|
| `Conformance/Core/` | `StateOk` itself; the framing contracts; `Boot.lean`, which defines `bootOkB` |
| `Conformance/Heap/` | Allocation, the primitive heap invariants, instance-variable writes |
| `Conformance/Names/` | Absence facts: which names are not defined where |
| `Conformance/Class/`, `Subclass/`, `Module/` | Creating a class, a subclass or a module: what survives it and what it establishes |
| `Conformance/Instance/`, `Singleton/` | Instance and singleton method tables and their dispatch |
| `Conformance/Closure/` | Captured frames: what a lambda or block can still read and write after its creator returns |

## Controls and examples

[`Controls/`](Controls/) is negative: countermodels, `#guard`s, and theorems
showing that a hypothesis cannot be dropped. `Controls/All.lean` imports every
one of them. [`Examples/`](Examples/) has derivations for concrete programs,
checked end to end. Both are part of the build.

## Names

Declarations are in the namespace `Checker.Soundness`. They sit inside the
checker's namespace so that `Expr` and `Ty` mean the checker's own copies. The
checker does not import the model, both libraries define those names, and this
book is the one place that imports both.

In the source, a typing rule together with its soundness proof is called a
*clink*, and the registry of them is what the theorem quantifies over.
