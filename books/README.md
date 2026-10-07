# books/ — every proof in this repository

[`../ruby-lean`](../ruby-lean/README.md) holds the two things that proofs are
*about*: an executable model of Ruby (`RubyCore/`) and a type checker for
Sorbet-annotated programs (`Checker/`). It proves nothing. This package uses it
as a library and holds the proofs, as a collection of *books*: each is a
directory under [`Books/`](Books/) with one result at its head. The name follows
ACL2's community books.

| Book | What it proves | Start at |
|---|---|---|
| [`Books/TypeSoundness/`](Books/TypeSoundness/README.md) | A program the checker accepts never raises a type error when the model runs it: `validateD p d = true → … → typeStuck (run fuel p) = false`, for every fuel | [`Soundness.lean`](Books/TypeSoundness/Soundness.lean) |
| [`Books/Metatheory/`](Books/Metatheory/README.md) | Facts about the model itself: the step relation and the executable `stepFn` agree, type safety stated as reachability, and the heap and stack lemmas the soundness proof stands on | [`Machine/Step.lean`](Books/Metatheory/Machine/Step.lean) |
| [`Books/FastPower/`](Books/FastPower/README.md) | One Ruby program, exponentiation by squaring, computes `b ** n` for every `b` and `n` | [`Proof.lean`](Books/FastPower/Proof.lean) |

[`Books/Lib/`](Books/Lib/) is not a book. It is the machinery for proving things
about a single program (running the kernel on a symbolic machine), and
[the FastPower page](Books/FastPower/README.md) explains how to write a new
program book with it.

Every headline theorem depends on `propext`, `Classical.choice` and `Quot.sound`
and nothing else. The build prints this and the checks below fail if it changes.

## Build and check

From the repository root:

```bash
make books        # build every book
make gate         # the gate: must be green before a commit
make proofs       # the metatheory's axioms and the measurements it depends on
make comparator   # an independent check of the soundness theorem
```

Or here, directly:

```bash
lake build                      # every book, as far as it is claimed (see below)
./scripts/run_typed_ratchet.sh  # the gate
./scripts/check-proofs.sh
./scripts/run-comparator.sh
```

The first build takes roughly half an hour on a cold cache, almost all of it in
`Books/TypeSoundness/`. Rebuilds after a change take seconds.

### What `lake build` covers

Every file under `Books/`. Each book is one Lake library over its whole
directory (`FastPower`, `Metatheory`, `TypeSoundness`), and CI fails if any file
stops building.

Soundness-proof files that were written against an earlier version of the model
and have not been rebuilt are not under `Books/`. They are in
[`Unrebuilt/`](Unrebuilt/README.md), unedited and out of the build, with a list
of what each one is waiting on. The soundness theorem does not depend on them.

### The gate

[`scripts/run_typed_ratchet.sh`](scripts/run_typed_ratchet.sh) is the check that
must pass before a commit. In order, it:

1. checks that the checker imports nothing from the model
   (`../ruby-lean/scripts/check-isolation.sh`);
2. builds the soundness theorem for the enabled rules and rejects any axiom
   beyond Lean's three;
3. builds the negative controls: programs and derivations the checker must
   refuse;
4. runs every program in [`corpus/`](corpus/) through Sorbet, the desugarer and
   the derivation emitter, and reports which ones the real `validateD` accepts;
5. runs the same programs under CRuby and under the model and fails on any
   disagreement.

`--clink-rebuild` runs steps 1–3 only. `RATCHET_SKIP_AGREEMENT=1` skips step 5.
The older full-coverage audit (`--full-corpus`) reads worked theorems that are
in `Unrebuilt/`, and is there with them.

### The comparator

[`scripts/run-comparator.sh`](scripts/run-comparator.sh) checks the soundness
theorem with [`leanprover/comparator`](https://github.com/leanprover/comparator).
[`Comparator/Challenge.lean`](Comparator/Challenge.lean) states the three
theorems with `sorry` for a proof. The comparator checks that the statements
proved in `Books/TypeSoundness/Soundness.lean` are identical to those, that the
proofs use only the three permitted axioms, and that a fresh Lean kernel accepts
the whole dependency closure. The script's header says what is not stock about
the run.

## Vocabulary

The code and the notes use a few project-specific words.

| Word | Meaning |
|---|---|
| model | `RubyCore`: the abstract machine and its step function `stepFn`. What "Ruby" means in every theorem here |
| checker | `Checker`: the type checker. Its entry point is `validateD`, which takes a program and a derivation and answers `true` or `false` |
| derivation | The untrusted hint the checker is given (`Deriv`). A wrong one costs an accept; it cannot produce an unsound one |
| rule | One constructor of the checker's typing judgment (`DJudge` and its companions) |
| clink | A rule together with the proof that it is sound on the model. The registry of clinks is what the soundness theorem quantifies over. A rule with no clink is *gated*: the checker refuses any derivation that uses it |
| rung | One program in `corpus/`. A rung is *climbed* when `validateD` accepts it |
| ratchet | The gate. Its numbers (rules enabled, rungs climbed) only go up |
| control | A negative test: something that must be rejected, or a countermodel showing why a hypothesis is needed |
| conformance | A machine state agrees with the checker's static context (`StateOk`). Preserving it across a step is most of the soundness proof |

## Layout

| Path | What it is |
|---|---|
| `Books/` | The books |
| `Comparator/` | The comparator's challenge file, config and replay patch |
| `corpus/` | The Sorbet-annotated Ruby programs the gate measures the checker on. The `.rb` files are the source of truth |
| `build/` | Generated from `corpus/` by `scripts/build_corpus.py`. Not committed |
| `scripts/` | The gate, the corpus pipeline driver, the proof audit and the comparator run |
| `MainActiveRatchet.lean`, `DenotationReport.lean` | The gate's report executables |
| [`Unrebuilt/`](Unrebuilt/README.md) | Proof files not yet rebuilt against the current model. Not built |
| [`AGENTS.md`](AGENTS.md), `notes/type-soundness/` | The working record of the checker and its soundness proof: current state, then the chronological notes |

The parts of the pipeline that are also used outside the gate stay with the
checker in `../ruby-lean/scripts/`: `srb_sigs.py` and `read_sigs.rb` (signatures
from Sorbet), `emit_deriv.rb` (the derivation emitter), and
`generate_audited_checker.py`.

## Where things were before

The proofs used to live inside `ruby-lean/`. The notes and older commits use
those paths.

| Before | Now |
|---|---|
| `ruby-lean/Ratchet/`, namespace `Ratchet` | `ruby-lean/Checker/`, namespace `Checker` |
| `ruby-lean/Denote/`, namespace `Ratchet.Denote` | `Books/TypeSoundness/`, namespace `Checker.Soundness` |
| `Denote/Bridge.lean` | `Books/TypeSoundness/Soundness.lean` |
| `Denote/Safety.lean` | `Books/TypeSoundness/RuleCoverage.lean` |
| `Denote/Ty/` | `Books/TypeSoundness/Denotation/` |
| `Denote/Sem/` | `Books/TypeSoundness/Conformance/` |
| `Denote/Clink/` | `Books/TypeSoundness/Registry/` |
| `ruby-lean/Semantics/` | `Books/TypeSoundness/Semantics/` |
| `ruby-lean/RubyCore/Proof/` | `Books/Metatheory/` (see [its README](Books/Metatheory/README.md) for the file-by-file map) |
| `ruby-lean/Comparator/` | `Comparator/` |
| `ruby-lean/corpus/`, `ruby-lean/build/` | `corpus/`, `build/` |
| `ruby-lean/scripts/run_typed_ratchet.sh` and the other gate scripts | `scripts/` |
| `ruby-lean/AGENTS.md`, `ruby-lean/notes/ratchet/` | `AGENTS.md`, `notes/type-soundness/` |
