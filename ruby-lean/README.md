# ruby-lean/ — the Lean project

One Lake package with four libraries:

| Library | What it is |
|---|---|
| `RubyCore/` | The model: the machine, `stepFn`, the heap, the builtins. Also builds the `rubycore` binary, which reads RubyCore JSON and prints what the program outputs |
| `Ratchet/` | The type checker: its own copy of `Expr`/`Ty`, derivations (`Deriv`) and `validateD`. It imports nothing from `RubyCore/` |
| `Semantics/` | One file that imports the real `stepFn`, so the proofs can talk about it |
| `Denote/` | The proofs connecting the two: what each type means on the real machine, a proof for each typing rule, and `validateD_safe_boot` in `Denote/Bridge.lean` |

Other directories:

| Path | What it is |
|---|---|
| `corpus/` | The annotated Ruby programs ("rungs") the checker is measured on. This is the source of truth |
| `build/` | Generated from `corpus/` by `scripts/build_corpus.py`. Never edit it |
| `prelude/` | Parts of Ruby's core library (Enumerable, Comparable, …) written in Ruby and run by the model |
| `RubyCore/Proof/` | The model's metatheory. Not on the default build target |
| `scripts/` | The untrusted pipeline stages, the gate, and measurement scripts |
| `notes/` | The working record: what was tried and what went wrong, for the model and the checker |
| `wasm/` | Builds the modules the playground runs in the browser |

## Build and run

```sh
lake build                        # toolchain pinned in lean-toolchain; no external Lean deps
echo 'puts 1 + 2' | ruby ../desugar/bin/export-json | .lake/build/bin/rubycore
scripts/cmp.sh 'p [1,2].select { |x| x > 1 }'   # CRuby vs the model: AGREE / DIFF / GATE
```

On a cold cache, the model builds in a few minutes and the rest takes about half
an hour, mostly for `Denote/`. Rebuilds after a change take seconds.

`rubycore` exits 0 on success, 3 when the program uses something the model does
not support (the reason is on stderr), and 1 on a model bug.

## The gate

```sh
./scripts/run_typed_ratchet.sh    # must end in RATCHET GREEN before you commit
./scripts/check-proofs.sh         # the off-target metatheory; run it at batch boundaries
```

The gate runs, in order: the isolation check (`Ratchet/` still imports nothing
from `RubyCore/`), the build of the proofs and negative controls, pipeline stages
1–4 over every corpus program, the model-vs-CRuby agreement run (skip it with
`RATCHET_SKIP_AGREEMENT=1`), and finally the checks that every typing rule has a
semantic proof and that the certified fragment has not shrunk.

## Where to read next

- [`RubyCore/README.md`](RubyCore/README.md): the written semantics of the model.
- [`AGENTS.md`](AGENTS.md): the checker's current state, the pipeline and its design record.
- [`Ratchet/README.md`](Ratchet/README.md) and [`Denote/README.md`](Denote/README.md): how
  each side is organized.
- [`notes/README.md`](notes/README.md): the chronological working notes.
- In `../docs/`: [Layout and fragment](../docs/model/fragment.md) (every model file, and
  what Ruby is and isn't supported) and [Metatheory](../docs/model/metatheory.md).
- Editing `prelude/prelude.rb`? Regenerate `RubyCore/Prelude.lean` afterwards; see
  [Regenerating the generated files](../docs/model/fragment.md#regenerating-the-generated-files).
