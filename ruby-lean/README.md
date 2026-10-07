# ruby-lean/ — the Lean project

One Lake package with two libraries:

| Library | What it is |
|---|---|
| `RubyCore/` | The model: the machine, `stepFn`, the heap, the builtins. Also builds the `rubycore` binary, which reads RubyCore JSON and prints what the program outputs |
| `Checker/` | The type checker: its own copy of `Expr`/`Ty`, derivations (`Deriv`) and `validateD`. It imports nothing from `RubyCore/`. Builds `ratchetd` (runs the checker over the corpus) and `validate-one` (the playground's adapter) |

Nothing in this package is a proof. The model's metatheory, the checker's
soundness theorem (`validateD_safe_run`), the corpus the checker is measured on
and the gate all live in [`../books/`](../books/README.md), a separate Lake
package that uses this one as a library.

Other directories:

| Path | What it is |
|---|---|
| `prelude/` | Parts of Ruby's core library (Enumerable, Comparable, …) written in Ruby and run by the model |
| `scripts/` | Generators for the committed Lean sources, the checker's untrusted front end (`srb_sigs.py`, `read_sigs.rb`, `emit_deriv.rb`), and measurement scripts |
| `notes/` | The model's working record: what was tried and what went wrong |
| `wasm/` | Builds the modules the playground runs in the browser |

## Build and run

```sh
lake build                        # toolchain pinned in lean-toolchain; no external Lean deps
echo 'puts 1 + 2' | ruby ../desugar/bin/export-json | .lake/build/bin/rubycore
scripts/cmp.sh 'p [1,2].select { |x| x > 1 }'   # CRuby vs the model: AGREE / DIFF / GATE
```

On a cold cache the package builds in a few minutes. Rebuilds after a change
take seconds.

`rubycore` exits 0 on success, 3 when the program uses something the model does
not support (the reason is on stderr), and 1 on a model bug.

The default runtime boots core Ruby. Modeled optional libraries (`json`, `uri`,
`forwardable`, `sorbet-runtime`) load on `require`; `pathname.rb` is a separate
feature over the Pathname class already booted by the pinned CRuby 4.0.5.
`--preload-json` loads JSON before the input program, matching the differential
runner's observation wrapper. It is unnecessary for ordinary standalone runs.
`python3 scripts/check-feature-loading.py` compares scope, reentry, caching and
failed-load retry against CRuby using identical feature bodies on both sides.

## The gate

The gate is in `../books/`, because what it checks is a proof:

```sh
(cd ../books && ./scripts/run_typed_ratchet.sh)   # must end in RATCHET GREEN before you commit
(cd ../books && ./scripts/check-proofs.sh)        # the metatheory; run it at batch boundaries
```

A change to `RubyCore/` or `Checker/` can break a proof without breaking this
package's build, so run the gate after changing either.
[`../books/README.md`](../books/README.md) says what each stage checks.

After changing an authored checker source under `Checker/Check/`, regenerate its
traced projection under `Checker/Audit/`:

```sh
python3 scripts/generate_audited_checker.py
```

## Where to read next

- [`RubyCore/README.md`](RubyCore/README.md): the written semantics of the model.
- [`../books/AGENTS.md`](../books/AGENTS.md): the checker's current state, the pipeline and its design record.
- [`Checker/README.md`](Checker/README.md): how the checker is organized.
- [`../books/README.md`](../books/README.md): the proofs.
- [`notes/README.md`](notes/README.md): the chronological working notes.
- In `../docs/`: [Layout and fragment](../docs/model/fragment.md) (every model file, and
  what Ruby is and isn't supported) and [Metatheory](../docs/model/metatheory.md).
- Editing `prelude/prelude.rb`? Regenerate `RubyCore/Prelude.lean` afterwards; see
  [Regenerating the generated files](../docs/model/fragment.md#regenerating-the-generated-files).
