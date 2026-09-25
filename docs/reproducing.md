# Reproducing the results

Every number in the root `README.md` comes from one of the commands below, run on
a clean checkout. Install the prerequisites first (`scripts/check-prereqs.sh`
lists what is missing and how to install it).

## Everything, in order

```sh
scripts/reproduce.sh                   # build + the typed ratchet gate
scripts/reproduce.sh --with-difftest   # also: model vs CRuby over MRI's bootstraptest
                                       #   (harvests the corpus on first run: one sparse
                                       #    clone of ruby/ruby into $RUBY_SRC or /tmp)
scripts/reproduce.sh --with-proofs     # also: the metatheory + `#print axioms`
```

It stops at the first failure.

## The gate

```sh
cd ruby-lean && ./scripts/run_typed_ratchet.sh            # quiet: the verdict + what's next
cd ruby-lean && ./scripts/run_typed_ratchet.sh --verbose  # every stage's output
```

The last line is **GREEN** or **RED**:

* **GREEN**: nothing is started and incomplete. Every registered rule has a
  semantic proof, every floor holds, the model agrees with CRuby on every
  stripped program, and reach has not dropped. Rungs nobody has worked on yet
  are still GREEN, because nothing claims them.
* **RED**: the certified fragment claims something the proofs cannot back. That
  can be a rule with no semantic proof, a worked theorem about the wrong program,
  a smaller fragment than before, or a floor that moved.

`RATCHET_SKIP_AGREEMENT=1` skips the CRuby replay, which is the fastest useful
run. In a sandbox with a protected uv cache, set
`UV_CACHE_DIR=/private/tmp/ruby-ratchet-uv-cache`.

### Reading the gate's output

On v0.01 (2026-09-15) it prints:

```
pipeline: reach 65 rungs · 252 agree, 0 disagree

259 rungs · fragment 63 (reach 17) · 196 outside
  48 rules certified, 0 owed

RATCHET GREEN
```

| Number | Meaning |
|---|---|
| **259 rungs** | annotated programs in `ruby-lean/corpus/` |
| **fragment 63** | rungs the certified judgment has rules for; for each one, acceptance is its safety proof |
| **reach 17** | the unbroken prefix from rung 001; rung 018 is correctly rejected |
| **48 rules certified, 0 owed** | every rule in the judgment has a semantic proof, so no rung is accepted on an unproved rule |
| **196 outside** | declined, not accepted wrongly. The gate lists what each one hit (42 block arguments, 21 `module`, 8 `casgn`, …); that list is the to-do list |
| **252 agree, 0 disagree** | the Lean model and CRuby produce identical output on every stripped program the certificates are about |

## The model against CRuby

The bootstraptest corpus is harvested, not vendored. One sparse clone, once:

```sh
git clone --depth 1 --filter=blob:none --sparse https://github.com/ruby/ruby /tmp/ruby-src
(cd /tmp/ruby-src && git sparse-checkout set bootstraptest)
desugar/bin/harvest_bootstraptest /tmp/ruby-src/bootstraptest
cd difftest && uv sync && uv run python -m difftest run --tier 0 --sut lean
```

On v0.01 this prints
`1309 programs ran · 995 agree · 0 disagreements · 308 unsupported`.
"Unsupported" means the model declined a program that uses something outside its
fragment, rather than guessing.

## One program by hand

```sh
echo 'puts 1 + 2' | ruby desugar/bin/export-json | ruby-lean/.lake/build/bin/rubycore
```

From `ruby-lean/`, `scripts/cmp.sh 'p [1,2].select { |x| x > 1 }'` runs a snippet
through both CRuby and the model and prints AGREE, DIFF or GATE.

## The proofs

```sh
cd ruby-lean && ./scripts/check-proofs.sh
```

This builds the metatheory, which is off the default build target, and re-checks
that the headline theorems depend only on Lean's three standard axioms
(`propext`, `Classical.choice`, `Quot.sound`).
