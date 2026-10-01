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

* **GREEN**: the original `validateD_safe_run` soundness theorem passes for the
  enabled registry using only standard Lean axioms, controls and corpus pipeline
  checks pass, and the model agrees with CRuby on the stripped programs checked.
  Disabled clinks and declined positive rungs are work remaining.
* **RED**: an enabled proof fails, soundness uses a nonstandard axiom, a control
  fails, or the pipeline/CRuby checks fail.

`RATCHET_SKIP_AGREEMENT=1` skips the CRuby replay while iterating. In a sandbox
with a protected uv cache, set `UV_CACHE_DIR=/private/tmp/ruby-ratchet-uv-cache`.

```sh
cd ruby-lean
./scripts/run_typed_ratchet.sh --clink-rebuild  # soundness and controls only
./scripts/run_typed_ratchet.sh --full-corpus    # historical full audit and floors
```

The historical full audit keeps its complete-registry requirement, coverage,
worked-theorem cross-checks and floors. It refuses a partial profile; these
requirements do not prevent the default active-soundness gate from being GREEN.

### Reading the active gate's output

With the seven-clink rebuild profile (2026-09-30):

```text
agreement: 254 agree, 0 disagree
ACTIVE CLINKS: 7/99 climbed; 92 gated
CORPUS RUNGS: 8/261 climbed by validateD; 207 positive goals remaining
  accepted prefix: 8; negative controls: 46/46 rejected
  009-add: gated: prim, DJudgeAll.cons, DJudgeAll.nil
...
RATCHET GREEN -- validateD_safe_run passes for the enabled clinks.
```

| Number | Meaning |
|---|---|
| **7/99 clinks climbed** | enabled rules in the active certified registry; disabled rules do not count |
| **8/261 corpus rungs climbed** | production `validateD` accepts under the active policy; each is covered by the original soundness theorem |
| **accepted prefix 8** | consecutive accepted programs from the start of the selected corpus |
| **207 positive goals remaining** | positive rungs declined by the validator or blocked upstream |
| **46/46 negatives rejected** | negative controls pass; rejection does not count as ascent |
| **254 agree, 0 disagree** | the Lean model and CRuby agree on the stripped programs replayed |

The pending list uses the actual verified derivation's trace to name gated rules,
including companion and body rules. The default builds fresh corpus outputs;
`--only 001,009` reports only those selected rungs. Use `--verbose` for all stages
and every rung. Source-controlled admission lives in `Ratchet/ClinkPolicy.lean`;
see [the rebuild guide](../ruby-lean/Denote/Clink/README.md) for climbing a rule.

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
