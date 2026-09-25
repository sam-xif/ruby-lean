# ruby-lean

An executable semantics for a large core of Ruby, written in Lean 4, and a type
checker for a small typed fragment whose "yes" is backed by a proof.

- **The model** (`ruby-lean/RubyCore/`) is a small-step interpreter for Ruby. It is
  tested by running the same programs through it and through CRuby and comparing
  the output. The interpreter is the semantics; there is no separate paper
  definition.
- **The checker** (`ruby-lean/Ratchet/` and `ruby-lean/Denote/`) takes
  Sorbet-annotated Ruby and returns one Lean `Bool`. A theorem says that when it
  returns `true`, the program cannot hit a type error (`NoMethodError`,
  `ArgumentError`, `TypeError`) when run by the model.
- **The playground** (`playground/`) is a browser UI that runs a program through
  every stage, steps the model one transition at a time, and runs CRuby beside it.

> **Version 0.01.** The theorems are proved and the results are reproducible, but
> the typed fragment is small. Read [Limits](#limits) before treating any number as
> a claim about Ruby in general.

## The main theorem

From [`ruby-lean/Denote/Bridge.lean`](ruby-lean/Denote/Bridge.lean):

```lean
theorem validateD_safe_boot {p : Ratchet.Expr} {d : Deriv}
    (h : validateD p d = true) (hb : bootOkB = true) :
    StuckFree bootMachine p
```

`StuckFree` means that for any amount of fuel, running `p` on the model never
ends in a `NoMethodError`, `ArgumentError` or `TypeError` (or a subclass). So if
the checker accepts a program, that program is type-safe under the model, with no
further argument needed. The build prints `#print axioms` for this theorem, and
it uses only Lean's three standard axioms.

Two things keep this from being an empty statement:

- The model it talks about is the same one that is tested against CRuby.
- The checker has negative controls that run at build time. A checker that
  accepted everything would fail the build.

## What you have to trust

Only the last stage. The first four produce a candidate proof; the fifth checks it.

| Stage | Tool | Trusted? |
|---|---|---|
| 1. Read Sorbet signatures | `ruby-lean/scripts/srb_sigs.py` | no |
| 2. Strip annotations | `difftest/ruby/*_strip.rb` | no |
| 3. Desugar to RubyCore JSON | `desugar/bin/export-json` | no |
| 4. Emit a derivation | `ruby-lean/scripts/emit_deriv.rb` | no |
| 5. **Check the derivation** | `validateD`, in Lean | **yes** |

A bug in stages 1–4 can cause a correct program to be rejected. It cannot cause a
wrong program to be accepted.

## Getting started

Install Lean (via elan), CRuby 4.0.x, Sorbet and uv:

```sh
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh
brew install ruby uv
gem install sorbet sorbet-runtime
scripts/check-prereqs.sh      # confirms everything is found
```

Build and run the gate:

```sh
cd ruby-lean && lake build                  # a few minutes for the model, ~30 min cold for the proofs
./scripts/run_typed_ratchet.sh              # ends in RATCHET GREEN or RED
```

Run one program through the model:

```sh
echo 'puts 1 + 2' | ruby desugar/bin/export-json | ruby-lean/.lake/build/bin/rubycore
```

Open the playground at http://localhost:8077:

```sh
cd playground && python3 server.py
```

[Reproducing the results](docs/reproducing.md) has every command behind the
numbers below, including the comparison against CRuby's own test suite.

## Current numbers

From a clean checkout of v0.01 (2026-09-15):

- **Checker:** 63 of the 259 annotated programs in `ruby-lean/corpus/` are in the
  certified fragment. All 48 typing rules have semantic proofs. The other 196 are
  declined, not wrongly accepted.
- **Model:** on 1309 programs from MRI's `bootstraptest` suite, 995 agree with
  CRuby, 0 disagree, and 308 use something the model does not support yet and
  are reported as unsupported.

## Repository layout

| Path | What it is |
|---|---|
| [`ruby-lean/`](ruby-lean/README.md) | The Lean project: the model, the checker, the proofs, the annotated corpus and the gate |
| [`desugar/`](desugar/README.md) | Ruby source → RubyCore JSON, and the harness that tests that translation against CRuby |
| [`difftest/`](difftest/README.md) | The differential testing engine: program generators, CRuby as the oracle, reports |
| [`playground/`](playground/README.md) | The browser UI |
| [`paper/`](paper/README.md) | Draft paper |
| [`docs/`](docs/index.md) | Longer documentation: design, methodology, what the model supports. Builds as a site with MkDocs |

If you want to change something, read [`CONTRIBUTING.md`](CONTRIBUTING.md) and
[`AGENTS.md`](AGENTS.md) first.

## Limits

- **The typed fragment is small.** The checker accepts 63 of 259 corpus programs.
  Block arguments, `module`, constant assignment and regexp literals are not
  supported yet. Unsupported programs are rejected, not accepted wrongly.
- **The model is incomplete.** It never disagrees with CRuby on the bootstraptest
  suite, but it declines about a quarter of it.
- **"Safe" means one kind of error.** The theorem rules out `NoMethodError`,
  `ArgumentError` and `TypeError`. It says nothing about termination, other
  exceptions, or side effects.
- **Sorbet accepting a program is not the same as this checker accepting it.**
  Sorbet accepts many programs the checker has no rules for yet.
- **Typing Ruby against a real semantics is expensive.** There were four earlier
  attempts at a checker in `RubyCore/` before this one. All were removed; only
  some of their lemmas survive. See [Metatheory](docs/model/metatheory.md).
- **The model's own metatheory is off the default build.** Run
  `ruby-lean/scripts/check-proofs.sh` to build it. It once broke for 24 commits
  without anyone noticing, which is why that script exists.

## Why model only part of the stack

A Ruby semantics can't prove anything certain about a real execution unless the
interpreter, compiler, OS and hardware underneath are also verified. It is still
useful when the question is about code someone else wrote, for example code
written or changed by an AI. That code can only do what Ruby lets it do, so a
faithful model of Ruby covers everything it can do. The interpreter underneath is
shared by everyone and is not the part under review.

What a partial model can be used for:

- **Reviewing changes by meaning.** Show how a diff changes method lookup or the
  heap, which exposes metaprogramming tricks that look harmless in a text diff.
- **Tests derived from the semantics.** For a program and a proposed change,
  check that they behave the same up to some bound, or find an input where they
  differ.
- **Certificates.** Claims like "this program never hits a type error". The
  checker here is the first and narrowest example.

Bounded checking always finishes but only covers executions up to the bound.
Proofs cover every execution but need someone to find an invariant. If the
person submitting a change has to supply the proof, and the reviewer only runs a
small trusted checker, the hard part falls on the submitter. That used to be too
expensive for humans to be practical; capable AI makes it cheaper.

This does not close the gap between the model and CRuby. Proofs make that gap
the only one, which is why the differential tests are permanent. Attacks below
Ruby (the interpreter's supply chain, the hardware) are out of scope.

## History

This repository was extracted from a larger monorepo with `git-filter-repo`, so
the full history of every file is kept (841 commits). Some older notes mention
directories that were left behind; the code, proofs, corpus and gate are complete.

## License

Apache License 2.0. See [`LICENSE`](LICENSE) and [`NOTICE`](NOTICE).
