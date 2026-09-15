# ruby-lean

**An executable semantics for Ruby in Lean 4 — and a typed fragment whose checker
is backed by a proof.**

Two artifacts live here, and the second is built on the first. Both are
libraries of the one Lean project, [`ruby-lean/`](ruby-lean/README.md):

1. **`ruby-lean/RubyCore/` — RubyCore.** A small-step machine plus fuel
   interpreter for a substantial Ruby core, written in Lean 4 and validated
   *empirically* by differential testing against CRuby: every program is run both
   ways and the observations compared. It is not a paper semantics with an
   interpreter beside it; the interpreter **is** the semantics.
2. **`ruby-lean/Ratchet/` + `ruby-lean/Denote/` — the typed ladder.** A checker
   over Sorbet-annotated Ruby whose single trusted output is one Lean `Bool`, and
   a theorem saying that when that `Bool` is `true`, the program cannot get stuck
   on a type error *when run by the semantics in `RubyCore/`*.

Plus **`playground/`**, a browser UI that steps a program through the real
`stepFn` one transition at a time and runs the same source through CRuby beside
it.

> **Version 0.01.** First extracted, self-contained cut of this work. The
> theorems below are proved and the gate below is reproducible; the *fragment*
> they cover is small and growing. See [Status and limits](#status-and-limits)
> before reading any number as a claim about Ruby at large.

---

## The claim, in one line

From [`ruby-lean/Denote/Typed/Bridge.lean`](ruby-lean/Denote/Typed/Bridge.lean):

```lean
theorem validateD_safe_boot {p : Ratchet.Expr} {d : Deriv}
    (h : validateD p d = true) (hb : bootOkB = true) :
    StuckFree bootMachine p
```

where, from [`ruby-lean/Denote/Sem/State.lean`](ruby-lean/Denote/Sem/State.lean),

```lean
def StuckFree (m : Machine) (e : Ratchet.Expr) : Prop :=
  ∀ fuel, Semantics.typeStuck (Interp.run fuel (evalFrom m e)) = false
```

and `typeStuck` is the `NoMethodError` / `ArgumentError` / `TypeError` family,
closed under subclassing, decided on the **real** machine's heap
([`ruby-lean/Semantics/Interp.lean`](ruby-lean/Semantics/Interp.lean)).

Read it as: *acceptance is the safety claim.* There is no gap between "the
checker said yes" and "this program is type-safe under our semantics" that a
human has to bridge — the composition is proved, and the proof is **axiom-clean**
(nothing beyond Lean's own three axioms). Two properties make that statement
worth something rather than vacuous:

* the semantics it quantifies over is the same `stepFn` the differential tests
  run against CRuby — it is a statement about a model that has been *attacked*,
  not one invented to make the theorem easy; and
* the checker is gated by **negative controls** that are `#guard`ed at build
  time, so a checker that accepted everything would fail the build rather than
  pass every rung.

"Axiom-clean" is checked by the build itself, not asserted here — `Bridge.lean`
ends in `#print axioms`, so `lake build` prints

```
'Ratchet.Denote.Typed.validateD_safe_boot' depends on axioms:
  [propext, Classical.choice, Quot.sound]
```

and nothing else. Those three are Lean's own; a `sorry` or a new axiom would
show up in that line, in the log, on every build.

## Where it stands today

Printed by `ruby-lean/scripts/run_typed_ratchet.sh` on a clean checkout of this
repository (v0.01, verified 2026-09-15):

```
pipeline: reach 65 rungs · 252 agree, 0 disagree

259 rungs · fragment 63 (reach 17) · 196 outside
  48 rules certified, 0 owed

RATCHET GREEN
```

| Number | Means |
|---|---|
| **259 rungs** | annotated programs in `ruby-lean/corpus/` |
| **fragment 63** | rungs the certified judgment has rules for — each one's acceptance *is* its safety proof |
| **reach 17** | the unbroken prefix from rung 001; rung 018 is correctly rejected |
| **48 rules certified, 0 owed** | every rule in the judgment carries a semantic proof, so no rung is claimed on an unproved rule |
| **196 outside** | declined, not mis-certified. The gate prints what each one hit: 42 block arguments, 21 `module`, 8 `casgn`, … — that list is the to-do |
| **252 agree, 0 disagree** | the Lean model and CRuby produce identical observations on every stripped program the certificates are about |

`GREEN` is the verdict, and it says *nothing is started and incomplete* — not
that the ladder is finished. Unclimbed rungs are green because nothing claims
them.

And the model itself, against MRI's own `bootstraptest` suite
(`scripts/reproduce.sh --with-difftest`, same checkout, same day):

```
1309 programs ran · 995 agree · 0 disagreements · 308 unsupported
```

`unsupported` is the model declining to guess — a construct outside its
fragment, reported rather than approximated. **Zero disagreements** is the
number that matters: nowhere does the model claim an answer CRuby contradicts.

## What is trusted, and what is not

The pipeline is deliberately lopsided. Four of its five stages can be arbitrarily
wrong without making a wrong answer possible:

| Stage | Tool | Trusted? |
|---|---|---|
| 1. Sorbet signatures | `srb -p symbol-table` via `ruby-lean/scripts/srb_sigs.py` | no |
| 2. Annotation stripping | `difftest/ruby/*_strip.rb` | no |
| 3. Desugar to RubyCore JSON | `harness/desugar-dt/bin/export-json` | no |
| 4. Emit a derivation | `ruby-lean/scripts/emit_deriv.py` | no |
| 5. **Check the derivation** | `validateD`, in Lean | **yes — only this** |

Stages 1–4 *generate* a candidate certificate. Stage 5 *checks* it, and only its
`true` is licensed by the theorem above. A bug upstream costs you an accept you
could have had (a false *reject*), never an unsound one.

## Install

Five external tools, all off-the-shelf.

```sh
# Lean (the toolchain version itself is pinned by */lean-toolchain — elan fetches it)
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh

# CRuby — the differential-testing oracle (validated against 4.0.x)
brew install ruby

# Sorbet — stage 1 of the typed pipeline
gem install sorbet sorbet-runtime

# uv — runs the difftest engine
brew install uv        # or: curl -LsSf https://astral.sh/uv/install.sh | sh
```

Then check all five at once:

```sh
scripts/check-prereqs.sh
```

It prints what it found, and for anything missing, the command that installs it.
`$RUBY` and `$SORBET` override the auto-discovery if you keep them somewhere
unusual.

## Build

```sh
cd ruby-lean && lake build   # the model + the `rubycore` SUT binary,
                             # the checker, its proofs, and the runners
```

One Lake package, four libraries — `RubyCore` (the model), `Ratchet` (the
checker), `Semantics` (the one import of the real machine) and `Denote` (the
denotation that joins them). The checker therefore always speaks about whatever
the model currently does: there is no second, driftable copy of the semantics,
and `Ratchet/` still imports nothing from `RubyCore/` (enforced by
`ruby-lean/scripts/check-isolation.sh`, which the gate runs first). The first
build fetches two Lean dependencies (`plausible`, `iris-lean`) into the manifest;
neither is on the default target, and neither is needed for anything on this page.

On a cold cache expect a few minutes for the model and on the order of half an
hour for the rest — the bulk of it is elaborating `Denote/`, which is where the
semantic proofs live. Incremental rebuilds are seconds.

## Reproduce

One command runs the whole thing in order and stops at the first failure:

```sh
scripts/reproduce.sh                   # build + the typed ratchet gate
scripts/reproduce.sh --with-difftest   # also: model vs CRuby over MRI's bootstraptest
                                       #   (harvests the corpus on first run: one sparse
                                       #    clone of ruby/ruby into $RUBY_SRC or /tmp)
scripts/reproduce.sh --with-proofs     # also: the metatheory + `#print axioms`
                                       #   (known red — see Status and limits)
```

The gate itself is the thing to run if you only run one:

```sh
cd ratchet && ./scripts/run_typed_ratchet.sh          # quiet: the verdict + what's next
cd ratchet && ./scripts/run_typed_ratchet.sh --verbose # every stage's output
```

Its last line is **GREEN** or **RED**, and the distinction is the point:

* **GREEN** — nothing is started and incomplete. Every registered rule has a
  semantic proof, every floor holds, the model agrees with CRuby on every
  stripped program, and reach has not dropped. Rungs nobody has climbed yet are
  GREEN: they are not *claimed*.
* **RED** — the fragment is claiming something the bridge cannot back: a rule
  with no semantic proof, a worked theorem about the wrong program, a shrunk
  fragment, a moved floor.

Useful knobs: `RATCHET_SKIP_AGREEMENT=1` skips the CRuby replay (fastest useful
run); in a sandbox with a protected uv cache, set
`UV_CACHE_DIR=/private/tmp/ruby-ratchet-uv-cache`.

Other reproductions, each a single command:

```sh
# the model against MRI's bootstraptest corpus, through the difftest engine.
# The corpus is harvested, not vendored — one sparse clone, once:
git clone --depth 1 --filter=blob:none --sparse https://github.com/ruby/ruby /tmp/ruby-src
(cd /tmp/ruby-src && git sparse-checkout set bootstraptest)
harness/desugar-dt/bin/harvest_bootstraptest /tmp/ruby-src/bootstraptest
cd difftest && uv sync && uv run python -m difftest run --tier 0 --sut lean

# run one program through the model by hand
echo 'puts 1 + 2' | ruby harness/desugar-dt/bin/export-json | ruby-lean/.lake/build/bin/rubycore

# the metatheory, and a re-check that the headline theorems are axiom-clean
cd lean && ./scripts/check-proofs.sh
```

### The playground

```sh
cd lean && lake build && cd ../ratchet && lake build validate-one   # once
cd ../playground && python3 server.py                               # http://localhost:8077
```

Python stdlib only — no dependencies. Tab 1 steps a program through `stepFn`
(with a step window, and breakpoints that match the rendered control) and runs
the same source in CRuby for comparison; tab 3 drives the five ratchet stages
over any corpus rung, one artifact at a time, with the derivation editable
before the trusted check. See [`playground/README.md`](playground/README.md).

## Layout

| Path | What it is |
|---|---|
| [`ruby-lean/`](ruby-lean/README.md) | The Lean project — one Lake package, and everything below is a directory in it. Working notes live in `ruby-lean/notes/`; the agent-facing state is [`ruby-lean/AGENTS.md`](ruby-lean/AGENTS.md). |
| `ruby-lean/RubyCore/` | **RubyCore**: `Syntax`/`Heap`/`Machine`/`Builtins`/`Interp` (`stepFn` + `run fuel`), the Ruby-authored `prelude/`, the `rubycore` SUT binary, and `RubyCore/Proof/` (metatheory, incl. type-safety-by-reachability). Off-default targets: `Metatheory`, `Judgment`, `HJudge`. |
| `ruby-lean/Ratchet/`, `Semantics/`, `Denote/` | The typed ladder: `Ratchet/` (the checker — its own copied `Expr`/`Ty`, `Deriv`, `validateD`; imports nothing from `RubyCore/`), `Semantics/` (the real machine, imported), `Denote/` (the semantic denotation and the bridge — the one library that imports both). With `corpus/` (annotated rungs) and `scripts/` (the untrusted pipeline + the gate). |
| [`difftest/`](difftest/README.md) | The differential engine: tiered generators, the CRuby oracle, `replay`, and the strip transforms the ratchet reuses. |
| [`harness/desugar-dt/`](harness/desugar-dt/) | Ruby → RubyCore JSON (`export-json`), the front end for everything here. |
| [`playground/`](playground/README.md) | The browser stepper and the live ratchet pipeline. |
| [`docs/`](docs/) | The written semantics and the design record — see [`docs/README.md`](docs/README.md). |

## Status and limits

Read these before quoting a number.

* **The fragment is small.** `validateD` accepts a *prefix* of the corpus, not
  Ruby: 63 of 259 rungs today, and block arguments, `module`, constant
  assignment (`casgn`) and regexp literals are all still outside it. Everything
  outside is *declined*, not mis-certified — which is the design, but it means "certified type-safe" here
  is a claim about a slice.
* **The model is a model.** It agrees with CRuby wherever it answers (0
  disagreements over 1309 bootstraptest programs) but it declines 308 of them —
  roughly a quarter of the suite is outside its fragment. What is modeled, and
  what is not, is listed in [`ruby-lean/README.md`](ruby-lean/README.md).
* **Safety means one family.** `StuckFree` rules out reaching
  `NoMethodError`/`ArgumentError`/`TypeError`. It is not a claim about
  termination, about other exceptions, or about effects.
* **Sorbet's verdict is not this repo's verdict.** `srb` clean with
  `validateD = false` is an ordinary, expected combination: Sorbet accepts many
  programs the certified fragment has no rules for yet.
* **One metatheory file does not build.** The off-default `Metatheory`
  target currently fails in `RubyCore/Proof/Static/Preservation.lean` (three
  broken proofs), so `scripts/check-proofs.sh` — and therefore
  `scripts/reproduce.sh --with-proofs` — exits non-zero. This is drift, not a
  false claim: `Proof/` is off the default build target precisely because
  nothing the SUT or the ratchet does depends on it, which is also why it rots
  unnoticed. **Nothing on this page depends on it.** The headline theorem
  `validateD_safe_boot` and every proof under `ruby-lean/Denote/` are on the
  default target, build clean, and print their axioms on every build. (A related
  break in `Proof/Static/Iter.lean` was repaired for this release — see
  `CHANGELOG.md`.)
* **`ruby-lean/build/` is derived.** It is regenerated from `corpus/*.rb` by the
  pipeline; the annotated `.rb` is the source of truth.

`ruby-lean/AGENTS.md` and the `ruby-lean/notes/` files (`implementation-notes.md`,
`found-issues.md`, `HANDOFF.md`, per layer under `notes/model/` and
`notes/ratchet/`) are the working record: what was tried, what broke, and which stall points
cost days. They are kept deliberately — the negative results are half the
content.

## Provenance and history

This repository is a subtree extraction from the "Semantics Done Quick"
monorepo, taken with `git-filter-repo` so that **the full commit history of
every file is preserved** — 841 commits, from the first differential-test engine
through the current typed ladder. `git log --follow` works across the move.

Paths were rewritten (`sam-xif/ruby/X` → `X`); sibling investigations that this
work does not depend on (the POSIX investigation, the Homebrew slice explorer's
backing tools, exploratory spikes, the session journals) were left behind. Some
historical notes in `*-notes.md` therefore reference directories that are not
here; the code, the proofs, the corpus and the gate are complete and
self-contained.

## License

Apache License 2.0 — see [`LICENSE`](LICENSE) and [`NOTICE`](NOTICE).
