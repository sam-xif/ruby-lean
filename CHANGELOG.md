# Changelog

All notable changes to this project are documented here. Versions follow a
simple "how finished is it" scale rather than semver: this is a research
artifact, and `0.01` is the first cut of it that a stranger can build.

## 0.01 — 2026-09-15

First self-contained release. Extracted from the "Semantics Done Quick"
monorepo with full per-file commit history preserved (841 commits).

**What works**

* **The model** (`lean/`) — a small-step machine and fuel interpreter for a Ruby
  core, running as the `--sut lean` system under test in the differential
  engine: L0–L2 core, a prelude carrying part of Ruby's core library written *in*
  RubyCore, the reflective metaprogramming core, `defined?`, class variables,
  `catch`/`throw`, and visibility.
* **The checker** (`ratchet/`) — `validateD`, one trusted Lean `Bool` over a
  derivation emitted by an untrusted pipeline, with
  `validateD_safe_boot : validateD p d = true → bootOkB = true → StuckFree bootMachine p`
  proved axiom-clean in `Denote/Typed/Bridge.lean`. Acceptance *is* the safety
  claim; there is no second reach number and no per-rung obligation owed.
* **The gate** (`ratchet/scripts/run_typed_ratchet.sh`) — the five-stage pipeline,
  the negative controls, the CRuby/model agreement replay and the safety
  cross-check, in one command with a GREEN/RED verdict.
* **The metatheory** (`lean/RubyCore/Proof/`) — progress/preservation by
  reachability (`invariant_sound`) over the full `stepFn`, plus the judgment
  layer and its semantic and higher-order (Iris) extensions, each on its own
  off-default build target.
* **The playground** (`playground/`) — a browser stepper over the real `stepFn`,
  a CRuby comparison, the static checkers, and a live view of all five ratchet
  stages with the derivation editable before the trusted check.

**Packaging added in this release**

* Root `README.md` with install, build and reproduction instructions.
* `scripts/check-prereqs.sh` — checks the five external tools and says how to
  install what is missing.
* `scripts/reproduce.sh` — build and gate in order, with optional difftest and
  metatheory passes.
* `docs/README.md` — a reading order for the design record.
* Apache-2.0 `LICENSE` and `NOTICE`.

**Fixed**

* `lean/RubyCore/Proof/Static/Iter.lean` — `startArgs_lambda` was stated without
  the non-shadowing hypothesis and its `rfl` had silently stopped holding when
  the model learned that a user `def lambda` shadows `Kernel#lambda`
  (`found-issues.md` §A5). Restated with the hypothesis `mkLam` actually needs,
  and proved. It went unnoticed because `Proof/` is off the default build
  target — the failure mode `scripts/check-proofs.sh` exists to catch.

**Known limits** — the certified fragment is a prefix of the 259-program corpus,
not Ruby; `StuckFree` covers the `NoMethodError`/`ArgumentError`/`TypeError`
family only; `lean/`'s off-default `Metatheory` target still fails in
`RubyCore/Proof/Static/Preservation.lean` (three broken proofs, so
`--with-proofs` exits non-zero — nothing on the default target or in the
ratchet's proof chain depends on it); the playground's Homebrew-slice tab is
disabled here because its backing tools were not part of the extraction. See the
root README's *Status and limits*.

**Measured on a clean checkout, 2026-09-15** — ratchet gate GREEN (259 rungs,
fragment 63, 48 rules certified, 0 owed, 252 agree / 0 disagree); tier-0
difftest 1309 programs, 995 agree, 0 disagreements, 308 unsupported.
