# Reproducing the DRuby results — the first reportable bug-finding campaign

**Status: plan.** Execution plan for the headline result:

> On the DRuby featured corpus (Furr & Foster, *Static Type Inference for Ruby*, SAC'09),
> rediscover the documented type errors **with zero false positives by construction**,
> ship every bug as a replayable witness + CRuby confirmation + machine-checked Lean
> theorem, and report new bugs found along the way.

Builds directly on prior writing — read these first, this doc only adds the campaign:

- [`../../type-safety-by-reachability.md`](../../type-safety-by-reachability.md) §9 —
  the corpus, tiers, and the measured gate histogram (§9.0).
- [`../concolic/README.md`](../concolic/README.md) — the engine, its trust model, its
  honest limitations.
- [`../typecheck-pipeline/README.md`](../typecheck-pipeline/README.md) — the
  codebase-agnostic discover→desugar→link→lift pipeline (adding a repo = a `config/`
  file + an `ASSUMPTIONS` doc, no shared code).
- [`../typecheck-pipeline/findings/2026-08-01-ai4r-qlearning-nil-policy.md`](../typecheck-pipeline/findings/2026-08-01-ai4r-qlearning-nil-policy.md)
  — the proof-of-concept finding, **including the measured division of labour** (engine
  found the bug class in 2 iterations; 21 of 25 branch conditions went `opaque` on Hash
  ops; the natural trigger needed a human). This campaign is largely about closing that
  measured gap and industrializing that finding's shape.
- [`semantics/search-and-proof.md`](semantics/search-and-proof.md) §8 — the ranked
  engine work items this plan schedules.

Origin: 2026-08-03 design conversation — the decision to sequence bug-finding (search +
coverage) ahead of the lemma library ([`semantics/lemma-library.md`](semantics/lemma-library.md)),
and to make the semantics' role in *acceleration* (not just replay) the paper's
methodological content.

---

## 1. The claim, stated carefully

DRuby's SAC'09 numbers on the featured corpus: **5 errors / 16 warnings / 16 false
positives** across 18 programs (29–1030 LOC). Our claim is *not* "we beat DRuby at its
own game" — DRuby is a static inference tool and flags inconsistencies; we are a
semantics-driven reachability checker and report **reachable** errors with witnesses.
The comparable set is the **documented bugs**: for each one, either

- **found**: a concrete input whose run reaches the type-stuck (or, per §4, bad-state)
  outcome — confirmed on CRuby, certified in Lean (`runTypeStuck_unsafe` /
  `run_typeError_unsafe`: the theorem `∃ r, ReachableResult … ∧ typeStuck r`,
  axiom-clean); or
- **out of fragment**: an honest `unsupported`/UNKNOWN with the gate named (the
  three-valued discipline — `text-highlight` is *expected* to land here; DRuby punted
  on it too).

And the differentiator is structural: **zero false positives by construction** (every
report replays), where DRuby's 16 FPs came from union types discriminated by runtime
tests — exactly what path-sensitive execution of the real `is_a?`/`respond_to?` prunes
for free.

Secondary claims, each already demonstrated once and needing only repetition at scale:

1. **New bugs**, not just reproductions (the ai4r `choose_action` nil-policy finding is
   the first; its finding-doc format is the template).
2. **Every result is a theorem** — no fuzzer or static analyzer ships that artifact.
3. **The semantics accelerates the search**, it doesn't just referee it (§6).

## 2. What exists — build on, do not re-plan

| Asset | State | Role here |
|---|---|---|
| Concolic engine (`concolic/`) | 5 demo programs, generational search, witnesses in 2–5 Lean runs, replay + CRuby confirmation, self-checking shadow | the search core |
| Pipeline (`typecheck-pipeline/`) | discover/desugar/link/lift working; ai4r: 50/58 files desugar, 7/36 drivers link, 3 run to byte-exact values | corpus onboarding — per-repo `config/` + `ASSUMPTIONS` |
| ai4r vendored + one finding | confirmed on CRuby 4.0.5 + Lean byte-identical | flagship target; finding template |
| Gate histogram (t-s-b-r §9.0) | measured 2026-07-30: `defined?` 36, `zsuper` 29, `Array#[]` slice 28, … | the coverage worklist, histogram-driven |
| Prelude mechanism (landed, WIP on branch) | core library written in RubyCore, loaded at boot (Enumerable, Range enumeration, Comparable, Hash overrides) | changes the coverage economics (§5.1) |
| `Search/Random.lean` (Phase 1) | shallow witnesses + shrinking | cheap first pass per target |
| Direction-B proofs (`T5Loop`, `DispatchLoop`) | proved, axiom-clean | the prove-safe subset's upgrade path |

## 3. Corpus acquisition and ground truth (M0)

Ten programs, from t-s-b-r §9.3. **Ground truth comes first**: before any model work,
manually reproduce each documented bug on CRuby at a pinned version — that defines
"done" per target and surfaces version archaeology early.

| Program | LOC | Documented bug | Our bad-state class | Source |
|---|---|---|---|---|
| hashslice | 91 | `@hash['a','b'] = 3,4` parses as 3 args → arity | `ArgumentError` ✓ in family | RubyForge mirror / IA |
| vimrecover | 173 | undefined vars in error-recovery branches | `NameError` — **§4 work item** | RubyForge mirror / IA |
| ObjectGraph | 153 | `break k` from `each_object` returns `Class` vs `Fixnum` → downstream `NoMethodError` | `NoMethodError` ✓ | RubyForge mirror / IA |
| ai4r | 992 | `return rule_not_found if …` — undefined var on untested branch | `NameError` — **§4** | vendored ✓ |
| StreetAddress | 877 | none (prove-safe) | — | live gem |
| text-highlight | 1030 | `eval`-metaprogramming; DRuby punted | expected UNKNOWN | RubyForge mirror / IA |
| pscan / merge-bibtex / style-check / gs_phone | 29–827 | none (DRuby 0/0/0) | prove-safe / exhausted-within-bounds | RubyForge mirror / IA |

Mechanics per program: `bin/fetch-<name>` + `config/<name>.rb` + `ASSUMPTIONS-<name>.md`
(the pipeline was built codebase-agnostic for exactly this). Pin the version DRuby
analyzed (SAC'09 Fig. 1); later releases may have fixed the bugs.

**Honest hard part — 1.8 archaeology.** The RubyForge-era programs target Ruby 1.8:
syntax Prism may reject (`when …:` colons), stdlib that no longer exists (`ftools`),
1.8 `String` semantics. Policy: **modernize minimally, diff-disclosed** — each
`ASSUMPTIONS-<name>.md` carries the exact patch, and the documented bug's mechanism must
be untouched by it (checked by reproducing the bug on both the pristine tree under an
old Ruby if obtainable, and the patched tree under modern CRuby). If a program's bug
*is* a 1.8-ism, report it as out of scope rather than force it.

## 4. The bad-state predicate must widen — `NameError`

Two of the four documented bugs (ai4r, vimrecover) are **undefined-variable
`NameError`s**, deliberately outside `typeErrorFamily` (t-s-b-r §2), and the model
currently *gates* the vcall/fcall `NameError` path to `unsupported`. Two work items,
both known and neither large:

1. **Model:** un-gate the undefined-identifier path so it raises a real `NameError`
   in-model (difftest-ratcheted like everything else — CRuby fixes the message bytes).
2. **Checker:** make the family a **campaign parameter**. This was always the thesis
   ("one checker, pluggable bad-state predicate" — search-and-proof §6.1); this is its
   first exercise. Concretely: `ConcolicMain` takes `--bad-state
   type|type+name|<class list>`; `typeStuck` in Lean is already generic modulo the
   family list. Report tables then say which predicate each result used — DRuby's
   "error" category maps to `type+name`.

## 5. Coverage plan — what must run before anything can be found

Per-program desugar coverage is the pipeline's first output; the campaign's coverage
work is histogram-driven, never speculative (t-s-b-r §10.3's standing rule: re-measure
after each batch).

### 5.1 The prelude changes the economics — measure it first

The prelude mechanism (core library written in RubyCore, loaded at boot) means many
"missing builtins" are now **Ruby code, not Lean work** — and prelude methods are user
code to the model, so the shadow traces *through* them. Open measurement, scheduled
early because it may re-rank everything: **how much of the gate histogram falls to
prelude implementations**, and does routing (e.g.) `Hash#empty?`/`Array#any?` through
prelude bodies over primitive ops make previously-`opaque` conditions solvable without
theory-of-arrays? (The ai4r finding's decisive guard was exactly `@q[state].empty?`.)
Do not assume — run the ai4r trace again after the prelude lands and count solvable
branches (this is search-and-proof §8's "re-measure ai4r" milestone, sharpened).

### 5.2 The known worklist (from the measured histogram)

In order, updated for the prelude: `defined?` (36, desugar-side) → `Array#[]` slice
(28) → Enumerable predicate family + Range enumeration (**prelude-first now**) →
`zsuper` param reconstruction (29) → `Struct` (16, needed by ObjectGraph-era code) →
Regexp (17 — gates StreetAddress/style-check; deferred, those targets sequence last).

### 5.3 Per-target mocks

- ObjectGraph: `ObjectSpace.each_object` — an **L3 effect-labeled mock** (iterate a
  fixed collection of booted-heap classes; the bug is in the `break`-vs-normal-exit
  return type, which survives mocking). Entry in the mock manifest, diffable.
- vimrecover: file-system probes → L3 mocks returning typed/symbolic results.
- ai4r: per the existing ASSUMPTIONS doc (CSV/Marshal/Random seams).

## 6. Engine work — the accelerators, in order

Ranked by (value ÷ cost) for *this campaign specifically*; the first three are
search-and-proof §8 items, the last three are the "leverage the model" items from the
2026-08-03 discussion. Each lands with a measured before/after on a corpus program.

1. **Exponential trip-count probing** (~20 lines) — several corpus programs iterate
   over input-sized data; linear unrolling is the measured weakness (Finding 4).
2. **Finite-domain splitting as directed goals** — enumerate hash-key / class-tag /
   symbol domains read off the concrete machine state, queue one goal per case
   (reuses `DispatchRisk`). **This is the projected fix for the ai4r natural trigger**:
   `@q[state]`'s domain is the concrete key set. The M3 experiment (§8) decides whether
   theory-of-arrays is needed at all this campaign.
3. **Boot snapshotting** — serialize the booted `Machine` once per target, start every
   search iteration from it. Linked ai4r drivers boot the whole library per run today;
   this is a large constant factor on every target and pure engineering (the machine is
   a Lean value).
4. **Speculative look-ahead (semantic target discovery)** — at each un-taken branch,
   fork the machine, step k steps, test `aboutToTypeStick` on speculative states;
   solver goals are then *aimed at discovered bad states* rather than blind coverage.
   The novel search move; the paper's methodological centerpiece.
5. **Heap-derived target ranking** — cross booted method tables against the program's
   send sites; rank sites whose receiver's candidate classes don't all respond. Triage
   for where to point the harness first on the 900+ LOC targets.
6. **Finite-difference analytic jumps** (search-and-proof §4.1) — only if a corpus
   program actually presents an accumulator-guarded branch; do not build speculatively.

## 7. Per-target campaign shape (the repeatable unit)

For each program, in order — this is the ai4r finding industrialized:

1. **Ground truth** (M0): documented bug reproduced manually on pinned CRuby.
2. **Coverage**: `bin/pipeline <name>` → gate histogram → close gates per §5 → linked
   driver runs under `bin/lift` (byte-exact where it completes).
3. **Harness**: a driver with inputs parameterized as `$__inK`. Authorship policy
   (bias disclosure, learned from ai4r): the harness may parameterize *which inputs the
   program receives*, never *what the program does*; the finding doc records the
   harness verbatim and states what was human-chosen. Where the documented bug is in a
   library API, the harness is the shipped example driver plus the most natural
   parameterization — as in the ai4r case.
4. **Search ladder**: `Search/Random.lean` first (shallow, free) → concolic
   (`bin/find-witness`) with the §6 accelerators → if stalled, read the frontier notes
   (they name the missing precision — that's the next §5/§6 work item, demand-driven).
5. **Confirm + certify**: CRuby replay (model-independent) + plain-`rubycore`
   observation path + the Lean certificate theorem. Shrink the witness.
6. **Report**: a finding doc in `typecheck-pipeline/findings/` on the 2026-08-01
   template — including the division-of-labour section (what the engine found, what a
   human added) and the frontier account (which conditions were unflippable and why).
7. **Regressions**: witness programs join the difftest regression corpus; the search
   run joins CI as a re-runnable artifact.

## 8. Milestones

| | Milestone | Exit criterion |
|---|---|---|
| **M0** | Corpus + ground truth | 10 programs fetched, pinned, configured; each documented bug reproduced manually on CRuby; 1.8 patches disclosed in ASSUMPTIONS docs |
| **M1** | Predicate + coverage base | `NameError` un-gated + pluggable family (§4); `defined?` + `Array#[]` slice landed; prelude coverage measurement done (§5.1); per-program gate histograms published |
| **M2** | Engine quick wins | exponential probing + boot snapshotting landed, with measured speedups on `loop_sum` and a linked ai4r driver |
| **M3** | **The ai4r experiment** | finite-domain splitting over hash keys: does the search find the `choose_action` natural trigger end-to-end, no human step? This re-measures the 4/25-solvable number and **decides the theory-of-arrays question** for the campaign |
| **M4** | The bug ladder | hashslice (smallest real bug) → vimrecover → ObjectGraph (best full-loop demo) → ai4r (flagship). Each: witness, CRuby confirmation, Lean theorem, finding doc |
| **M5** | The safe side | pscan/merge-bibtex/style-check/gs_phone: exhausted-within-bounds verdicts with the bound frontier reported; **one** upgraded to a Direction-B invariant proof (the contrast the paper needs); StreetAddress if regex permits, else deferred with the gate named |
| **M6** | Write-up | results table vs DRuby Fig. 1 (found / out-of-fragment / new-bugs / FP=0), findings docs, certificates, replayable artifact |

Sequencing constraints, not calendar: M3 gates nothing (M4 can start on hashslice with
M1 alone) but decides the biggest open engineering question, so it runs as early as its
inputs (prelude + splitting) exist. `text-highlight` needs no work at all — it is
onboarded in M0 and reported as the honest UNKNOWN.

## 9. Risks, ranked

1. **1.8 archaeology** (§3) — could disqualify individual programs; mitigated by the
   disclosure policy and by the corpus being 10 wide (the claim survives losing one or
   two, stated honestly).
2. **The M3 experiment fails** — hash-key splitting doesn't reach the natural trigger →
   theory-of-arrays over the object store enters the critical path (concolic-dataflow
   §8.2), a real project. Fallback for the paper: report the 2-iteration bug-class
   finding + human trigger as-is (already a result), keep ai4r's full automation as
   future work.
3. **String-guarded branches** — the parsers are string-saturated; expect unflippable
   frontiers. Mitigation: sequence those targets last (M5), report frontiers loudly;
   cvc5 string theory is out of scope this campaign.
4. **Harness-authorship criticism** — "you wrote the driver that crashes." Mitigated by
   the §7.3 policy, verbatim harnesses in finding docs, and the shipped-driver-plus-
   natural-extension pattern the ai4r finding established.
5. **Version-pinned bugs already fixed upstream** — fine for reproduction (we pin), and
   upstream-reporting the still-live ones (ai4r) is its own small result.

## 10. What this yields for the paper

The results table has four columns per program — *documented bug found (witness +
theorem) / new bugs / out-of-fragment (gate named) / false positives (identically 0)* —
against DRuby's error/warning/FP triple. The methods section is §6: constraints emitted
from inside the semantics, targets discovered by speculatively stepping it, domains
enumerated from its concrete state, and every finding certified as a kernel-checked
theorem — with CRuby appearing exactly once per finding, as the reality check. The
lemma library ([`semantics/lemma-library.md`](semantics/lemma-library.md)) is explicitly
*not* on this critical path; it is the following paper's machinery.
