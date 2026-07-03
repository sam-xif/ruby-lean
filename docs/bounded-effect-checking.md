# Bounded effect checking at commit time

Design sketch for operationalizing **US3** of [`user-stories.md`](user-stories.md): a
**semantics-based bounded model checker running as a CI gate**, verifying confinement (or
another safety property) for a given program *as code changes are committed*. The
interesting design decisions are (a) what is symbolic, (b) how verdicts are staged, and
(c) how per-commit cost is made to track **diff size rather than program size**.

Status: design only — nothing here is built. It consumes artifacts we do have (the desugar
front end, the `obs⁺` harness) and ones we plan (the Lean step relation + fuel
interpreter, a POSIX-layer effect model).

---

## 1. The property: a policy manifest, checked where effects surface

Confinement is stated as a **capability manifest** checked into the repo:

```yaml
# .effects.yaml
entrypoint: bin/worker
may:
  fs.read:  [config/**, /etc/ssl/**]
  fs.write: [tmp/**, log/**]
  net.connect: [db.internal:5432]
deny_all_else: true
```

In the model, effects are not ambient — they surface as **specific step-relation rules**
(sends to modeled IO builtins in RubyCore; syscall transitions in a POSIX-substrate
model). "Check the policy" therefore means: at every effect-emitting rule the search
encounters, ask whether the effect's arguments can violate the manifest under the current
path condition.

The manifest being diffable text is load-bearing: a commit that needs a new capability
must also touch the manifest — exactly the moment a human (or reviewing agent) should
look.

## 2. The engine: concolic execution of the step relation

Lift the fuel interpreter's `Config` over symbolic terms plus a path condition.

- **Concolic, not purely symbolic.** Run the program's *boot phase* (requires, class
  definitions, all metaprogramming) fully concretely, producing a concrete heap `H` with
  settled method tables. Symbolize only the **inputs**: argv, stdin, env, and file/DB
  contents behind the modeled FS interface. Pure symbolic execution over Ruby strings and
  heaps drowns immediately; concolic-with-concrete-boot is the pragmatic center, and is
  sound for this purpose because dispatch resolves against the real booted heap.
- **Fork on branches**; an SMT solver prunes infeasible paths. At each effect rule, emit
  the query `pathCondition ∧ effect ∉ policy` — SAT yields a **concrete witness input**.
- **Bounds as explicit dials**: fuel per path (k₁), path/branch budget (k₂), input-data
  sizes (k₃ — string lengths, collection sizes), solver timeout. This is the verified
  frontier of `user-stories.md` §5, as config knobs.
- **Witnesses are confirmed outside the model**: shrink the input (delta debugging;
  cf. shrinkray, cited in the 2026-06-30 meeting notes), then run it against real CRuby in
  a syscall-tracing sandbox (`strace`/dtrace) and observe the actual violation. A
  confirmed witness is *model-independent*. A witness-in-model that fails to reproduce in
  reality is a **model bug** — routed to the differential-testing ratchet.

**Relation to prior art.** This is KLEE's shape (symbolic execution of coreutils with a
modeled environment, OSDI'08) with two upgrades KLEE could not have: the executor is a
*semantics*, so coverage is measured in semantic rules — where Ruby backdoors hide — and
the environment model (FS state) can itself be symbolic. A SibylFS-style tree model lets
the checker ask "does there *exist* a filesystem state under which this write escapes
`tmp/`?" — the symlink-trickery question. That is where the
[`posix/`](posix/AGENTS.md) investigation plugs in: the POSIX layer is the checker's
**policy vocabulary and symbolic environment**, not a separate project.

## 3. Verdicts: three-valued, with the frontier as first-class output

Per entrypoint, per commit:

| Verdict | Meaning | CI action |
|---|---|---|
| **VIOLATION(witness)** | shrunk, real-execution-confirmed repro | block merge, attach repro |
| **VERIFIED(k₁,k₂,k₃)** | no witness within bounds — bounds are part of the verdict, never elided | pass; record frontier |
| **UNKNOWN(frontier report)** | *which* paths were truncated and *why*: fuel exhausted here, solver timeout there, **unmodeled construct** at this site | pass/fail by policy; always report |

Out-of-fragment code (the desugarer's `Unsupported`, exactly) is treated conservatively as
"may emit anything" — which either fails the policy or forces an explicit, reviewable
escape-hatch entry in the manifest. The harness's **fragment-coverage ratchet thereby
doubles as a security metric**: the fraction of the codebase whose effects are analyzable
at all.

The adversarial framing demands UNKNOWN be loud, not silent: the report is "here is where
we did not look," because that is precisely where an adversary will put things.

## 4. Incrementality: making per-commit cost track the diff

Naively re-searching the whole state space per commit dies immediately. Two mechanisms;
the second is where the object-model design pays off unexpectedly.

### 4.1 Summaries with diff-directed invalidation

The Infer playbook (compositional analysis on Meta-scale diffs): for each method, cache an
**effect summary** — effects it can emit, under what argument/path conditions, valid up to
bounds. Per commit, re-analyze only changed methods and re-propagate to dependents;
unchanged callees contribute cached summaries instead of being re-explored.

### 4.2 Semantic diffing via the booted heap

The Ruby wrinkle: "which methods changed" is **not syntactic** — a diff adding a `prepend`
or a `define_method` changes dispatch at call sites in files it never touched. The model
makes this tractable rather than fatal: **boot both versions and diff the resulting
heaps** — method tables, ancestor chains, dispatch-lookup results. The invalidation set is
"call sites whose lookup outcome changed," computed from the *heap delta*, not the text
delta.

This falls directly out of the everything-is-heap-mutation design and is something a
syntactic tool cannot do: a metaprogramming-based backdoor *is* a heap delta, and shows up
as one even when the textual diff looks inert. (This also implements US2 of
`user-stories.md` — the semantic diff review — as a byproduct.)

## 5. Trust story: certifying, not trusted

The search engine wants to be fast (extracted OCaml/Rust, not `#eval` in Lean). Keep it
**out of the trusted base** by making it *certifying*: it emits a replayable certificate
(the explored tree, per-path solver artifacts, a justification for each VERIFIED claim)
that a small Lean checker validates against the inductive step relation. The CI trust base
is then the Lean kernel plus solver proof-checking; the engine can be arbitrarily clever
and buggy.

This gives clean continuity with the proof-carrying-code story (`user-stories.md` §5):
**PCC for unbounded claims when the submitter provides invariants; certified bounded
search as the automatic floor when they don't.** Same relation, same checker, two effort
levels.

## 6. The commit-time pipeline, end to end

1. **Desugar** changed files → RubyCore (the existing harness front end, verbatim).
2. **Boot** old and new versions → heaps `H`, `H′`; compute the **semantic diff**
   (dispatch-relevant heap delta, §4.2).
3. **Invalidate** summaries for changed methods + dispatch-shifted call sites; identify
   affected entrypoints. *Diff that cannot reach any effect site → fast-pass.*
4. **Search**: bounded concolic execution from affected entrypoints (§2), cached summaries
   elsewhere; policy queries at effect rules (§1).
5. **Violations** → shrink → confirm on real CRuby under syscall trace → block, repro
   attached.
6. **Report**: verdict + **frontier delta vs. previous commit** — did analyzability
   regress? did any previously-VERIFIED bound shrink? The ratchet, as a merge check.
7. **Nightly**: raise bounds with a larger budget; refresh summaries; run adversarial
   difftest on the same corpus to keep hammering model fidelity.

## 7. Honest hard parts, ranked

1. **Path explosion through dynamic dispatch** — mitigated by concrete boot + summaries,
   but real; receiver-type ambiguity multiplies paths.
2. **Symbolic string reasoning** — Ruby is string-saturated; SMT string theories are
   usable but brittle. Expect solver timeouts to dominate the UNKNOWN set early.
3. **Model fidelity** — everything upstream inherits it (`user-stories.md` §7). The
   difftest harness is the permanent foundation, not scaffolding to discard.

## 8. What this implies for sequencing

The *product* is the checker; the Ruby semantics is its **executor**; the POSIX layer is
its **policy vocabulary and symbolic environment**. One system, not two candidate targets.
Concretely testable milestones on the way: (a) the semantic heap-diff (§4.2) is buildable
against the current harness *before* any Lean exists — boot two program versions under
CRuby, dump method tables via reflection, diff; (b) a toy concolic stepper over RubyCore
with a hand-rolled path condition on integers only, checked against `obs⁺`, would
de-risk §2 cheaply.
