# docs

The written record behind the code: what the semantics says, why it is shaped
that way, and what the whole thing is *for*. Nothing here is generated from the
Lean sources — these are design artifacts, some of them ahead of the code and
some of them behind it. Where the two disagree, the code in
[`../ruby-lean/`](../ruby-lean/) — the model and the checker alike — is what runs.

## Start here

| Document | What it gives you |
|---|---|
| [`semantics/README.md`](semantics/README.md) | **The semantics itself**, artifacts 00–06 in reading order: notation and abstract syntax, the object model and heap, dispatch and MRO, scope and constants, blocks/procs/control flow, the differential-testing methodology, and desugaring. |
| [`semantics/lean-model-sketch.md`](semantics/lean-model-sketch.md) | The bridge from those artifacts to Lean 4 — what was adopted from the prior art, what was rejected, and the fragment ladder. |
| [`type-safety-by-reachability.md`](type-safety-by-reachability.md) | The idea underneath the ratchet (`ruby-lean/Ratchet/`): "type-checking" a program by *executing the semantics* and asking whether any path reaches a type-stuck outcome — no type system required. Witness-finding vs. verification. |
| [`semantics/certificate-language.md`](semantics/certificate-language.md) | The certificate discipline: untrusted generation, one trusted checker, and why the boundary is drawn where it is. |
| [`semantics/answer-typed-judgments.md`](semantics/answer-typed-judgments.md), [`answer-typed-schema.md`](semantics/answer-typed-schema.md) | The judgment form the current ladder's derivations are written in. |
| [`semantics/judgment-layer.md`](semantics/judgment-layer.md) | The J-milestones: the declarative judgment layer over the machine, its metatheory, and the semantic-judgment and higher-order (Iris) extensions. |

## Why any of this

| Document | What it argues |
|---|---|
| [`user-stories.md`](user-stories.md) | What a *partial* semantics actually buys an end user: regression-suite synthesis, semantic diff review, confinement certificates, and the trusted-monitor architecture that composes them. The check-vs-prove spectrum, and what "asymptotic confidence" cashes out as. |
| [`bounded-effect-checking.md`](bounded-effect-checking.md) | The flagship application sketched as a commit-time gate: a semantics-based bounded model checker, with the bound frontier as a first-class output. Not built — the design and the cheap de-risking milestones. |
| [`ruby-PROJECT_PLAN.md`](ruby-PROJECT_PLAN.md) | The original plan for the Ruby investigation: targets, norms, and the order of work. |
| [`workspace-AGENTS.md`](workspace-AGENTS.md) | The working index of the investigation this repo was extracted from. Kept for orientation; it names some directories that were left behind in the extraction (see the root README's *Provenance*). |

## The rest

`semantics/` also holds the narrower design notes — `co-semantics.md`,
`linearization.md`, `slot-frame.md`, `types-and-preservation.md`,
`typed-lambdas-plan.md`, `typed-portion-safety.md`, `search-and-proof.md`,
`concolic-dataflow.md`, `lemma-library.md`, `static-soundness-poc.md`,
`type-judgments.md`, `typing-the-slice-milestones.md`,
`PROCEDURE-authoring-semantics.md` — plus
[`druby-reproduction-plan.md`](druby-reproduction-plan.md), the plan for
reproducing DRuby's narrowing results against this model.
