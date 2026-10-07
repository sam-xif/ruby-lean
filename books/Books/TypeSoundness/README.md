# `Books/TypeSoundness/` — accepted programs do not get type-stuck

The checker (`Checker`, in [`../../../ruby-lean/Checker/`](../../../ruby-lean/Checker/README.md))
decides whether a Sorbet-annotated Ruby program is well typed. This book proves
that its answer means something on the model. The theorem is in
[`Soundness.lean`](Soundness.lean):

```lean
theorem validateD_safe_run {p : Checker.Expr} {d : Deriv}
    (h : validateD p d = true) (hb : bootOkB = true) (fuel : Nat) :
    Semantics.typeStuck (Semantics.run fuel (toRuby p)) = false
```

If the executable checker `validateD` accepts program `p` (with any derivation
`d`, which is an untrusted hint), then running `p` on the model from the booted
prelude, for any number of steps, never ends in an uncaught `NoMethodError`,
`ArgumentError` or `TypeError`. `bootOkB = true` says the booted machine satisfies
the invariant; it is a closed boolean that the build evaluates, and it is what
keeps the theorem from being vacuous. `validateD_safe` is the same statement
from any conformant machine and `validateD_safe_boot` is the step between.

The hypothesis is the verdict of the code that actually runs, not a relation
that the code is separately claimed to implement. So acceptance is the safety
claim.

Declarations here are in the namespace `Checker.Soundness` (mostly
`Checker.Soundness.Typed`). They sit inside the checker's namespace so that
`Expr` and `Ty` mean the checker's own copies. The checker deliberately does not
import the model, so both libraries define those names, and this book is the one
place that imports both.

## How the proof is put together

1. **What a type means.** [`Denotation/`](Denotation/) defines, for each checker
   type, the set of runtime values it describes on a real heap.
2. **What it means for a machine to agree with the checker.**
   [`Conformance/`](Conformance/) defines `StateOk`: every local, instance
   variable, class and method table on the machine has the type the checker's
   context says it has. Most of the book is showing that each kind of machine
   step preserves it.
3. **What a typing rule owes.** [`Judgment/`](Judgment/) states the semantic
   contract of a typing judgment, and [`Rules/`](Rules/) proves, rule by rule,
   that each rule of the checker meets it.
4. **No rule without its proof.** [`Registry/`](Registry/README.md) pairs each
   rule with its proof (a *clink*). The checker refuses any derivation that uses
   a rule with no registered proof, and `Registry/AuditBridge.lean` turns an
   accepted derivation into a certified one.
5. **The theorem.** `Soundness.lean` composes these in about forty lines.

[`Semantics/Interp.lean`](Semantics/Interp.lean) is where the model's real
`stepFn` is imported and `typeStuck` is defined.
[`Controls/`](Controls/) and [`Examples/`](Examples/) are tests of the above,
described below. `Report/Active.lean` is the source of the gate's progress
report.

## Status

The theorem above is proved, with no `sorry` and no extra axioms, for every rule
the checker has (`Checker/ClinkPolicy.lean` lists them; a rule that is not
listed is refused by `validateD`, so the theorem never speaks about it).
Every file in this directory builds.

The proofs were rebuilt against a newer version of the model, and not all of the
older files came along. The ones that have not been rebuilt (older lemmas about
class, subclass and module entry, the controls and worked examples that use
them, and the corpus-wide audit `RuleAudit`/`RuleCoverage`) are in
[`../../Unrebuilt/`](../../Unrebuilt/README.md), out of the build. The file counts
in the tables below are for what is here. See [the rebuild guide](Registry/README.md)
and [`../../AGENTS.md`](../../AGENTS.md) for the current counts.

## Three tiers, and they are a strict stack

The import graph runs one way, and reading it in this order is the fastest way in:

| tier | directory | what a file here says | files |
|---|---|---|---|
| 1 | `Denotation/` | **what a `Ty` means** — `den`/`denB` over a real heap and value, arrows and closures, heap growth, joins. No machine state, no judgment | 15 |
| 2 | `Conformance/` | **what it means for a machine to conform** — `StateOk κ Γ I m`, and the transport lemmas that carry it across a real `stepFn` transition | 199 |
| 3 | `Judgment/` | **the semantic judgment itself** — `SemSafeCtxA`, the continuation and run contracts, the fuel-indexed reading | 12 |
| 3 | `Rules/` | **what one rule owes** — a per-rule obligation, premises semantic and conclusion semantic, which is exactly what a `Clink.sem` field has to be | 219 |

Tier 2 is the bulk of the work and is grouped into pockets by what they are *about*, because
a transport lemma is only ever reached from the state component it preserves:

| pocket | files | contents |
|---|---|---|
| `Conformance/Core/` | 23 | `StateOk` itself, `Answer`, the frame/framing contracts (`Framed`, `FramePres`, `FieldsPres`, `Reframe`), the translation `Trans`, `Transport`, and `Boot.lean` — the executable boot gate (`bootMachine`, `bootOkB`) that keeps the whole ladder non-vacuous |
| `Conformance/Heap/` | 11 | allocation, the primitive heap invariants, ivar writes and their stability |
| `Conformance/Names/` | 18 | absence facts: own/root/global names, the named chain, dispatch names, the native guards |
| `Conformance/Class/` | 54 | fresh class creation — everything old that survives it, and everything new it establishes |
| `Conformance/Subclass/` | 18 | the same, parameterized by an existing parent, plus the metaclass readiness facts |
| `Conformance/Instance/` | 16 | class sites, the instance/method tables, main's retained world |
| `Conformance/Module/` | 38 | fresh module creation, with the same split as `Class/` |
| `Conformance/Singleton/` | 7 | singleton method tables and their dispatch |
| `Conformance/Closure/` | 14 | captured frames: what a lambda or block can still read and write after its creator moves on |

## The registry, and why a rule cannot arrive without its proof

`Registry/` is the mechanism: a rule is authored **once**, with the judgment family abstracted
(`form : DFam → Prop`), and instantiating that one `form` twice gives both readings — the
syntactic one is the `DJudge` constructor, the semantic one is **a field of a structure**
(`Clink.sem`), so it cannot be omitted. `register_dclink` refuses a rule with no proof, and
the refusal is itself captured by a `#guard_msgs` control, so the gate going quiet is a build
failure.

| file | role |
|---|---|
| `Registry/Spec.lean` | `Clink`, `Closed`, and the unconditional soundness theorems |
| `Registry/Form.lean` | `ruleForm` — the one piece of metaprogramming: constructor → `form` |
| `Registry/Registry.lean` | `DFam`, `register_dclink`, `dclinks`, `DJudgeC`, the growth gate |
| `Registry/Controls.lean` | worked derivations, the captured refusal, the positive control |

## Semantic rebuild profile

Rules are gated until their proofs are rebuilt against the dynamic-state machine. Select rules
in `Checker/ClinkPolicy.lean` and proof providers in `Registry/ActiveProofs.lean`.
[The rebuild guide](Registry/README.md) explains admission and the gate modes.

The default `scripts/run_typed_ratchet.sh` (in `books/`) checks the active registry and
`Soundness.lean`'s original soundness theorem, then reports enabled clinks and actual
`validateD` corpus accepts as climbed. `Registry/SoundnessAudit.lean` rejects
nonstandard theorem axioms; `Report/Active.lean` derives gated dependencies from
the checker's verified traces. Disabled rules are work remaining.

Use `--clink-rebuild` for proofs/controls only. The original complete-coverage audit
(`--full-corpus`) is in `books/Unrebuilt/` with the worked theorems it reads. The generic validator/certifier supports
all authoring families, including companion and body premises; enable the needed
clinks and their semantic providers to admit more programs. `Soundness/Full.lean`
holds optional raw-DJudge completeness helpers.

## Controls and examples are separated from the proofs on purpose

`Controls/` (36 files and their aggregate `All.lean`) is negative: countermodels, `#guard`s, and theorems that *pin an
obstruction* rather than discharge one. `Examples/` (22) is the worked instantiations: derivations for
concrete programs, checked end to end.
Neither is the production interface: production lemmas stay class-, body- and
annotation-parameterized.

**`Controls/All.lean` names every control here, and `scripts/check_controls.sh` builds
that module.** It has to be
explicit: nothing imports a control by need, and `scripts/run_typed_ratchet.sh` builds named
targets rather than everything. That list used to be reached by `ClassControls.lean` importing
fifty-one of its siblings, which made "what I need" and "who I keep alive" indistinguishable
in a control's import block. Adding a control means adding a line to `All.lean`.

## A naming collision worth knowing about

`notes/` and the LEGACY sections of [`../../AGENTS.md`](../../AGENTS.md) refer to a **different**
`Rules/` — `Rules/Lit.lean`, `Rules/Vasgn.lean`, `Rules/Args.lean` and friends, the
per-rule files of the deleted 83-constructor `Judge`. Those files are gone. The `Rules/` here
is the answer-typed replacement, grouped by feature rather than one file per rule.
