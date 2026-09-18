# `Denote/` — the semantic side

The one library that imports **both** [`../Ratchet/`](../Ratchet)'s copied type language and
`Semantics/`'s real machine, because a denotation is by definition a statement relating the
two. Its headline theorem is [`Bridge.lean`](Bridge.lean)'s

    validateD_safe_boot : validateD p d = true → bootOkB = true → StuckFree bootMachine p

so **acceptance is the safety claim**: there is one reach number, not two.

## Three tiers, and they are a strict stack

The import graph runs one way, and reading it in this order is the fastest way in:

| tier | directory | what a file here says | files |
|---|---|---|---|
| 1 | `Ty/` | **what a `Ty` means** — `den`/`denB` over a real heap and value, arrows and closures, heap growth, joins. No machine state, no judgment | 11 |
| 2 | `Sem/` | **what it means for a machine to conform** — `StateOk κ Γ I m`, and the transport lemmas that carry it across a real `stepFn` transition | 112 |
| 3 | `Judgment/` | **the semantic judgment itself** — `SemSafeCtxA`, the continuation and run contracts, the fuel-indexed reading | 6 |
| 3 | `Rules/` | **what one rule owes** — a per-rule obligation, premises semantic and conclusion semantic, which is exactly what a `Clink.sem` field has to be | 88 |

Tier 2 is the bulk of the work and is grouped into pockets by what they are *about*, because
a transport lemma is only ever reached from the state component it preserves:

| pocket | files | contents |
|---|---|---|
| `Sem/Core/` | 19 | `StateOk` itself, `Answer`, the frame/framing contracts (`Framed`, `FramePres`, `FieldsPres`, `Reframe`), the translation `Trans`, `Transport`, and `Boot.lean` — the executable boot gate (`bootMachine`, `bootOkB`) that keeps the whole ladder non-vacuous |
| `Sem/Heap/` | 6 | allocation, the primitive heap invariants, ivar writes and their stability |
| `Sem/Names/` | 16 | absence facts: own/root/global names, the named chain, dispatch names, the native guards |
| `Sem/Class/` | 35 | fresh class creation — everything old that survives it, and everything new it establishes |
| `Sem/Subclass/` | 25 | the same, parameterized by an existing parent, plus the metaclass readiness facts |
| `Sem/Instance/` | 11 | class sites, the instance/method tables, main's retained world |

## The registry, and why a rule cannot arrive without its proof

`Clink/` is the mechanism: a rule is authored **once**, with the judgment family abstracted
(`form : DFam → Prop`), and instantiating that one `form` twice gives both readings — the
syntactic one is the `DJudge` constructor, the semantic one is **a field of a structure**
(`Clink.sem`), so it cannot be omitted. `register_dclink` refuses a rule with no proof, and
the refusal is itself captured by a `#guard_msgs` control, so the gate going quiet is a build
failure.

| file | role |
|---|---|
| `Clink/Spec.lean` | `Clink`, `Closed`, and the unconditional soundness theorems |
| `Clink/Form.lean` | `ruleForm` — the one piece of metaprogramming: constructor → `form` |
| `Clink/Registry.lean` | `DFam`, `register_dclink`, `dclinks`, `DJudgeC`, the growth gate |
| `Clink/Controls.lean` | worked derivations, the captured refusal, the positive control |

## Controls and examples are separated from the proofs on purpose

`Controls/` (63 files) is negative: countermodels, `#guard`s, and theorems that *pin an
obstruction* rather than discharge one. `Examples/` (11) is the worked instantiations — the
`Point`/`Rect`/`FlagBox` programs and `CorpusSafety.lean`'s concrete per-rung theorems.
Neither is the production interface: production lemmas stay class-, body- and
annotation-parameterized.

**`Controls/All.lean` names every control, and the gate builds that module.** It has to be
explicit: nothing imports a control by need, and `scripts/run_typed_ratchet.sh` builds named
targets rather than everything. That list used to be reached by `ClassControls.lean` importing
fifty-one of its siblings, which made "what I need" and "who I keep alive" indistinguishable
in a control's import block. Adding a control means adding a line to `All.lean`.

## A naming collision worth knowing about

`notes/` and the LEGACY sections of [`../AGENTS.md`](../AGENTS.md) refer to a **different**
`Denote/Rules/` — `Rules/Lit.lean`, `Rules/Vasgn.lean`, `Rules/Args.lean` and friends, the
per-rule files of the deleted 83-constructor `Judge`. Those files are gone. The `Rules/` here
is the answer-typed replacement, grouped by feature rather than one file per rule.
