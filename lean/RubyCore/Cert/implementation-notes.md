# `RubyCore/Cert/` — implementation notes (**V-numbers**)

The certificate language: format, validator, and (in `RubyCore/Proof/Cert/`) the
`validate_sound` theorem. Design artifact:
[`../../../docs/semantics/certificate-language.md`](../../../docs/semantics/certificate-language.md).
Working norms: that document's §7, which restates `homebrew/PLAN.md` §4 — in
particular **norm 1**, which is why this file exists: every non-trivial decision is
recorded here, numbered and committed, including the ones that look obvious.

Numbering is **V1, V2, …**, one entry per decision, and `Proof/Cert/` shares the
series (§7 norm 7's table: *"same V-file"*).

---

## V1 — what a certificate *is*: the table, and why that is the only choice

§1.1 of the design document says a certificate is *"a claimed static shadow of the
run"*. That is the reading; it does not fix the representation, and the milestone
ladder (§6 C0) leaves the first commit to choose between two: a `certify/` driver
over the `--assn-program` JSON, or a Lean module importing `Types.Program`.

**Neither, as it turns out, is the *content* question**, and answering the content
question first is what fixed the representation. The content question is: *what can
a certificate supply that changes which programs are provable?*

The answer is forced by `Inv` (`Proof/Static/Konts.lean`). Its control conjunct is

```
CtlOk F c Γ Γs m   ≡   … ∃ τ …, infer F Γ e Γs.isEmpty c = some (τ, Γ', D') ∧ …
```

— the *nominal* `infer`, at the invariant's own table `F`. `step_ok` consumes that,
and §7 norm 7 forbids touching `Types/Core.lean` or `Proof/Static/`. So the single
degree of freedom a certificate has, without re-opening preservation, is **`F`**:

> A certificate names the declaration table the program is to be checked against,
> plus the evidence that the extension over `declsOf p` is legitimate.

Everything in §3's strawman then lands somewhere concrete:

| §3 section | what it is, under V1 |
|---|---|
| `deltaRows` | the extension itself — `Cert.table` folds `addRow` over it |
| `assumes` | the `decl` atoms the extension owes, i.e. the residue |
| `theta` | the substitution `denote`/`SatStore` are stated over |
| `bodies` | the per-body claims (C0: signatures-only, re-checked) |
| `ledger` | C2 |

And the emitter question answers itself: the emitter's job is to *produce a table
extension and a residue*, so it is a `certify/` driver over the existing export
pipeline and never a Lean module. Recorded as **V1's corollary**: §6 C0's "whichever
the first commit finds cheaper, recorded as V1" is answered — the driver, because
the Lean side is a *checker* of a table and not a serializer of a pass.

**What this deliberately does not attempt.** It does not route `inferProgram`'s
whole-program accept into `check`'s soundness. That would need the open pass's
`def` arm to satisfy `infer`'s `def` rule (`params.isEmpty`, excluding 67 of the
slice's 112 bodies — L262), and it is not what `validate_sound` is for. The open
pass is an *emitter input* here: it computes a residue, the certificate carries it,
the validator re-checks it with no search.

## V2 — `.fromDef` is in the grammar, refused by the validator, and the reason is a measurement

§3's `Provenance.fromDef` is described as *"the validator re-checks body `i` at this
sig: CHECKED, zero trust"*. **That arm cannot be sound at `Machine.init p` at all**,
and the blocker is not the validator's:

`MethodRowsOk D h` obliges `EntryOk D h τ n d` for every row of `D`, **at this
heap**. A row a program's own `def` supplies is witnessed by `UserEntryOk`, whose
resolution clause is `∀ k, TyClass h τ n → ResolvesUser h k n md` — and at the boot
heap the method is not installed yet. So the claim is *false*, not merely unproved,
and a certificate carrying it would be conditional on a false assumption: the worse
of the two failure modes §8.3 names.

Three consequences, and the third is the one worth keeping:

1. `validate` refuses a `.fromDef` claim **by name** (`Provenance.honoured`), rather
   than accepting it and letting the theorem be vacuous (§7 norm 4: gate rather than
   guess).
2. **Nothing is lost for the population `infer` already reaches.** `infer` *threads*
   the table (F1b.10): a `def` the nominal `def` rule admits adds its own row for the
   rest of the program. So a program whose rows come from its own `def`s needs no
   `deltaRows`, which is why C0's round-trip property — everything `--check` accepts
   re-validates with `assumes = emp` — holds with an *empty* certificate.
3. What is genuinely out of reach is a row for a `def` the nominal rule **refuses** —
   a parameterized one, or one on a class outside `reopenableClasses`. That is a
   **heap-phase** claim (§4 D3, milestone C9): the row is true after boot expression
   `e_k` and false before it. Recorded here so that C9 is read as *the milestone
   `.fromDef` was always waiting for* rather than as an ambition.

## V3 — the guards: one is load-bearing, four of L264's five are dropped, and why that is not a weakening

L264's `promotable` carries five guards. `Cert/Format.lean`'s `rowGuards` keeps
**one** of them, and the reason each of the other four goes is that it is about
whether a row can be *witnessed by a `def` the program contains*:

| L264 guard | why it is not here |
|---|---|
| `declaresName D name = false` | **kept.** `subDecls_addRow`'s hypothesis, and what makes `Cert.table`'s fold shadow-free and its rows disjoint from each other. |
| `cls ≠ "Object"` | a toplevel `def` installs a **private** method, so `ResolvesUser` refuses it (L162). No `def` is involved here. |
| `name ≠ "initialize"` | private by the same rule. Likewise. |
| `reopenableClasses.contains cls` | where `ClassOk`'s uniqueness clause is stated (F1b.9) — needed to tie a *name* to one class object when a `def` installs into it. An assumed row makes no claim about which object; `EntryOk` at `nomTy c` quantifies over all of them. |
| `groundClassNames.contains cls = false` | `DeclsOk_addRow`'s guard against a row on the **`.cls` arm** at a ground name (L189). `nomTy` never produces that: `nomTy "Integer"` is `.int`, the type such a row is actually read at. L266's `declFor_addRow_self_inv` is what makes the guard unnecessary rather than merely inconvenient. |

Keeping the four would forbid exactly the rows this initiative exists to ingest —
`Integer#even?` from an RBI (C4), `Comparable` (L265's next-rung list), every
program-defined class — and forbid them for reasons that do not apply to an assumed
row. What replaces them is **one visible `decl` atom in `assumes` per claimed row**,
checked by `rowsDeclared` and read out by `validate_sound`: the trust is in the
conclusion where a reader can see it, which is §1's stated discipline and §8.3's
mitigation for assumption creep.

The one guard that survives is also the one with a *cost*: `declaresName` is
name-global (`Types/Assn.lean` §R2), so a certificate row on `Comparable#<=>`
forbids every `def <=>` in the program. That is the same price `infer`'s `def` rule
pays and it is the R2 rung, not a certificate problem.

A third clause is hygiene rather than soundness: `r.sig.blk == none`, because
`sigOf` filters block-taking rows out (L242), so claiming one is claiming a
capability no rule can spend. Refused rather than silently ignored.

## V4 — three files, and the split is forced at one of the three seams

`Format.lean` / `Validate.lean` / `Json.lean` are separate from day one, which §7
norm 3 asks for on general grounds. One of the three seams is not general:

> `Lean.Json.parse` does not reduce in the kernel (L135).

So nothing on the **checked** path may import the codec, or `validate c p = true`
stops being `decide`-able and §2 constraint 2 is violated. `Json.lean` therefore
imports `Validate.lean` and nothing imports `Json.lean` but `Main.lean`. Stated as a
decision rather than left to be rediscovered, because the natural refactor —
"put the codec next to the datatype" — is the one that breaks it.

## V5 — `validate` is a conjunction of five decidable checks, and one of them is `check` at the cert's table

`validate c p` (`Cert/Validate.lean`):

1. `c.version == Cert.version` — §2 constraint 5.
2. `rowsGuarded (declsOf p) c.deltaRows` — V3.
3. `rowsDeclared c` — every claimed row appears as a `decl` atom of `c.assumes`.
4. `nominalOk c p` — `(infer (c.table p) [] p true { cls := "Object" }).isSome`.
5. `residueOk c p` — every `req`/`obl`/`eqv` atom of `c.assumes` that the certificate
   claims to have *discharged* really is discharged at `c.table p` under `c.thetaFn`.

**(4) is `check` with the table as a parameter, and that is the point rather than an
embarrassment.** §1's decoupling is about *who searches*, not about what is
provable (§8 risk 2 says so in as many words): the nominal judgement is
deterministic and syntax-directed, so there is no search in it to relocate. What the
certificate relocates is the *choice of table*, which is where the search actually
lives — an emitter picks the extension, and (4) re-checks the consequence with no
knowledge of how the extension was found.

**(5) is what makes `assumes` a residue rather than a wish.** `denote` is
`EntryOk`-valued at a `decl`/`req`/`obl` atom, so an atom the table *already*
satisfies is not an assumption at all: `dischargeAll` decides it and
`dischargeAll_sound` turns the decision into the denotation. So the validator sorts
`assumes` into *carried* and *discharged* halves, and the theorem's hypothesis is
only ever the carried one. Without (5) an emitter could pad `assumes` with anything
and the accept would be unfalsifiable.

## V6 — the residue is split, and the fourth ratchet counts the two halves separately

§8 risk 3 (*assumption creep*) asks for exactly this and it is cheap here, so it is
built at C0 rather than promised: `Cert.residue` is the sub-assertion of `assumes`
whose atoms the table does **not** already satisfy, and `validate_sound` is stated
over it. Two numbers, not one:

* **unconditional accepts** — `residue = emp`; the theorem has no hypothesis;
* **residual accepts** — `residue ≠ emp`; the theorem is exactly as strong as the
  printed atoms are true.

An accept whose residue is a *false* atom is therefore visible as a residual accept
with a nameable atom, which is the failure mode §8.3 wants routable to the emitter.

## V7 — C1 as built: what the milestone predicted, and the one thing it got wrong

`Proof/Cert/Bridge.lean` + `Proof/Cert/Sound.lean`. §3's price list holds up almost
exactly — initiation is `initiation_at` (L267) plus the extension's obligation,
consecution and safety are *nothing at all* — with one correction worth stating
because it is about the design and not about the effort.

### The bridging lemma §3 budgets for does not exist, because V1 removed the gap

§3's table anticipates *"a bridging lemma: `validate`'s per-body checking-mode
acceptance implies the `FramesOk`/`CtlOk` instance `step_ok` consumes — the analogue
of `inferOpen_factors`, in the checking direction"*. There is none, and there is
nothing for one to do:

> `CtlOk`'s eval clause **is** `infer F Γ e … = some …`, and `validate`'s `nominalOk`
> conjunct is that equation at the certificate's table. The validator's acceptance and
> the invariant's clause are the same proposition.

That is V1 paying off: choosing *the table* as what a certificate names is exactly
what makes the bridge an identity. The cost is the other half of V1 — a certificate
cannot say anything the nominal judgement cannot check — and that is where the
per-body `bodies` section lands: it is a **measurement**, not a hypothesis or a
conclusion (V2, and `Validate.lean` §3's two-tables note).

### The verdict ladder, as three theorems rather than three readings

`validate_sound_carries` is the sharp form (conditional on `rowAssn` — one `decl`
atom per claimed row); `validate_sound` is §3's statement over the whole printed
`assumes`, derived from it by `rowsDeclared`; `validate_sound_unconditional` has no
hypothesis at all. Three statements rather than one plus prose, because §2 constraint
4 makes the residue first-class and *"the verdict-strength ladder becomes an ordering
on residues instead of prose"* is only true if the ordering is in the types.

`check_accept_of_validate_empty` closes the ladder at the bottom: the empty
certificate certifies exactly what `check` accepts. So the round-trip property of §6
C0 is a theorem and not an observation about six examples.

### The gate: three programs, and the middle one is the result

| program | `check` | certificate | conclusion |
|---|---|---|---|
| `class String; def value; 1; end; def get; value; end; "x".get; end` | accept | empty | **unconditional** (round trip) |
| `1.even?` | unknown | one row, `Integer ▷ even? : () → Boolean` | **unconditional** — the residue is *discharged* |
| `1 / 2` | unknown | one row, `Integer ▷ / : (Integer) → Integer` | **conditional**, and undischargeable |

The middle row is what the pivot was for. `even?` is absent from `baseDecls` for no
reason at all — `Types/Decls.lean` picked `zero?` as the one nullary row on two
measured grounds (no bootstraptest program defines `zero?`; `abs` is defined twice in
the prelude) and never came back — so the row is claimable, and its `EntryOk` is the
*three-line instantiation* `static-soundness-poc.md` §8.2(5) advertises:
`entryOk_int_nullary` at `f := fun x => .bool (x % 2 == 0)`, with
`IntBuiltinResolves` by the same eight `rfl`s `tableOk_initHeap` uses. **A program
`check` rejects, proved safe with no hypothesis**, and the proof went through the
certificate rather than through a new rule.

The third row is kept deliberately, and it is the reason `1 / 2` and not something
tidier is this initiative's standing example: `Integer#/` is absent from `baseDecls`
by *decision* (`1 / 0` raises), so its residue has no proof and `egDiv_certified`
cannot be instantiated. §8 risk 3's mitigation is therefore not a policy here but the
shape of the theorem — an accept whose residue is false is visible as one, because a
reader has to supply the residue to use it.

### What C1 did **not** need, recorded so a later rung does not re-budget it

* no change to `Inv`, `CtlOk`, `KontOk`, `step_ok`, or any consecution case;
* no change to `Types/Core.lean`, and therefore no `--check`/`--assn` movement;
* no new invariant conjunct for the table extension — `Inv` ∃-quantifies the table
  already (F1b.8), and L267's measurement is that *nothing* in `initiation` was ever
  specific to `declsOf p`.

The whole trusted addition is `Bridge.lean`'s four lemmas and `Sound.lean`'s three
statements, on top of L266/L267 in the existing tree.
