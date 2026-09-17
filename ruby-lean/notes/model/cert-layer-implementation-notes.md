# `RubyCore/Cert/` — implementation notes (**V-numbers**)

The certificate language: format, validator, and (in `RubyCore/Proof/Cert/`) the
`validate_sound` theorem. Design artifact: the certificate-language note (deleted; see
[`../../AGENTS.md`](../../AGENTS.md) §Superseded design notes).
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

## V8 — C2 as built: the ledger, and the premise L262 left open

`Cert/Ledger.lean` (checker) + `Proof/Cert/Ledger.lean` (theorem). L262 proved
`discharge_sound` and said plainly what it did not do:

> **The second premise is real and is not discharged here.** `SatProvs D θ st` says
> `sigOf D (θ α) n` really is the signature the `def` supplied — a fact about the
> **table**, not about `θ`. […] Stating it as a premise is the honest split.

`satProvs_ledgerStore` discharges it, and the shape is §1's thesis in one line: **the
certificate records what `discharge` had to search for.** The pairing is a choice;
`Types/Discharge.lean` finds it by walking the store, the ledger states it, and the
validator's obligation per cancellation is one `sigOf` lookup.

### Three decisions in the checker

1. **A `DischargeStep` determines *both* polarities**, so the ledger determines a whole
   `Store` (`ledgerStore?`): `required` into `rows`, `provided` into `provs`. That is
   what makes `discharge` applicable to it and `discharge_sound` composable
   (`ledger_satStore`). A ledger that only carried provisions would have discharged
   `SatProvs` and left nothing to spend it on.
2. **The `pinPair` equalities are re-derived, never stored.** `ledgerEqsOk` runs
   `dischargeSig` — the same function `discharge` runs — and checks `θ` against its
   output. A stored equality would be one more thing to trust, and re-deriving means
   L262's three refusals arrive here as *rejections* rather than as silent
   non-cancellations.
3. **`validateFull`, not a seventh conjunct of `validate`.** Mechanically because
   `ledgerOk` lives in a file that imports `Validate.lean`; honestly because the
   ledger's theorem concludes `SatStore`, not `¬ typeStuck` — a different obligation,
   not a stronger version of the same one.

### The worked example, and what it is the first of

`Proof/Cert/Ledger.lean` §4 is L262's headline with the pairing stated: the store, the
cancellation, the solver's answer on the *cancelled* store by `satStoreB_sound (by
decide)`, and `SatStore` for the whole store. **That is the first place both of
`discharge_sound`'s premises are met**, and the whole chain is a kernel computation —
two `decide`s and a `rfl`, no `native_decide`.

### The wall, measured (and it is R2)

For a row the program **itself defines**, `ledger_ok` and `status: accept` cannot both
hold. `ledgerStepOk`'s `sigOf` lookup needs the provision in the certificate's table;
`infer`'s `def` rule requires `declaresName D name = false` (F1c); so declaring
`String#value` makes `infer` refuse `def value` and `nominalOk` false.

```
class String; def value; 1; end; def get; value; end; end
  ledger_ok: true                      the cancellation's obligation IS discharged
  status:    reject (why: "nominal")   because the table now shadows the `def`
```

Both halves are honest and they are about different things — C2's gate is the premise,
and it is met. What is blocked is *composing* it with the program-level conclusion, and
the blocker is name-global `declaresName` (`Types/Assn.lean` §R2, stated-but-not-built).
**R2 is now load-bearing for two separate things** (V3's cost note and this), which is
a measurement that should reorder it relative to C5–C9. Not worked around: the
workaround is a ledger reading a table the program does not see, and two tables
disagreeing about what a class declares is what L263's superclass-seeding refusal
already rejected.

---

## V9–V17 — the validator stops calling `infer`

The goal: rebuild `validate` with **no dependency on any of the existing `infer*`
machinery**, and drive it to cover the entire `Expr` grammar. What follows is what
that cost and what it found, decision by decision.

### V9 — fuel, not well-founded recursion

`chk` (`Cert/Check.lean`) is structurally recursive on a `Nat` carried by the
certificate (`Cert.fuel`, default 64). Everything else about this initiative follows
from that choice:

* the kernel reduces it, so `validate` is one `decide` — see V17's measurement;
* the list helpers (`chkSeq`/`chkArgs`/`chkElems`/`chkPairs`/`chkKwEntries`) take the
  recursive call as a **parameter** rather than sitting in a `mutual` block with
  `chk`, because a mutual block at the same fuel value is well-founded recursion
  again;
* fuel exhaustion answers `none`, i.e. *refuses*. A wrong bound costs a body, never
  an accept — `thetaFn`'s `.any` default is the same argument.

**Carried rather than computed.** A `sizeOf p` would be a derived `Nat` the kernel has
to reduce before it can start.

The trap this discipline exists to avoid caught **five** functions in turn, each
found by a `decide` that would not close: `infer` itself, `findDef` (a `mutual` over
`Expr`/`List Expr`), `bindParams` (the `.destr` arm recurses into a `List Param`
inside the head element), `defFree`, and the derived `BEq Expr` (V16). Every one is a
nested-inductive recursion that Lean compiles by well-founded recursion. The rule of
thumb the file now records: **on the checked path, nothing recurses on syntax except
through fuel.**

### V10 — an arm for every head, and no catch-all

`chk` has an arm for all 47 `Expr` constructors. `infer`'s trailing `| _ => none`
covered nine heads that no certificate could then address (`begin'`, `hash`, `for'`,
`defined?`, `module'`, `defs`, `sclass`, `dowhile`, `casgn`) plus the argument-position
markers, `break`/`redo`/`retry`, `alias`/`undef`, class variables, block-passes, and
parameterized `def`s. The absence of a catch-all is the point: a missing arm is now a
gap in the reading rather than a silent refusal.

### V11 — claims are read only where a rule has no answer

`NodeClaim` is §4 D1's stackmap entry (C5) and D2a's per-site instantiation (C6). It is
consulted **only in the `none` branch** of a deterministic rule, never to override one
that fired and refused. That ordering is what keeps a bad claim a lost body rather
than a false accept, and it is `deltaRows`' bargain applied per node.

### V12 — the independence is a module-graph fact

`Cert/Format.lean` imported `Types.Program` (→ `OpenSelf` → `Core`); it now imports
`Cert.ExprEq` → `Types.Assn`, whose closure is `Decls → Ty → Syntax`. **Nothing on the
checked path can call `infer`, because `infer` is not in scope.** That is a stronger
claim than a discipline and it is checkable by `grep`.

### V13 — one private copy, and what it is paid for with

`defFreeF` re-spells `Types/Core.lean`'s `defFree` on fuel. Norm 7 forbids a private
copy of anything the standing tree has; the exception is taken because (a) the module
that defines `defFree` also defines `infer`, and (b) the original does not reduce.
The debt is `defFreeF_sound : defFreeF n e = true → defFree e = true`, which was
proved and then deleted with the bridge (V17); it comes back when the fresh
development reaches the `def` arm.

### V14 — the verdict is two-dimensional

`validate c p` is the **coverage** verdict (the fourth ratchet's unit).
`Cert.certifies c p = validate c p && inferFrag c.fuel p && c.claimFree` is the
**sound** one. Two `Bool`s and not a docstring, because §2 constraint 4 says the
strength of a verdict is output; the JSON reports both plus a `tier` field. Also here:
`bodyOk` now accepts parameters, which is §9.6's 7 `open_params` bodies — *"which
`bodyOk` cannot claim by construction"* — becoming claimable.

### V15 — **a path-keyed claim cannot appear in an invariant**

The finding that changed the design, and it came from trying to state the soundness
theorem rather than from reading:

> `Inv` is a predicate on machine states, and a machine's `ctl` holds an `Expr`, not
> an address. So `chk c n D Γ e top ctx π` cannot be asserted at a reachable machine:
> there is no `π` to hand it.

So `Cert.claims : List (Expr × NodeClaim)` — keyed on the **subterm**. Consequences,
every one a simplification: `chk` loses its `Path` parameter, the list helpers lose
their index arguments, `findDef` stops threading an address, and the emitter's
obligation to compute addresses the same way the checker does is *gone* (the checker
computes none). The wire format keeps `Path`; `childAt`/`subtermAt`/`resolveClaims`
(`Cert/Json.lean`) resolve it once the program is known, and an address naming nothing
is dropped, which refuses.

The weakening, stated because it is real: two syntactically identical subterms share a
claim. That is a type ascription's convention; where a program wants two answers for
one term the claims conflict and the first wins, refusing.

### V16 — `deriving BEq for Expr` does not reduce

Measured: `example : ((.int 1 : Expr) == (.int 1)) = true := by decide` **fails**.
`Cert/ExprEq.lean` is the fuel-structural replacement (`exprEq`, `paramEq`,
`kwEntryEq`, `listEq`, `optEq`). The derived instance stays in `Syntax.lean` for
compiled use. `Cert` derives `BEq` rather than `DecidableEq` because `Expr.flt`
carries a `Float`, which has no `DecidableEq`; two `NaN` literals therefore compare
unequal and a claim on one is not found — refusing.

### V18 — the split, under norm 3

`Cert/Check.lean` reached 1,167 lines, over norm 3's limit, so it is three files and
the split is by concern rather than by size:

| file | concern |
|---|---|
| `Cert/CheckAux.lean` | the list combinators, `defFreeF`, the binding forms, the joins, `chkRescues`/`chkBlockClaim` — the machinery `chk` defers to, and the subjects `Proof/Cert/Mono.lean` §1 states its laws about |
| `Cert/Check.lean` | `chk` itself, 47 arms, no catch-all |
| `Cert/Frag.lean` | `inferFrag` — a *different question* from `chk`'s: not *does this check* but *is the accept transferable* |

### V17 — the measurement that priced the soundness half, and the bridge that was deleted

**What is done and green:** `validate` calls no `infer*`, all six conjuncts `decide`,
26 examples in `Validate.lean` + 8 in `ExprEq.lean` are `by decide`, `native_decide`
appears nowhere, tier-0 is 0 disagreements.

**What is open:** the soundness half. `CtlOk`'s eval clause is literally
`infer F Γ e … = some …` (`Proof/Static/Konts.lean`), so a `chk`-based accept does not
reach `Inv` yet.

A bridge — `chk_infer : chk c n D Γ e top ctx = some r → infer D Γ e top ctx = some r`
on the fragment — was built (~600 lines, nearly complete) and then **deleted**. It is
the wrong shape: it makes the headline theorem depend on the function the pivot exists
to retire, so `infer` cannot be deprecated while the bridge holds the theorem up. Two
things it did find are worth keeping, and both are recorded in `Cert/Check.lean` §5:

* **`defFreeF` has to be a *fragment* condition, not just a rule condition.** `infer`'s
  promotion guard reads `defFree body` and `chk`'s reads `defFreeF n body`; the two are
  related by implication only, so without the conjunct the two checkers take
  *different branches* of the promotion — one threading a row, one not — and both
  still **accept**. An implication-shaped bridge would not have caught it; only the
  equation does.
* **A literal-block send needs a receiver.** `infer`'s implicit-self block arm answers
  `some (.any, Γ, D)` for `lambda { … }` without reading `ctx.selfCls`, where `chk`
  computes the receiver first. One shape, moved to the coverage tier.

**The price of the fresh development, measured.** `Proof/Static/Mono.lean` proves
twenty structural laws about `infer`, every one by
`induction … using infer.induct with | motive2 … | motive5 …` — the well-founded
*functional induction principle* of that mutual block. `chk` has no such principle and
cannot: it recurses on fuel, and its list helpers are separate functions. So the laws
are a restate-and-reprove:

| file | to match | status |
|---|---|---|
| `Proof/Cert/Mono.lean` | 1291 | **rung 1 landed** — `TableRet`, `tableRet_zero`, and the five list-helper laws |
| `Proof/Cert/Konts.lean` | 2245 | `KontOk`'s 12 constructors carry `infer`/`inferArgs`/`inferElems`/`inferSeq`/`inferIf` premises |
| `Proof/Cert/Locals.lean` | 1988 | `FramesOk`/`StackCtx` |
| `Proof/Cert/Preservation.lean` | 2711 | `step_ok`, 73 inversion sites |

and that is the cost to reach **today's** coverage; `chk`'s fifteen extra heads are
additional per-head work after it. Stated so the ladder is priced rather than
aspirational.

**One budgeted cost that is not owed:** fuel monotonicity. State the invariant's clause
as `∃ n, chk c n D Γ e top ctx = some …` and every arm hands its children a witness at
`n`; a loop re-enters the same subterm at the same fuel, and a method body is a subterm
of the program. The existential absorbs it.

**Three tactical facts, each of which cost a wrong turn** (recorded in
`Proof/Cert/Mono.lean` §2): use `split at h` and not `cases` on a non-hypothesis
scrutinee; a generic `VarKind` blocks the head match and makes `split` re-open all 45
arms; and `absurd h (by simp)` is not a finisher — it elaborates, leaves the side goal
open, and so a `first` combinator treats it as a success (26 arms failed silently that
way before `Option.noConfusion` replaced it).

### V19 — `chk` becomes a mutual fuel block, because `chk.induct` is the whole ballgame

V17 priced the infer-free soundness route at ~8,200 lines. **It was pricing the wrong
design**, and the measurement that says so is one command:

```
#check @chk.induct
  Cannot derive functional induction principle …
    the argument has type (fun a => ∀ …) of sort Prop
    but is expected to have type Rec of sort Type
```

The list helpers took the recursive call as a *parameter* (`Rec`), which kept both
`chk` and the helpers structural without a `mutual` block. A recursive call passed as a
higher-order argument is exactly what Lean's induction-principle generator cannot see
through — and `chk.induct` is not a convenience. `Proof/Static/Mono.lean`'s twenty
structural laws are every one of them `induction … using infer.induct with | motive2 …`,
so without the analogous principle each law is a hand-rolled fuel induction fighting
`split at h`. Hand-rolling *one* of the twenty took a session and did not close.

So `chk` and its helpers are now **one `mutual` block in which every call decreases the
fuel**, a helper's call into its own tail included. Still structural recursion on a
`Nat`, so:

* the kernel still reduces it — all 26 `validate` examples remain `by decide`, whole
  file ~1.4 s, `native_decide` still nowhere (V9 intact);
* **`chk.induct` is derived**, ten motives, one per function.

Two arms had to be given **names** before any law could reach them, and this is the
second half of V19:

* **`chkOpt`** — the optional-subterm computation (`.cpathAsgn`'s base, the scoped
  class/module bases, a block-pass's operand);
* **`chkRecv`** — a send's receiver, explicit or implicit-self.

An *inline* `match eo with …` becomes a case hypothesis whose scrutinee is still `eo`,
and `split at h` cannot reach inside a hypothesis it just created. In the arms whose
enclosing pattern is a wildcard — a send whose block is `some val` for an unconstrained
`val` — the operand can then never be made concrete and the case is unprovable. Named,
each gets a motive of its own. Measured: the send arm was the last thing blocking the
table-return law, twice, for exactly this reason.

Price: fuel now bounds **node count** rather than depth, so `Cert.fuel`'s default goes
64 → 256. It fails in the same direction it always did.

### V20 — what the induction principle buys, and the residue

With `chk.induct` and the motive map (recorded in `Proof/Cert/Mono.lean`, because it
cannot be read off the file), the table-return law's ~250 cases fall to a single
uniform tactic except for a handful. Two things worth keeping:

* **Motives 3, 5 and 7 have identical types** (`chkSeq`/`chkElems`/`chkArgs`), so a
  swapped assignment *type-checks* and only the induction hypotheses' shapes reveal it.
  The first assignment had 5 and 7 exchanged; it surfaced as a send case whose
  hypothesis was about `chkElems` where the arm uses `chkArgs`. This is
  `Proof/Static/Mono.lean`'s L230 note recurring verbatim one layer up. Motives 1 and
  10 (`chkOpt`/`chkRecv`) are ambiguous the same way.
* **The residue is not mathematical.** It is the `chkPairs`/`chkKwEntries` cases, which
  want a three-link chain of induction hypotheses and where `simp_all` diverges — max
  steps, then max recursion, then `isDefEq` heartbeats in turn, and at 40M heartbeats it
  does not terminate in ten minutes. Those two motives want the chain applied
  explicitly rather than searched for.

**Four tactical facts**, each of which cost a wrong turn and all four recorded in
`Proof/Cert/Mono.lean` so the next rung does not re-pay them: use `split at h` and not
`cases` on a non-hypothesis scrutinee; a generic `VarKind` blocks the head match and
makes `split` re-open all 47 arms; `absurd h (by simp)` is not a finisher because it
elaborates and leaves its side goal open, so `first` treats it as a success (26 arms
failed silently that way); and **macro bodies are hygienic**, so an `ih`/`hr` written
inside a `local macro` refers to a fresh `ih✝` rather than the caller's hypothesis —
three separate wrong turns before that one was written down.

**Status of `validate_sound` under the new architecture: open.** `CtlOk` is still
stated over `infer`, so an accept reaches `Inv` only inside `inferFrag`. What is done
is the foundation and the *price*: C-1 is now a tractable port rather than an
open-ended one, and `Proof/Cert/Mono.lean` names the next thing to write.
