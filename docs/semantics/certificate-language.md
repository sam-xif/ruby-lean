# The certificate language — type-checking as certificate replay

> **Status (2026-08-25): C0–C4 built.** `validate` and the versioned JSON format are
> in [`../../lean/RubyCore/Cert/`](../../lean/RubyCore/Cert/) (**V-numbers**), the
> proved `validate_sound` in
> [`../../lean/RubyCore/Proof/Cert/`](../../lean/RubyCore/Proof/Cert/), the untrusted
> emitters in [`../../certify/`](../../certify/) (**E-numbers**). `rubycore --certify
> FILE` is the entry point. §9 records what the ladder got right and what it got
> wrong, per milestone; the ladder itself (§6) is left as written so the corrections
> are legible against it.

**Design artifact (2026-08-25). §1–§8 as designed; see §9 for as built.** Origin: an advisor suggestion —
*have the type-checking procedure emit a proof certificate that gets replayed in Lean;
if the replay passes, the program is type-checked* — worked out in a design conversation
against the machinery as it stands after L265.

This is not a new architecture. It is the **return to the architecture
[`../../../type-safety-by-reachability.md`](../../../type-safety-by-reachability.md) §4/§6
originally specified** ("certifying, not trusted": an untrusted engine emits evidence, a
small Lean validator re-checks it, `invariant_sound` turns the check into a guarantee) —
which the build then drifted away from by making the *inference* pass itself the verified
artifact (`infer` → `inferOpen` → `inferProgram`, L262–L265). This document specifies the
certificate format, the validator, the soundness statement, and the milestone ladder for
pivoting back.

**Scope, stated up front:** this initiative delivers the certificate format, the
validator, *and the proved `validate_sound` theorem* (C1). The proof is a first-class
deliverable, not future work — an unproved validator would reproduce exactly the
trusted-inference-engine posture this pivot exists to retire, and C1 is deliberately
early in the ladder so that no emitter work builds on an unverified checker. Work
happens in **its own directories** (§7 norm 7) under the **`homebrew/PLAN.md` §4 working
norms**, restated in §7.

Companions: [`static-soundness-poc.md`](static-soundness-poc.md) (the verified nominal
checker this generalizes), [`type-judgments.md`](type-judgments.md) (the declarative
judgments the validator decides), [`../../homebrew/assertion-language.md`](../../homebrew/assertion-language.md)
(the assertion language, which §3 argues is already ~90% of the certificate language),
and [`../../homebrew/slice-verdict.md`](../../homebrew/slice-verdict.md) (the census the
milestones are measured against).

---

## 1. Why: the decoupling, stated precisely

The certificate split is a **relocation of the trust boundary** so that the two halves of
type-checking land on opposite sides of it, each responsible for exactly one property:

* **Generation owns completeness only.** The emitter may be heuristic, unsound, buggy, or
  an LLM. A bad certificate costs a body we failed to certify — never a false
  "type-checked." So emitters are iterated freely, swapped, or run as a portfolio, with
  zero proof obligation.
* **Validation owns soundness only.** The validator plus the once-proved `validate_sound`
  are the entire trusted surface. It does not need to be clever, only correct — and
  checking is a much smaller thing to prove than inference, because it re-derives nothing.

Why this matters *now*: the current cost structure is that every completeness improvement
(a new inference arm) drags a soundness cost (a new hand-proved lemma) with it — one rung
per session through L225–L265, with the slice at ~17/112 bodies certified and **85
`needed`**. After the split, the coverage ratchet moves by improving *untrusted* code.
Most of the 85 `needed` atoms are answerable from Homebrew's 280 RBI files or one LLM
call; a validator does not care where the answer came from.

Two further payoffs:

* **The SMT caveat of `type-safety-by-reachability.md` §6 dissolves.** No Alethe/LFSC
  proof reconstruction: the solver emits the *answer* (a ground substitution `θ`), and
  Lean checks the answer by `decide`. We check answers, not derivations, so the solver
  never enters the TCB.
* **It forces the composed top-level theorem.** The whole-program layer currently has
  piecewise soundness (`inferOpen_factors`, `discharge_sound`) and no composed statement.
  The certificate architecture does not permit deferring it: `validate_sound` *is* that
  theorem.

The one place the two halves stay coupled is the **certificate language itself** — the
shared vocabulary bounds both what an emitter can express and what the schema-level
preservation theorem must cover. Growing the language is the one activity that still
touches trusted code, and it is where the residual hand-proof work (the walls) lives.
The decoupling is real, but it is a decoupling *modulo a shared vocabulary*.

### 1.1 What a certificate is, semantically

Ruby's **dynamic** type structure is canonical — every value carries its class, `classOf`
is total, `Sub` is literally the `ancestors` walk read off the heap. The **static** side
is a designed abstraction of it, and the agreement between the two levels is the
invariant (`ValueTy`/`TypeAgree`/`FrameConforms`), preserved by `stepFn` — that is
preservation's entire content. A certificate is therefore **a claimed static shadow of
the run**; validation checks that the shadow cannot come apart from the real tags at any
step. "Replayed in Lean" = the kernel decides the validator's acceptance, and
`validate_sound` (one induction, already paid for by `invariant_sound`) converts
acceptance into unreachability of `typeStuck`.

## 2. Constraints on the language (the non-negotiables)

1. **Validation is search-free.** Everywhere the current pass makes a choice — a fresh
   variable, a join, which provision cancels which requirement — the certificate records
   the choice and the validator only verifies it. No fixpoints, no unification, no
   solving inside the trusted code.
2. **Kernel-checkable.** Everything `decide`-able under the L73 reducibility discipline;
   `native_decide` stays banned (§4 norm 5). This biases the representation toward finite
   association lists over ground data — conveniently, what `Assn`/`Row`/`Store` already
   are. Kernel cost at slice scale (2,159 linked lines) is a *measured* risk, gated at C0,
   not an assumed-away one; the prelude-heap precedent (L135: `Lean.Json.parse` does not
   reduce, so `Saturated` there is certificate-carried already) shows both the problem
   and the fix.
3. **The certificate determines an `Inv` instance.** Soundness goes through
   `invariant_sound`, so the cert's sections map one-to-one onto `Inv`'s components:
   table claims → `DeclsOk`, per-body typings → `FramesOk`/`Γ`, control claims →
   `CtlOk`/`KontOk`. This correspondence is the design's spine; a proposed section that
   does not land in some `Inv` component is decoration.
4. **Residual assumptions are first-class.** An accept is *conditional*; the condition
   lives in the certificate (`assumes`), where the theorem quantifies over it and the
   output renders it. This is L265's `means` field made formal: an unconditional accept
   is precisely a cert with `assumes = emp`, and the verdict-strength ladder becomes an
   ordering on residues instead of prose.
5. **Versioned, canonical, diffable.** JSON serialization versioned like
   `export.rb`'s `Export::VERSION`; rows in `Row.normalize` canonical form so two
   certificates diff meaningfully. A certificate is a reviewable CI artifact in exactly
   the sense the effect manifest of `bounded-effect-checking.md` is.

## 3. The core grammar

The vocabulary exists: `ATy`/`ASig`/`Row` (`Types/Assn.lean`), the four `Assn` atom kinds
(`decl`/`req`/`obl`/`eqv`), `Store`'s polarity split (`rows` asked vs `provs` supplied,
L262), `Sig`/`Decls` (`Types/Decls.lean`). What is new is the **witness data** — the
recorded choices. Strawman:

```lean
structure Cert where
  version   : Nat
  theta     : List (TyVar × Ty)   -- the solution: ground instantiation of every variable
  deltaRows : List RowClaim       -- table extension, each row with provenance
  bodies    : List BodyCert       -- per-def typing claims
  ledger    : List DischargeStep  -- which provision answers which requirement (C2)
  assumes   : Assn                -- the residue the conclusion is conditional on

inductive Provenance where
  | fromDef (i : Nat)             -- validator re-checks body i at this sig: CHECKED, zero trust
  | assumed (src : String)        -- RBI/mock/LLM-sourced: flows into `assumes` as a decl atom

structure RowClaim where
  cls : String;  name : String;  sig : Sig;  why : Provenance

structure BodyCert where
  owner : String;  name : String
  sig    : Sig                          -- claimed params + return (C0: signatures-only)
  joins  : List (Label × Env) := []     -- stackmap at each join point / loop head (C5)
  insts  : List (CallSite × List Ty) := []  -- per-site callee instantiations (C6)

structure DischargeStep where
  var : TyVar;  name : String;  required : ASig;  provided : ASig
  -- the pinPair equalities this cancellation owes are re-derived and checked, not stored
```

Section-by-section:

* **`theta`** — the untrusted solver's entire contribution, and the mechanism by which
  SMT stays outside the TCB. Under `theta`, every `ATy` grounds to a `Ty` and every atom
  becomes decidable.
* **`deltaRows`** — L264's promotion, generalized. A `.fromDef` row is re-checked by the
  validator (the body types at the claimed sig), so it costs no trust — this is L1
  mocking's "checked, not trusted" reappearing at the type level. An `.assumed` row is a
  visible `decl` atom in `assumes`, so trust is legible in the conclusion. Promotion's
  five guards (L264) are re-checked per claimed row, copied not chosen.
* **`bodies`** — what `inferOpen` currently *infers*, now merely *claimed*; the validator
  runs in checking mode (no `OState`, no counter, no joins at C0).
* **`ledger`** — `discharge` currently *finds* the requirement/provision pairing; the
  certificate *states* it, and the validator checks `SatProvs` pairwise. This is the
  section that makes `discharge_sound`'s premise mechanically dischargeable per-program
  (the honest gap L262 recorded: "L263's `def` arm is what has to record it faithfully").
* **`assumes`** — the surviving `obl`/`req`/`decl`/`eqv` atoms, printed exactly as
  `--assn-program` prints them today.

**The soundness statement:**

```lean
theorem validate_sound (c : Cert) (p : Expr)
    (h : validate c p = true) (ha : ⟦c.assumes⟧ D θ) :
    ∀ r, Reaches (Machine.init p) r → ¬ typeStuck r
```

proved once, by exhibiting the `Inv` instance the certificate determines and applying
`invariant_sound` — initiation is `decide` at the literal boot heap (as
`StaticSoundness.lean` already does it), consecution reuses `step_ok` (already
parametric in `Γ`/`D`), safety reuses the existing progress argument. The per-program
kernel work is *only* `validate c p = true`.

**Proving this theorem is in scope (milestone C1).** The proof plan, so the milestone is
priced rather than aspirational — three obligations, each with a named reuse:

| obligation | content | what is reused | what is new |
|---|---|---|---|
| **initiation** | `Inv` holds at `Machine.init p` under the cert's table | `StaticSoundness.lean`'s literal-heap `decide`/`rfl` pattern (`tableOk_initHeap`, `classOk_initHeap`) | the table is `declsOf p ⊕ c.deltaRows` — extend `tableOk_declsOk` to checked `.fromDef` rows; `.assumed` rows are hypotheses via `⟦c.assumes⟧` |
| **consecution** | every step preserves the cert-determined `Inv` | `step_ok` (`Proof/Static/Preservation.lean`), already parametric in `Γ`/`D` | a bridging lemma: `validate`'s per-body checking-mode acceptance implies the `FramesOk`/`CtlOk` instance `step_ok` consumes — the analogue of `inferOpen_factors`, in the checking direction (strictly easier: no solver state to relate) |
| **safety** | `Inv` refutes `aboutToTypeStick` | the existing progress argument (`StaticSoundness.lean` `safety`) | nothing — the bad-state predicate is unchanged |

Plus the ledger's obligation at C2: `validate`'s pairwise check implies `SatProvs`, which
is `discharge_sound`'s open premise discharged mechanically. The proof lands in
`Proof/Cert/` (§7 norm 7), enters `check-proofs.sh`'s axiom audit at C1, and every later
milestone re-verifies it axiom-clean.

## 4. Design dimensions (the open choices, with leanings)

**D1 — how much derivation to record.** Spectrum: full per-expression derivation trees
(huge, trivially checkable) ↔ signatures-only (tiny; validator re-propagates). The sweet
spot has strong precedent — **environments at join points and loop heads only**, i.e.
Java stackmap tables / Rose's lightweight bytecode verification: between joins,
checking-mode propagation is deterministic given the claimed `Γ`; at joins the
certificate supplies the answer instead of the validator computing a fixpoint. Note the
`if`-join and `begin`-join walls (L231–L236) were exactly join-inference walls; under D1
those become *claimed and checked*, which may retire the class. Lean: signatures-only at
C0, stackmaps at C5.

**D2 — ground vs polymorphic.** A total ground `theta` cannot certify
`def twice(a); a; end` once for all callers (its provision `(α₃) → α₃` is not ground —
L264's measured correction). Escalations: (a) **per-call-site instantiation lists**
(`BodyCert.insts`) — monomorphization, finite because call sites are finite, and it is
what the solved assertion already prints (`.eqv 4 α₃` at a site); (b) schematic rows with
binders — genuine let-polymorphism, much heavier metatheory. Lean: ship (a) at C6;
let the slice census say whether (b) is ever needed.

**D3 — heap-phase claims.** `Inv`'s heap conjuncts decide at the literal boot heap, but
Ruby's difficulty is that tables mutate. A certificate could carry a **boot schedule** —
"after boot expression `e_k`, the table is `D_k`; `NoHook` holds thereafter" — validated
by replaying boot concretely (concrete execution is already trusted) and checking each
claimed `D_k` against the actual heap: the semantic heap-diff of
`bounded-effect-checking.md` §4.2 reused as a certificate section. This is the road to
certifying programs containing `define_method`. Ambitious; grammar space reserved,
build deferred (C9).

**D4 — blame atoms (the Sorbet strand).** Give each row a mode: `static` (validator
proved every call conforms) vs `guarded` (a sorbet-runtime wrapper checks it dynamically
— the `T` prelude shim, L80, already modeled). Certs with `guarded` rows conclude
`¬ sorbetStuck` instead of `¬ typeStuck` via the existing weakening
(`sorbetStuck_typeStuck`). This makes the language natively *gradual*, and it
operationalizes the stated Sorbet goal: **the provable subset of Sorbet is the set of
sigs translatable to `static` rows that replay.**

**D5 — two polarities, one language.** A refutation is also a certificate — an input +
trace, checked by replay (Direction A, already built). `TopCert := safe SafetyCert |
unsafe Witness` unifies the system under one `--certify` entry point and gives the
currently-empty `basis = refuted` cell (`slice-verdict.md` §1) a formal inhabitant.
Cheap: witness replay exists.

**D6 — modules and linking.** Per-file certificates with an interface of
(provides, assumes); the linker's obligation is `assumes ⊆ provides ∪ residue` across the
require graph. This is the shape the 227-file Homebrew cycle forces anyway, and it makes
certification incremental: an unchanged file's certificate revalidates without its
neighbors.

## 5. Deliberately excluded

* **Lean proof terms as certificates** — replay cost explodes and emitters would need to
  produce Lean; the invariant-shaped data is the small thing.
* **SMT proof objects (Alethe/LFSC)** — unnecessary once `theta` is the interface; we
  check answers, not derivations.
* **Traces as safety evidence** — traces refute (D5's `unsafe` arm); only
  invariant-shaped data certifies.

## 6. Milestones

Each milestone names its gate and the ratchet it is measured on. The standing ratchets:
the per-body census (`fragment-gap.py`, currently 112 defs / 17 accept / 85 needed / 3
oof on the slice) and a **new fourth ratchet: bodies certified-by-replayed-certificate**.
Re-measure after every milestone rather than trusting this ladder; pin the brew checkout
for ratchet numbers (L265 recorded an 84-vs-85 drift from checkout skew).

### C0 — the format, the validator, self-certification
`Cert` with `theta` + `deltaRows` + `assumes` and signatures-only `bodies`; `validate` in
checking mode over the existing fragment; a **self-certification emitter** serializing
what `inferProgram` already computes (verdict, assertion, promoted rows, and a `theta`
when the assertion is solvable). Per §7 norm 7 the emitter does not edit
`Types/Program.lean`: it is a new module in `Cert/` that *imports* `Types.Program` and
reads `PState`/the assertion out, or equivalently a `certify/` driver over the
`--assn-program` JSON — whichever the first commit finds cheaper, recorded as V1.
Round-trip: everything `--assn-program` accepts today re-validates.
**Gate:** the L263/L265 worked examples and the headline one-liner validate end-to-end;
`validate` acceptance is kernel-`decide`d, and its wall-clock at slice scale is
*measured* (constraint 2's risk retired or sized here, before anything is built on it).
**Ratchet:** fourth ratchet exists and equals the `--assn-program` accept count.

### C1 — `validate_sound`, the composed theorem
The statement of §3, axiom-clean, into `check-proofs.sh`'s audit list. Mostly
re-plumbing: `Inv` is parametric, `step_ok` carries preservation, initiation is the
`StaticSoundness.lean` pattern. This is the composed program-level soundness theorem the
stack currently lacks — the milestone the whole pivot exists to force.
**Gate:** an end-to-end `#check`-able corollary for the headline example: *this JSON
certificate, this program, therefore no reachable `typeStuck`*, conditional only on the
printed residue.

### C2 — the ledger
`DischargeStep` list; validator checks `SatProvs` pairwise instead of re-running
`discharge`'s search; the `pinPair` equalities re-derived and compared.
**Gate:** `discharge_sound`'s premise discharged mechanically for every C0-validating
certificate; no search remains anywhere in `validate`.

### C3 — the first external emitter: a solver for `theta`
z3 (or plain enumeration first — the domains are small) solving the `eqs`/residual
variables of the assertions `--assn-program` already emits. Entirely untrusted; wire as
`concolic/`-style Python beside the existing engine.
**Gate:** the fourth ratchet strictly exceeds the per-body accept count — the first
number that moves *without touching trusted code*. **Measure against the 85-`needed`
census:** how many `needed` verdicts become conditional accepts with a solved `theta`.

### C4 — RBI ingestion (`assumed` rows)
Translate Homebrew RBI/inline sigs into `.assumed` `RowClaim`s (a `SigRead.lean`
consumer). This is M10/M11's LLM-type-fill slot made sound-by-construction — a wrong row
is a visible assumption, a wrong `theta` fails replay. LLM-proposed rows ride the same
path with a different `src`.
**Gate:** at least one real slice file's bodies certify with RBI-sourced assumptions,
residue printed. **Headline unlocked:** the Sorbet-subset statement — sigs → `static`
rows that replay = the proved subset (D4 completes it; this milestone makes it
demonstrable).

### C5 — join-point stackmaps
`BodyCert.joins`; the validator consumes claimed environments at joins/loop heads instead
of computing joins.
**Gate:** bodies currently out-of-fragment or `needed` *specifically at the `if`/`begin`
join walls* (the L231/L233 population) certify. This is the milestone that tests D1's
bet that certificates retire walls, not just inference arms — if it does not move the
census, the walls are schema-level after all and the finding goes in this file.

### C6 — per-call-site instantiations
`BodyCert.insts` (D2a). Parameterized `def`s certify against each caller's ground
instantiation.
**Gate:** the `(α₃) → α₃` population (L264's non-promotable provisions) certifies at its
call sites; measure whether any slice body still wants D2b's real polymorphism.

### C7 — the refutation polarity
`TopCert := safe | unsafe` (D5); `unsafe` carries input + trace, checked by the existing
replay path; `--certify` becomes the single entry point.
**Gate:** `basis = refuted` is inhabited by a replayed certificate for one known witness
(e.g. a `repro/` case), and the concolic engine emits `unsafe` certs directly. From here
the 85 `needed` atoms double as concolic goals: violate one → an `unsafe` cert; fail at a
stated bound → an empirical frontier report beside the proof.

### C8 — guarded rows (gradual/Sorbet)
D4's `static`/`guarded` row modes; conclusion weakens to `¬ sorbetStuck` exactly when a
`guarded` row is load-bearing, via the existing transfer lemmas.
**Gate:** a mixed program — some sigs proved static, some runtime-guarded — certifies
with the split legible in the certificate; the tier-4 corpus re-measured under
`--certify`.

### C9 — boot schedules (heap phases)
D3. Only if the target corpus demands `define_method`-bearing programs; priced against
the alternative (gate them honestly).
**Gate:** one program whose method table is metaprogrammed at boot certifies, with the
claimed table sequence checked against concrete boot replay.

## 7. Working norms

**The `homebrew/PLAN.md` §4 norms apply to this work unchanged.** They are restated here
— not linked and forgotten — because §4 itself records what ignoring norm 5 cost (three
proof breaks undetected for 24 commits, L119), and this initiative adds trusted code, the
place where that failure mode is most expensive.

1. **Record every non-trivial decision** in the owning directory's
   `implementation-choices.md`/`implementation-notes.md`, numbered and committed, for
   reversibility — including choices that seem obvious. This initiative's new components
   get their own files and prefixes (norm 7's table); existing files (L-numbers,
   K-numbers, …) are extended only when the change lives in that component.
2. **Commit small, atomic units.** One coherent change per commit; at minimum one commit
   per decision entry, so `git revert` undoes the decision and its code together. One
   milestone is a commit *series*, never a single monolithic commit.
3. **Files under 1,000 lines, one concern per file, named for the concern.** The
   validator especially: `Format`/`Validate`/`Sound` are separate concerns from day one
   (norm 7's layout), not a split deferred until a file bloats. Do not add to the known
   offenders (`Interp.lean`, `Builtins.lean`); this initiative should not need to touch
   them at all (norm 7).
4. **Ratchet discipline.** After every change, `difftest run --tier 0 --sut lean`:
   **0 disagreements at every commit**, agreement only goes up, gate `Unsupported` rather
   than guess, `MODEL-BUG` never acceptable in a commit. This initiative adds no
   interpreter behavior, so tier-0 should be *byte-stable* — a moved number is a red
   flag, not progress. Additionally: `--assn`/`--assn-program` **byte-identical** at
   every milestone (the L265 worktree-binary comparison is the template), and the
   fourth-ratchet measurement in the commit message.
5. **No `native_decide` above a per-program leaf; nothing non-kernel-reducible on the
   checked path** — no `partial def`, no `String.startsWith`/`endsWith` (L73/L94). Run
   `cd ruby/lean && scripts/check-proofs.sh` at every batch boundary; `validate_sound`
   and the C2 ledger lemmas enter its audit list the commit they land. A green ratchet
   says nothing about proofs.
6. **Verify against the CRuby oracle before trusting new behavior.** Mostly inherited
   context here (the validator does not execute programs), but it binds the emitters:
   an `unsafe` certificate (C7) is confirmed against CRuby before it is reported, exactly
   as concolic witnesses are today.
7. **Isolation: this initiative lives in its own directories.** Clean separation between
   work items in the repo — the certificate machinery must be revertible, reviewable, and
   buildable as a unit, without entangling the standing `Types/`/`Proof/Static/` trees or
   the interpreter. The layout:

   | directory | contents | trust | decisions file |
   |---|---|---|---|
   | `lean/RubyCore/Cert/` | `Format.lean` (the `Cert` grammar + JSON codec), `Validate.lean` (the checker), one file per later section (`Ledger.lean`, `Joins.lean`, …) | **trusted** (validator) / format shared | `lean/RubyCore/Cert/implementation-notes.md` (**V-numbers**) |
   | `lean/RubyCore/Proof/Cert/` | `Sound.lean` (`validate_sound`), `Bridge.lean` (checking-mode → `FramesOk`/`CtlOk`), later per-section lemma files | **trusted** (the theorem) | same V-file |
   | `certify/` (new top-level, sibling of `concolic/`) | the untrusted emitters: the `inferProgram` serializer driver, the `theta` solver (C3), RBI ingestion (C4), plus `certs/` fixtures and its own tests | **untrusted** | `certify/implementation-notes.md` (**E-numbers**) |

   The interaction rule: `Cert/` and `Proof/Cert/` depend on `Types/`/`Proof/Static/`
   **by import only** — no edits to existing files beyond (a) `Main.lean` wiring for
   `--certify` and (b) index/docs entries, each as its own commit. If a needed lemma is
   missing from the existing trees, add it *there* as its own commit with its own
   L-number (it is a fact about the existing machinery), then import it — never fork a
   private copy into `Cert/`. Emitters talk to Lean exclusively through the versioned
   certificate JSON and the existing export pipeline; nothing in `certify/` links
   against or patches the Lean tree.

## 8. Risks, stated

1. **Kernel replay cost** (constraint 2) — measured at C0, not assumed. If kernel
   `decide` is too slow at slice scale, the fix is reduction-friendly validator data
   structures (as `stepFn` already is), never `native_decide` — otherwise the headline
   theorem inherits `ofReduceBool` and "replayed in Lean" loses exactly the force the
   idea is after.
2. **The vocabulary wall does not move.** Certificates change *who searches*, not *what
   is provable*: the schema-level preservation theorem still bounds coverage, and
   growing the certificate language is still hand-proof work. C5 is the designed test of
   how much of the recent grind was inference-side (retired) vs schema-side (kept).
3. **Assumption creep.** `.assumed` rows make it *easy* to certify conditionally; the
   discipline is that residues are ranked output (the fourth ratchet counts
   `assumes = emp` and residual accepts separately), and an `.assumed` row that a
   Direction-A witness violates is a finding, not an embarrassment — route it to the
   emitter, exactly as difftest disagreements route to the model.

---

## 9. As built — C0 through C4, and where the ladder was wrong

Recorded per §7 norm 1, and per §6 C5's own instruction that a milestone whose bet
does not pay *"goes in this file"*. The decision-level detail is in
`lean/RubyCore/Cert/implementation-notes.md` (**V1–V8**) and
`certify/implementation-notes.md` (**E1–E16**); this section is the design-level
account. Numbers are on the pinned checkout `homebrew/vendor/brew`, which reproduces
L265's third ratchet exactly (112 defs / 17 accept / 7 pacc / 8 uncond / 85 needed /
3 oof).

### 9.1 The content question §3 left open, and the answer that fixed everything else

§6 C0 leaves the *representation* to the first commit. The question that actually had
to be answered first was **what can a certificate supply that changes which programs
are provable**, and `Inv` forces it (V1):

> `CtlOk`'s eval clause **is** `infer F Γ e … = some …` at the invariant's own table
> `F`. So the one degree of freedom a certificate has, without re-opening
> preservation, is `F`. A certificate names **the declaration table**, plus the
> evidence that the extension over `declsOf p` is legitimate.

Two consequences ran through everything after it.

**The bridging lemma §3 budgets for does not exist.** §3's price table anticipates
*"a bridging lemma: `validate`'s per-body checking-mode acceptance implies the
`FramesOk`/`CtlOk` instance `step_ok` consumes"*. There is none and there is nothing
for one to do — `nominalOk` **is** that instance. That is the good half of V1.

**And the bad half:** a certificate cannot say anything the nominal judgement cannot
check. Which is why the per-body `bodies` section is a *measurement* and not a
conclusion, and why §4 D1's stackmaps (C5) are the next thing worth building.

### 9.2 `.fromDef` cannot be sound at `Machine.init p` — C9 is the milestone it was waiting for

§3 describes `Provenance.fromDef` as *"the validator re-checks body `i` at this sig:
CHECKED, zero trust"*. Measured (V2), it is not checkable at all at the initial
machine: `MethodRowsOk` obliges `EntryOk D h τ n d` **at this heap**, a program's own
`def` is witnessed by `UserEntryOk`, and `UserEntryOk`'s resolution clause is about
the heap *after* installation. At the boot heap the claim is **false**, not unproved.

So `validate` refuses `.fromDef` by name, and the row it was for is a **heap-phase**
claim — §4 D3, milestone **C9**. Nothing is lost for the population `infer` already
threads a row for (F1b.10), which is why C0's round-trip holds with an *empty*
certificate and `check_accept_of_validate_empty` is a theorem.

### 9.3 The kernel-replay risk (§8.1) is inherited, not created

§2 constraint 2 asks for kernel-`decide`ability and §6 C0 for it to be measured. Four
of `validate`'s six conjuncts `decide` at a literal certificate. The two that do not
are the two that name `infer`, and the reason is `static-soundness-poc.md` §8.1(4)
unchanged: `infer` is well-founded-recursive, so kernel reduction gets stuck — which
is why `check p = .accept` has been discharged by `simp` since P0a.

So **the certificate inherits the cost rather than creating it**, and §8 risk 1's
prescribed fix (reduction-friendly data structures, never `native_decide`) is a
restructuring of `Types/Core.lean`, which §7 norm 7 puts out of scope. Every worked
example in `Proof/Cert/` is `simp`-over-equation-lemmas where `infer` appears and
`decide` everywhere else; `native_decide` appears nowhere.

### 9.4 What C1 delivered, and the rung that is the actual result

Three theorems rather than one plus prose, because §2 constraint 4 only holds if the
ordering on residues is in the types: `validate_sound_carries` (conditional on the
claimed rows alone), `validate_sound` (§3's statement, over the whole printed
`assumes`), `validate_sound_unconditional` (no hypothesis). Plus
`check_accept_of_validate_empty`, which closes the ladder at the bottom.

The gate is three programs, one per rung, and **the middle one is the result**:

| program | `check` | certificate | conclusion |
|---|---|---|---|
| `class String; def value;1;end; def get;value;end; "x".get; end` | accept | empty | unconditional (round trip) |
| `1.even?` | unknown | `Integer ▷ even? : () → Boolean` | **unconditional — the residue is *discharged*** |
| `1 / 2` | unknown | `Integer ▷ / : (Integer) → Integer` | conditional, and undischargeable |

`even?` is absent from `baseDecls` for no reason at all (`Types/Decls.lean` picked
`zero?` as the one nullary row on two measured grounds and never came back), so the
row is claimable and `entryOk_int_nullary` discharges it — the *three-line
instantiation* `static-soundness-poc.md` §8.2(5) advertises. **A program `check`
rejects, proved safe with no hypothesis, through the certificate rather than through a
new rule.** `1 / 2` is kept precisely because its residue has no proof (`1 / 0`
raises): §8 risk 3's mitigation is not a policy but the shape of the theorem.

### 9.5 C2 closed L262's open premise, and hit R2

`satProvs_ledgerStore` discharges the premise L262 stated and declined
(*"`SatProvs D θ st` … is a fact about the table, not about `θ`"*). The shape is §1's
thesis in one line: the certificate records what `discharge` had to **search** for, so
the obligation per cancellation is one `sigOf` lookup. `Proof/Cert/Ledger.lean` §4 is
L262's headline with the pairing stated, and it is the first place *both* of
`discharge_sound`'s premises are met.

**And then it hits a wall that is not the certificate's** (V8/E9). For a row the
program *itself* defines, `ledger_ok` and `status: accept` cannot both hold:
`ledgerStepOk`'s lookup needs the provision in the table, and `infer`'s `def` rule
requires `declaresName D name = false` (F1c). Both halves are honest and they are about
different things; what is blocked is *composing* them.

### 9.6 The fourth ratchet: 5 → 11, and every remaining body is R2

`certify/certify.py ratchet --brew homebrew/vendor/brew --solve-bodies --optimize`

| stage | fourth ratchet |
|---|---|
| C0, empty certificates | 5 |
| + C4 project RBI rows | 7 |
| + C3 body solving, C4 core rows, E15's search | **11** |

against `--assn`'s 17 accepts (+7 `open_params`, which `bodyOk` cannot claim by
construction — L168). So **C3's gate is not met**: the ratchet moved without touching
trusted code, which is C3's substantive claim, but it does not *strictly exceed* 17.

The shortfall is exactly six bodies and every one has the same blocker
(`certify/implementation-notes.md` E16): `Token#blank?` needs `Token#null?` while
`null?` is claimed on `NullToken`; `Version#null?/#hash/#to_i/#to_s` and
`PkgVersion#head?` have a `T.nilable(String)` receiver, so L260's union dispatch needs
**both** `String#hash` and `NilClass#hash` — two rows, one name.

> **All six are blocked by name-global `declaresName`.**

### 9.7 The finding that reorders the ladder: **R2 and a `const` atom, before C5–C9**

Two measurements, and each names a rung in the **existing** tree rather than anything
the certificate language can fix.

**(a) `declaresName` is name-global, and it is now load-bearing three times over.**
`Types/Assn.lean` §R2 records it as *stated but not built* — `declaresIn` exists,
`infer` still reads `declaresName`, and the heap-side argument
(`DeclsOk_defineMethod` takes name-globality from an *arbitrary* dispatch class) is on
the wrong side of the `ResolvesAt`/`ConformsAt` line. It now blocks: V3 (a certificate
row forbids every `def` of that name), E9 (the C2 ledger against `nominalOk`), and
§9.6 (all six remaining ratchet bodies). **This should be the next rung**, ahead of
C5.

**(b) The certificate language has no atom for a constant, and that is 61% of the
census.** §6 C3 asks for the ratchet measured against the 85 `needed` atoms. Measured
(E12): **52** of the 85 have a *class-object* receiver — `T.class_of(Object) ~
::Regexp`, `~ ::NULL_TOKEN`, `~ ::Boolean` — which is to say they are **constant
reads**, 16 have a variable receiver, 8 an unmapped parameter, and 9 are row-shaped
(of which 4 are `super:` rows and one takes a block). **Four** atoms in the whole
census are claimable as rows.

`tyClassNames (.clsOf _) = []` is L264's deliberate decision, so a row on a class
object is unreadable whatever the table holds; and `Assn` has atoms for method rows
only. `Proof/Static/Assn.lean` already names the rung in as many words — *"the
constant half, carried rather than certified … giving it an atom is the assertion
language's own next rung"* — and this is the measurement that prices it: **an
`Assn.const` atom, with a `Certifies`/`InvA` clause, is worth more than half the
remaining census.**

So the honest re-ordering of §6 is: **R2, then `Assn.const`, then C5** — and §9.9 adds
a third, **T2 (`Sub`)**, from an independent direction. Recorded here rather than acted
on, because all three are rule/schema changes in the standing tree and this
initiative's norm 7 keeps it out of them.

### 9.8 Two corrections to documents this initiative depends on

* **[✗→] `Ty` has no general union, and the slice does need one.** L193 declined it on
  the grounds that *"nothing in the slice needs one, and a general union needs a normal
  form"*. Measured: the slice's central accessors — `Token#value`,
  `Version#version`, `PkgVersion#version` — are every one of them
  `T.nilable(T.any(String, Integer))`, and *every* unconfirmed accept depends on one.
  The emitter's workaround is to **narrow** (E13), which is unsound-and-visible; the
  real fix is a `Ty` arm.
* **[✗→] `attr_reader` carries a sig, and it is the population that matters.** The
  first RBI parser read `def`s only, which misses exactly those three accessors —
  methods with a signature and no body, which is what a claimed row is *for* and what
  `bodyOk` can never derive (E14).

### 9.9 The LLM arm of C4, and the third name on the wall

§6 C4 ends *"LLM-proposed rows ride the same path with a different `src`"*, and
`certify/llm.py` (`--llm`) is that path: Claude is given the file, every per-body
verdict, the type language positively **and** negatively, the rows already claimed, and
the one-row-per-name rule; it returns rows under a JSON schema; they become `.assumed`
claims with `src: "llm:<model>"` and go through the same search (E15) and the same
validator as everything else. Responses are **cached and committed** — a ratchet whose
number depends on a live sample is not a ratchet (§7 norm 4).

**Measured over the slice (`claude-opus-5`): 53 rows proposed, 53 expressible, 0
dropped, fourth ratchet unchanged at 11.** The certificates carry substantially more —
`version.rb` from 38 claimed rows to 47, `vulns/identify.rb` from 21 to 40 — and
certify exactly the same bodies. Every rule respected on the first attempt — no
constant reads, no `T.class_of` receivers, no union types, no duplicate names — and the
rows are correct Ruby. They cannot be *spent*, for three reasons, and the third is new:

* **R2** — the row that would help (`Token#value`) is unavailable, because `value` is
  already claimed on `NullToken`/`StringToken`/`NumericToken`;
* **no `Assn` atom for a constant** — the bodies wanting `Regexp#match` and
  `Pathname#*` are blocked on `::Regexp` and `::Pathname` first;
* **[new] no inherited-declaration lookup.** Seven of the ten rows are on `Comparable`
  or `Object`. `tyClassNames (.cls "Version") = ["Version"]`, so `sigOf` reads a
  class's *own* row only — verified: a row on `Comparable#<` answers at
  `.cls "Comparable"` and `none` at `.cls "Version"`. `Types/Decls.lean` records this
  as deliberate (*"it is **not** the ancestors walk … which is `Sub`'s job
  (`PLAN.md` W5 T2) and is deliberately still absent"*), and nothing is ever typed
  `.cls "Object"`.

`vulns/identify.rb` is the sharpest single instance: 19 rows, every one expressible,
zero gain — fifteen of them `String#{sub,include?,start_with?,match?,tr,…}` and
`MatchData#[]`, exactly the core-library rows §9.6 says are missing, at exactly the
receiver that file's chains go through. They change nothing because all seven of its
bodies are blocked *before* reaching them, on `::Regexp` / `::URI` constant reads —
which is the 52 again.

One of the eight files has no cached proposal: the largest,
`vulns/vulnerability.rb`, reproducibly **stalls** the request (blocked on I/O, no
`stop_reason`). It contributes 0 certified bodies in every configuration measured, so
the numbers above are complete for the ratchet — stated because "53 rows over the
slice" would otherwise read as all eight. The stall is why `llm.py` sets an explicit
client timeout and why a failed call is reported per-file rather than losing the batch
(E18a).

The model flagged the third blocker itself, unprompted, in the `notes` field the schema
asks for — *"if it uses a different ancestor those five rows will simply not fire"* — along
with a blocker §9.6's own analysis had missed (that `value` was already claimed
elsewhere).

So the reading, and it is §8 risk 2 arriving on schedule (*"certificates change who
searches, not what is provable"*):

> **Generation is not the bottleneck.** What stands between this slice and a
> certificate is three **schema** limits in the standing tree, not any emitter's
> ability to produce signatures.

Which makes the re-ordering of §9.7 three items long: **R2, `Assn.const`, and T2
(`Sub`) — all three before C5.** The `Comparable` rows are the concrete witness for
the last of them.
