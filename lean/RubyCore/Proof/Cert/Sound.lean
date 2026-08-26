import RubyCore.Proof.Cert.Bridge

/-!
# C1 — `validate_sound`, the composed program-level theorem

`docs/semantics/certificate-language.md` §3 and milestone **C1**:

```lean
theorem validate_sound (c : Cert) (p : Expr)
    (h : validate c p = true) (ha : ⟦c.assumes⟧ D θ) :
    ∀ r, Reaches (Machine.init p) r → ¬ typeStuck r
```

This is the theorem the whole pivot exists to force — *"the composed program-level
soundness theorem the stack currently lacks"* — and the milestone's own prediction
about its cost holds up: it is **re-plumbing**, and the three obligations §3 prices
land exactly where that table says.

| obligation | how it is discharged here |
|---|---|
| initiation | `initiation_at` (L267) — `initiation` generalized over the table, plus `declsOk_table` for the extension. `StaticSoundness.lean`'s literal-heap `decide`/`rfl` pattern is reused verbatim; nothing about it was ever specific to `declsOf p`. |
| consecution | **nothing new.** `sound_from` already takes `Inv` at an arbitrary machine and `Inv` ∃-quantifies the table (F1b.8), so `step_ok` is untouched. |
| safety | **nothing new** — the bad-state predicate is unchanged, which §3 predicted. |

## What the milestone got wrong, and it is worth stating

§3's table anticipates *"a bridging lemma: `validate`'s per-body checking-mode
acceptance implies the `FramesOk`/`CtlOk` instance `step_ok` consumes — the analogue
of `inferOpen_factors`, in the checking direction"*. **No such lemma is needed and
none is here.** The reason is V1: a certificate names a *table*, and `CtlOk`'s eval
clause is literally `infer F Γ e … = some …` at that table, so `validate`'s
`nominalOk` conjunct **is** the instance — there is nothing to bridge, because the
validator's acceptance and the invariant's clause are the same proposition.

What that costs is stated in `Cert/Validate.lean` §3 and is the honest other side of
the same coin: the per-body `bodies` section is *not* what the theorem reads. Its
claimed rows are true only after the program's own `def`s run, and `Machine.init p`'s
heap is before them (V2), so `bodies_certified` is a measured ratchet and C9's heap
schedule is what would make it a conclusion.

## The three shapes of the conclusion, and why there are three

* `validate_sound_carries` — conditional on `c.rowAssn`: **one `decl` atom per claimed
  row and nothing else.** This is the sharp form and the one the other two are proved
  from.
* `validate_sound` — §3's statement, conditional on the whole printed `assumes`.
  Follows from the sharp form by `rowsDeclared`, and is what a reader of the JSON's
  `carries`/`reports` fields is looking at.
* `validate_sound_unconditional` — no hypothesis at all, when `deltaRows = []`. An
  unconditional accept is a different claim and should not have to be read out of a
  quantifier over an empty list.

§4 of this file is the gate: three worked programs, one per rung of that ladder, each
a `#check`-able theorem about a concrete program and its concrete certificate.
-/

namespace RubyCore
namespace Proof
namespace Cert

open Interp
open RubyCore.Types
open RubyCore.Cert
open RubyCore.Proof.Static

set_option maxRecDepth 100000

/-! ## 1. `validate`, taken apart

Six conjuncts, and the theorem reads two of them. Naming the projection rather than
`simp`ing at each use site, because the *count* is the interesting fact: adding a
conjunct to `validate` must not silently change what the theorem depends on. -/

theorem validate_parts {c : RubyCore.Cert.Cert} {p : Expr} (h : validate c p = true) :
    c.version = RubyCore.Cert.version ∧
    rowsGuarded (declsOf p) c.deltaRows = true ∧
    rowsDeclared c = true ∧ eqsOk c = true ∧ bodiesOk c p = true ∧
    nominalOk c p = true := by
  unfold validate at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1.1.1.1, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

/-! ## 2. The theorem -/

/-- **`validate_sound`, in its sharp form**: conditional on the *carried rows* and
    nothing else.

    Read the proof for how little there is: `declsOk_table` is the extension's
    obligation (`Proof/Cert/Bridge.lean`), `nominalOk` is `CtlOk`'s clause verbatim,
    and `initiation_at`/`sound_from` are the existing machinery. No consecution case
    and no new invariant conjunct — which is what makes the certificate architecture
    cheap and is the claim §3 makes about it. -/
theorem validate_sound_carries {c : RubyCore.Cert.Cert} {p : Expr}
    (h : validate c p = true)
    (ha : denote (c.table p) c.thetaFn c.rowAssn (Machine.init p).heap) :
    ∀ r, ReachableResult (Machine.init p) r → ¬ typeStuck r := by
  obtain ⟨-, hg, -, -, -, hn⟩ := validate_parts h
  refine sound_from (initiation_at (F := c.table p) ?_ ?_)
  · exact declsOk_table (tableOk_declsOk tableOk_initHeap classOk_initHeap) hg ha
  · unfold nominalOk at hn; exact hn

/-- **§3's statement, verbatim.** *This JSON certificate, this program, therefore no
    reachable `typeStuck` — conditional only on the printed residue.* -/
theorem validate_sound {c : RubyCore.Cert.Cert} {p : Expr}
    (h : validate c p = true)
    (ha : denote (c.table p) c.thetaFn c.assumes (Machine.init p).heap) :
    ∀ r, ReachableResult (Machine.init p) r → ¬ typeStuck r :=
  validate_sound_carries h (rowAssn_of_assumes (validate_parts h).2.2.1 ha)

/-- **And an unconditional accept is unconditional.** `Cert.unconditional` is the
    `Bool` the JSON reports, so the two readings cannot come apart. -/
theorem validate_sound_unconditional {c : RubyCore.Cert.Cert} {p : Expr}
    (h : validate c p = true) (hu : c.unconditional = true) :
    ∀ r, ReachableResult (Machine.init p) r → ¬ typeStuck r := by
  refine validate_sound_carries h ?_
  have hnil : c.deltaRows = [] := by
    unfold RubyCore.Cert.Cert.unconditional at hu
    simpa using hu
  unfold RubyCore.Cert.Cert.rowAssn
  rw [hnil]
  exact trivial

/-- **The certificate does not widen `check`'s accepts for free.** A certificate with
    no rows certifies exactly the programs `check` accepts, and this is the direction
    that says so: `validate` at the empty certificate is `check p = .accept`. Kept as a
    theorem rather than a remark because it is what makes the round-trip property of
    §6 C0 a fact rather than an observation about six examples. -/
theorem check_accept_of_validate_empty {p : Expr}
    (h : validate ({} : RubyCore.Cert.Cert) p = true) : check p = .accept := by
  obtain ⟨-, -, -, -, -, hn⟩ := validate_parts h
  have hn' : (infer (declsOf p) [] p true { cls := "Object" }).isSome = true := by
    simpa [nominalOk, RubyCore.Cert.Cert.table] using hn
  unfold check
  cases hr : infer (declsOf p) [] p true { cls := "Object" } with
  | none => rw [hr] at hn'; exact absurd hn' (by simp)
  | some r => rfl

/-! ## 3. Reading the residue

The `denote` obligation `validate_sound` quantifies over is `EntryOk` at each claimed
row (`Proof/Static/Assn.lean`'s `denote`, `.decl` arm), which is exactly what the
`carries:` line prints. Two lemmas so that a consumer never has to unfold `Assn.all`:
the residue is a conjunction of `EntryOk`s and nothing else. -/

/-- One claimed row: the residue *is* the `EntryOk` for it. -/
theorem rowAssn_single {c : RubyCore.Cert.Cert} {D : Decls} {θ : TyVar → Ty} {h : Heap}
    {r : RowClaim} (hr : c.deltaRows = [r])
    (he : EntryOk D h (nomTy r.cls) r.name r.sig) :
    denote D θ c.rowAssn h := by
  unfold RubyCore.Cert.Cert.rowAssn
  rw [hr]
  exact he

/-! ## 4. The gate — three worked programs, one per rung

Each is a theorem about a *concrete program and a concrete certificate*, so each is
`#check`-able and each is in the axiom audit below. The three are chosen to be the
three different things an accept can mean. -/

/-! ### Rung 1 — unconditional, no extension

`egVcall` (`Proof/StaticSoundness.lean`'s `egVcall`, and `Cert/Validate.lean`'s): the
L265 headline's shape at `String`, the one class the nominal fragment can both reopen
and produce a value of.

```ruby
class String
  def value; 1; end
  def get; value; end
  "x".get
end
```

`check` already accepts it (`egVcall_safe`), and the point of the certificate here is
the **round trip**: the empty certificate re-derives the same conclusion, so nothing
about the pivot lost ground. -/

theorem egVcall_validates : validate ({} : RubyCore.Cert.Cert) RubyCore.Cert.egVcall = true := by
  simp [validate, RubyCore.Cert.egVcall, rowsGuarded, rowsDeclared, eqsOk, bodiesOk,
    nominalOk, RubyCore.Cert.Cert.table, Assn.eqAtoms, infer, inferArgs, subTys, subTy,
    inferSeq, inferElems, declsOf, declaresName, baseDecls, readableClasses,
    reopenableClasses, defFree, defFreeAll, addRow, declsFor, sigOf, declFor, declOf?,
    tyClassNames, groundClassNames, isSelf]

theorem egVcall_certified :
    ∀ r, ReachableResult (Machine.init RubyCore.Cert.egVcall) r → ¬ typeStuck r :=
  validate_sound_unconditional egVcall_validates (by decide)

/-! ### Rung 2 — a table extension whose residue is **discharged**, so the
conclusion is unconditional anyway

```ruby
1.even?
```

`check` abstains: `even?` is absent from `baseDecls`, and the absence is a coverage
gap rather than a decision — `Types/Decls.lean` picked `zero?` as the one nullary row
for two measured reasons (no bootstraptest program defines `zero?`, and `abs` is
defined twice in the prelude), and `even?` was simply never added.

So the certificate claims the row, the residue is `Integer ▷ even? : () → Boolean`,
and **that residue is provable**: `entryOk_int_nullary` at the boot heap, which is
the *"three-line instantiation"* `static-soundness-poc.md` §8.2(5) advertises as the
payoff of parameterising the conformance lemma. The result is a program that `check`
rejects and a certificate proves safe with **no hypothesis at all**.

This is the rung that says the pivot buys coverage and not just plumbing, and it says
it in the honest currency: the residue is not assumed away, it is discharged. -/

def egEven : Expr := .send (some (.int 1)) "even?" [] none

def egEvenRow : RowClaim :=
  { cls := "Integer", name := "even?", sig := { params := [], ret := .bool },
    why := .assumed "baseDecls-gap" }

def egEvenCert : RubyCore.Cert.Cert :=
  { deltaRows := [egEvenRow],
    assumes := .decl .int "even?" { params := [], ret := .bool } }

/-- `check` abstains — the row is absent, so there is no opinion either way. -/
theorem egEven_unknown : check egEven = .unknown := by
  simp [check, egEven, infer, inferArgs, subTys, subTy, illTyped, tableRefutes, defTy,
    sigOf, declFor, declOf?, declsFor, baseDecls, tyClassNames, declsOf]

theorem egEven_validates : validate egEvenCert egEven = true := by
  simp [validate, egEvenCert, egEvenRow, egEven, rowsGuarded, rowGuards, rowsDeclared,
    entailAtom, Assn.declAtoms, Assn.eqAtoms, eqsOk, bodiesOk, nominalOk,
    RubyCore.Cert.Cert.table, nomTy, Provenance.honoured,
    infer, inferArgs, subTys, subTy, declsOf, declaresName, baseDecls, addRow,
    declsFor, sigOf, declFor, declOf?, tyClassNames, groundClassNames, isSelf]

/-- `Integer#even?` resolves at the boot heap, by the same eight `rfl`s
    `tableOk_initHeap`'s four entries use. That it is eight `rfl`s and not a
    `native_decide` is L73's reducibility discipline being spent (§8.4). -/
theorem intResolves_even : IntBuiltinResolves Boot.initHeap "even?" "Integer#even?" :=
  ⟨_, _, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- …and conforms to `() → Boolean`. `entryOk_int_nullary` at
    `f := fun x => .bool (x % 2 == 0)`, which is what `Builtins.run` answers by `rfl`. -/
theorem entryOk_even {D : Decls} :
    EntryOk D Boot.initHeap .int "even?" { params := [], ret := .bool } :=
  Or.inl (entryOk_int_nullary (f := fun x => .bool (x % 2 == 0)) intResolves_even
    (by decide) (by decide) (by decide)
    (fun _ _ => ValueTy.exact rfl)
    (fun _ _ => rfl)
    (fun _ _ => by
      simp [Builtins.deferTwin?, Builtins.reprDefer?, Builtins.coerceDefer?,
        Builtins.toAryDefer?]))

/-- **The gate.** A program `check` rejects, certified safe **unconditionally** —
    the residue the certificate carries is discharged rather than assumed. -/
theorem egEven_certified :
    ∀ r, ReachableResult (Machine.init egEven) r → ¬ typeStuck r :=
  validate_sound_carries egEven_validates
    (rowAssn_single (r := egEvenRow) rfl entryOk_even)

/-! ### Rung 3 — a residue that **cannot** be discharged, and the theorem says so

```ruby
1 / 2
```

`check` abstains here too, and this time the absence is a *decision*:
`Types/Decls.lean` records that `/` may not appear in `baseDecls` because
`1 / 0` raises, so `Integer#/ : (Integer) → Integer` is **not** a conformant row and
no proof of the residue exists.

The certificate accepts, and the conclusion is exactly as strong as the residue is
true — which is to say, not true. That is the point of keeping this example: an
accept whose residue is false is *visible* as such, because the residue is printed
and quantified over. §8 risk 3's mitigation is not a policy here, it is the shape of
the theorem: a reader who cannot prove `EntryOk … "/" …` cannot instantiate this. -/

theorem egDiv_validates :
    validate RubyCore.Cert.egDivCert RubyCore.Cert.egDiv = true := by
  simp [validate, RubyCore.Cert.egDivCert, RubyCore.Cert.egDiv, rowsGuarded, rowGuards,
    rowsDeclared, entailAtom, Assn.declAtoms, Assn.eqAtoms, eqsOk, bodiesOk, nominalOk,
    RubyCore.Cert.Cert.table, nomTy, Provenance.honoured,
    infer, inferArgs, subTys, subTy, declsOf, declaresName, baseDecls, addRow,
    declsFor, sigOf, declFor, declOf?, tyClassNames, groundClassNames, isSelf]

/-- **Conditional, and the hypothesis is the printed residue verbatim.** Compare
    `egEven_certified`, which has none: the difference between the two is a
    conformance proof, and that is exactly where the trust boundary sits. -/
theorem egDiv_certified
    (hres : EntryOk (RubyCore.Cert.egDivCert.table RubyCore.Cert.egDiv)
              (Machine.init RubyCore.Cert.egDiv).heap .int "/"
              { params := [.int], ret := .int }) :
    ∀ r, ReachableResult (Machine.init RubyCore.Cert.egDiv) r → ¬ typeStuck r :=
  validate_sound_carries egDiv_validates
    (rowAssn_single (r := { cls := "Integer", name := "/",
                            sig := { params := [.int], ret := .int },
                            why := .assumed "rbi" }) rfl hres)

/-! ## 5. Axiom hygiene

The C1 exit criterion, and the same baseline every other headline theorem in this
project has: `[propext, Classical.choice, Quot.sound]` and nothing else. In
particular no `native_decide`/`ofReduceBool` — §7 norm 5, and §8 risk 1's reason for
it: *"otherwise the headline theorem inherits `ofReduceBool` and 'replayed in Lean'
loses exactly the force the idea is after."*

`scripts/check-proofs.sh` runs the same audit; these are here so the file fails on its
own if the baseline moves. -/

/-- info: 'RubyCore.Proof.Cert.validate_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms validate_sound

/-- info: 'RubyCore.Proof.Cert.validate_sound_unconditional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms validate_sound_unconditional

/-- info: 'RubyCore.Proof.Cert.egVcall_certified' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms egVcall_certified

/-- info: 'RubyCore.Proof.Cert.egEven_certified' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms egEven_certified

/-- info: 'RubyCore.Proof.Cert.egDiv_certified' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms egDiv_certified

end Cert
end Proof
end RubyCore
