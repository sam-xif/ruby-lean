import RubyCore.Proof.Cert.Bridge
import RubyCore.Proof.StaticSoundness
import RubyCore.Proof.Cert.Mono

/-!
# The composed certificate theorem, and the one premise C-1 discharges

`docs/semantics/certificate-language.md` §3 and milestone **C1** proved

```lean
theorem validate_sound (c : Cert) (p : Expr) (h : validate c p = true) (ha : ⟦c.assumes⟧) :
    ∀ r, Reaches (Machine.init p) r → ¬ typeStuck r
```

**unconditionally**, and it did so by one specific route: `validate`'s sixth conjunct
*was* `infer (c.table p) [] p true … |>.isSome`, so it *was* `Inv`'s control clause and
there was nothing to bridge (§9.1).

`validate` no longer calls `infer` (V9–V16; V12 makes the independence a fact about the
module graph). **So this file's headline theorem is now conditional**, on exactly one
premise, and that is the honest state of the pivot rather than a detail:

```lean
theorem validate_sound_of_ctl (h : validate c p = true) (ha : …)
    (hctl : CtlOk (c.table p) { cls := "Object" } [] [] (Machine.init p)) :
    ∀ r, ReachableResult (Machine.init p) r → ¬ typeStuck r
```

Read what is and is not open:

* **The certificate's own half is proved.** `DeclsOk` for the table the certificate
  names, given the carried residue, is `declsOk_table` (`Bridge.lean`) — and it is
  untouched by the pivot, because it reads `rowsGuarded` and the `decl` atoms of
  `assumes` and mentions no checker at all. That is the half where the *trust* lives.
* **Safety and consecution are proved and unchanged** — `sound_from`, and `step_ok`
  underneath it. The bad-state predicate never moved.
* **The control clause is open.** `CtlOk`'s eval arm is stated over `infer`
  (`Proof/Static/Konts.lean`), so `chkOk c p = true` does not yet produce one.

Milestone **C-1** (§10.6) is exactly the discharge of `hctl` from `chkOk`, and
`Proof/Cert/Mono.lean` is its first rung — with V20's measurement saying it is a
tractable port rather than an open-ended one.

**Why the premise is `CtlOk` and not `infer … = some …`.** `initiation_ctl`
(`Proof/StaticSoundness.lean`, L268) was factored out of `initiation_at` for this: the
statement below mentions **no `infer`**, so nothing in this file stands in the way of
deprecating it, and C-1 has one premise to close rather than a shape to reverse-engineer.
An earlier attempt went the other way — a bridge from `chk` back to `infer` — and was
deleted for precisely that reason.
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
    chkOk c p = true := by
  unfold validate at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1.1.1.1, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

/-! ## 2. The half that is proved: the table the certificate names is sound

This is the certificate's own contribution and the only place its trust enters. It is
independent of which checker `validate` runs — `declsOk_table` reads `rowsGuarded` and
the `decl` atoms, and mentions no judgement. -/

/-- **`DeclsOk` for the claimed table**, at the boot heap, conditional on the carried
    rows. `declsOf p`'s own obligation is F1a's (`rfl` at the boot heap) and each
    claimed row costs exactly one `EntryOk`, which `rowsDeclared` forces to appear as a
    `decl` atom of `assumes`. -/
theorem declsOk_of_validate {c : RubyCore.Cert.Cert} {p : Expr}
    (h : validate c p = true)
    (ha : denote (c.table p) c.thetaFn c.rowAssn (Machine.init p).heap) :
    DeclsOk (c.table p) Boot.initHeap :=
  declsOk_table (tableOk_declsOk tableOk_initHeap classOk_initHeap)
    (validate_parts h).2.1 ha

/-! ## 3. The composed theorem, modulo the control clause -/

/-- **§3's statement, with its one open premise named.** Everything but `hctl` is
    proved: the table's soundness from the certificate (§2), initiation from
    `initiation_ctl`, consecution and safety from `sound_from`.

    `hctl` is milestone C-1. Note what the statement does *not* mention: `infer`. -/
theorem validate_sound_of_ctl {c : RubyCore.Cert.Cert} {p : Expr}
    (h : validate c p = true)
    (ha : denote (c.table p) c.thetaFn c.rowAssn (Machine.init p).heap)
    (hctl : CtlOk (c.table p) { cls := "Object" } [] [] (Machine.init p)) :
    ∀ r, ReachableResult (Machine.init p) r → ¬ typeStuck r :=
  sound_from (initiation_ctl (declsOk_of_validate h ha) hctl)

/-- The same, over the whole printed `assumes` rather than the carried rows — which is
    what a reader of the JSON's `carries`/`reports` fields is looking at. -/
theorem validate_sound_assumes {c : RubyCore.Cert.Cert} {p : Expr}
    (h : validate c p = true)
    (ha : denote (c.table p) c.thetaFn c.assumes (Machine.init p).heap)
    (hctl : CtlOk (c.table p) { cls := "Object" } [] [] (Machine.init p)) :
    ∀ r, ReachableResult (Machine.init p) r → ¬ typeStuck r :=
  validate_sound_of_ctl h (rowAssn_of_assumes (validate_parts h).2.2.1 ha) hctl

/-- **And an unconditional accept needs no residue.** `Cert.unconditional` is the
    `Bool` the JSON reports, so the two readings cannot come apart. -/
theorem validate_sound_unconditional {c : RubyCore.Cert.Cert} {p : Expr}
    (h : validate c p = true) (hu : c.unconditional = true)
    (hctl : CtlOk (c.table p) { cls := "Object" } [] [] (Machine.init p)) :
    ∀ r, ReachableResult (Machine.init p) r → ¬ typeStuck r := by
  refine validate_sound_of_ctl h ?_ hctl
  have hnil : c.deltaRows = [] := by
    unfold RubyCore.Cert.Cert.unconditional at hu
    simpa using hu
  unfold RubyCore.Cert.Cert.rowAssn
  rw [hnil]
  exact trivial

/-! ## 4. Reading the residue

The `denote` obligation the theorems quantify over is `EntryOk` at each claimed row
(`Proof/Static/Assn.lean`'s `denote`, `.decl` arm), which is exactly what the
`carries:` line prints. -/

/-- One claimed row: the residue *is* the `EntryOk` for it. -/
theorem rowAssn_single {c : RubyCore.Cert.Cert} {D : Decls} {θ : TyVar → Ty} {h : Heap}
    {r : RowClaim} (hr : c.deltaRows = [r])
    (he : EntryOk D h (nomTy r.cls) r.name r.sig) :
    denote D θ c.rowAssn h := by
  unfold RubyCore.Cert.Cert.rowAssn
  rw [hr]
  exact he

/-! ## 5. The gate, as far as it goes

The three worked programs of C1 — one per rung of the verdict ladder — with their
*validation* facts, which are what the pivot changed and are now each one `decide`
rather than a fifteen-name `simp` list over `infer`'s equation lemmas. Their
`_certified` corollaries wait on C-1; keeping the validation facts here is what makes
that a one-line change when it lands, and keeps them from silently rotting. -/

theorem egVcall_validates :
    validate ({} : RubyCore.Cert.Cert) RubyCore.Cert.egVcall = true := by decide

theorem egVcall_sound_tier :
    RubyCore.Cert.Cert.certifies ({} : RubyCore.Cert.Cert) RubyCore.Cert.egVcall = true := by
  decide

/-- `1.even?` — the rung whose residue is *discharged*, so the conclusion will be
    unconditional once C-1 lands. `even?` is absent from `baseDecls` for no reason at
    all, so the row is claimable and `entryOk_int_nullary` discharges it. -/
def egEven : Expr := .send (some (.int 1)) "even?" [] none

def egEvenRow : RowClaim :=
  { cls := "Integer", name := "even?", sig := { params := [], ret := .bool },
    why := .assumed "baseDecls-gap" }

def egEvenCert : RubyCore.Cert.Cert :=
  { deltaRows := [egEvenRow],
    assumes := .decl .int "even?" { params := [], ret := .bool } }

theorem egEven_validates : validate egEvenCert egEven = true := by decide

/-- `Integer#even?` resolves at the boot heap, by the same eight `rfl`s
    `tableOk_initHeap`'s four entries use. -/
theorem intResolves_even : IntBuiltinResolves Boot.initHeap "even?" "Integer#even?" :=
  ⟨_, _, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- …and conforms to `() → Boolean`. -/
theorem entryOk_even {D : Decls} :
    EntryOk D Boot.initHeap .int "even?" { params := [], ret := .bool } :=
  Or.inl (entryOk_int_nullary (f := fun x => .bool (x % 2 == 0)) intResolves_even
    (by decide) (by decide) (by decide)
    (fun _ _ => ValueTy.exact rfl)
    (fun _ _ => rfl)
    (fun _ _ => by
      simp [Builtins.deferTwin?, Builtins.reprDefer?, Builtins.coerceDefer?,
        Builtins.toAryDefer?]))

/-- **The residue is provable**, which is the whole point of that rung: the accept will
    be unconditional, not merely conditional-on-something-plausible. Kept green so the
    conformance proof does not rot while C-1 is outstanding. -/
theorem egEven_residue_discharged :
    denote (egEvenCert.table egEven) egEvenCert.thetaFn egEvenCert.rowAssn Boot.initHeap :=
  rowAssn_single (r := egEvenRow) rfl entryOk_even

/-- `1 / 2` — the rung whose residue *cannot* be discharged, kept for exactly that
    reason: `Types/Decls.lean` records that `/` may not appear in `baseDecls` because
    `1 / 0` raises, so no proof of this residue exists and a reader who cannot produce
    one cannot instantiate the theorem. §8 risk 3's mitigation is the shape of the
    statement, not a policy. -/
theorem egDiv_validates :
    validate RubyCore.Cert.egDivCert RubyCore.Cert.egDiv = true := by decide

/-- …and it is in the sound tier: a *table* extension is not a node claim. -/
theorem egDiv_sound_tier :
    RubyCore.Cert.Cert.certifies RubyCore.Cert.egDivCert RubyCore.Cert.egDiv = true := by
  decide

/-! ## 6. Axiom hygiene

Every theorem above is `[propext, Classical.choice, Quot.sound]` and nothing else — in
particular no `native_decide`/`ofReduceBool`, which is §7 norm 5 and §8 risk 1's reason
for it. `scripts/check-proofs.sh` runs the same audit; these are here so the file fails
on its own if the baseline moves. -/

/-- info: 'RubyCore.Proof.Cert.validate_sound_of_ctl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms validate_sound_of_ctl

/-- info: 'RubyCore.Proof.Cert.validate_sound_unconditional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms validate_sound_unconditional

/-- info: 'RubyCore.Proof.Cert.declsOk_of_validate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms declsOk_of_validate

/-- info: 'RubyCore.Proof.Cert.egEven_residue_discharged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms egEven_residue_discharged

/-- info: 'RubyCore.Proof.Cert.egVcall_validates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms egVcall_validates

end Cert
end Proof
end RubyCore
