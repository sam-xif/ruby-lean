import RubyCore.Proof.Cert.Sound
import RubyCore.Proof.Judgment.Sound

/-!
# The composed certificate theorem over the judgment (J24) — J1's exit

`validate_sound_of_ctl`'s open premise `hctl` was "the control clause, over
`infer`" (`Proof/Cert/Sound.lean`, C-1). The judgment layer replaces its supplier:
the control clause is a **derivation**, and the composed theorem needs no checker in
its statement at all —

    judge_sound_cert : rowsGuarded … → (residue, as `EntryOkJ` per claimed row) →
      MFrag p → Judge (c.table p) [] p true topJCtx τ Γ' D' →
      ∀ r, ReachableResult (Machine.init p) r → ¬ typeStuck r

The certificate's own half (`declsOkJ_table`) is `declsOk_table`'s proof with the
target swapped: the fold/guard lemmas of `Proof/Cert/Bridge.lean` are consumed
unchanged, and the assembly runs through `DeclsOkJ_of_subDecls` (J23). The residue
is taken directly as one `EntryOkJ` per claimed row rather than through the `Assn`
denotation — the builtin arm the discharged residues actually use is shared between
`EntryOk` and `EntryOkJ`, so a discharged old-style residue (`entryOk_even`) is a
J-residue verbatim. The J2 rung (`Deriv.check`) supplies `hj` from a serialized
certificate; `egEven` below supplies it by hand, which closes the loop the C-ladder
left open: **a certificate with a claimed row, certified end to end, no `infer`,
no `chk`.**
-/

namespace RubyCore
namespace Proof
namespace Judgment

open Interp
open RubyCore.Types
open RubyCore.Cert
open RubyCore.Proof.Static
open RubyCore.Proof.Cert
open RubyCore.Judgment

set_option maxRecDepth 100000

/-- **The certificate's table is J-sound at the heap the base table is J-sound
    at** — `declsOk_table`, retargeted. The residue arrives as one `EntryOkJ` per
    claimed row, at the certificate's own table. -/
theorem declsOkJ_table {c : Cert} {p : Expr} {h : Heap}
    (hD : DeclsOkJ (declsOf p) h)
    (hg : rowsGuarded (declsOf p) c.deltaRows = true)
    (ha : ∀ r ∈ c.deltaRows, EntryOkJ (c.table p) h (nomTy r.cls) r.name r.sig)
    (hgr : ∀ r ∈ c.deltaRows, ∀ q ∈ r.sig.params, groundTy q = true) :
    DeclsOkJ (c.table p) h := by
  refine DeclsOkJ_of_subDecls hD (subDecls_rowFold c.deltaRows _ hg) ?_
  intro τ n d hnone hsome
  rcases declFor_rowFold_inv c.deltaRows _ hg hsome with ⟨r, hm, hk, rfl, rfl⟩ | hd2
  · have hτ : τ = nomTy r.cls := tyClassNames_singleton_inv hk
    subst hτ
    exact ⟨ha r hm, hgr r hm⟩
  · rw [hd2] at hnone
    exact absurd hnone (by simp)

/-- **The composed theorem** (J1's exit): a certificate's table half plus a root
    derivation at that table certify the program — `validate_sound_of_ctl` with
    `hctl` discharged by the judgment layer, and no checker in the statement. -/
theorem judge_sound_cert {c : Cert} {p : Expr} {τ : Ty} {Γ' : Env} {D' : Decls}
    (hg : rowsGuarded (declsOf p) c.deltaRows = true)
    (ha : ∀ r ∈ c.deltaRows,
      EntryOkJ (c.table p) Boot.initHeap (nomTy r.cls) r.name r.sig)
    (hgr : ∀ r ∈ c.deltaRows, ∀ q ∈ r.sig.params, groundTy q = true)
    (hmf : MFrag p)
    (hj : Judge (c.table p) [] p true topJCtx τ Γ' D') :
    ∀ r, ReachableResult (Machine.init p) r → ¬ typeStuck r :=
  judge_sound (declsOkJ_table declsOkJ_declsOf hg ha hgr) hmf hj

/-! ## `egEven`, unconditionally — the rung the C-ladder left open

`1.even?` with the claimed row `Integer#even? : () → Boolean`
(`Proof/Cert/Sound.lean`'s `egEvenCert`): the row's residue is *discharged* (the
same `entryOk_int_nullary` witness, whose builtin arm `EntryOk` and `EntryOkJ`
share), the derivation reads the claimed row back through `sigOf`, and the
conclusion is the real safety property — where `egEven_certified` waited on C-1,
this is that corollary, delivered through the judgment instead. -/

/-- The claimed row's J-residue: the discharged builtin witness, verbatim. -/
theorem entryOkJ_even {D : Decls} :
    EntryOkJ D Boot.initHeap .int "even?" { params := [], ret := .bool } :=
  Or.inl (entryOk_int_nullary (f := fun x => .bool (x % 2 == 0)) intResolves_even
    (by decide) (by decide) (by decide)
    (fun _ _ => ValueTy.exact rfl)
    (fun _ _ => rfl)
    (fun _ _ => by
      simp [Builtins.deferTwin?, Builtins.reprDefer?, Builtins.coerceDefer?,
        Builtins.toAryDefer?]))

theorem egEven_judged : Judge (Cert.table egEvenCert egEven) [] egEven true topJCtx
    .bool [] (Cert.table egEvenCert egEven) := by
  have hsig : sigOf (Cert.table egEvenCert egEven) .int "even?"
      = some ([], .bool) := by decide
  exact .send (.expl .int) .nil hsig .nil

theorem egEven_mfrag : MFrag egEven :=
  mfragB_sound (n := 4) (by decide)

/-- **The `egEven_certified` C-1 was waiting for.** -/
theorem egEven_judge_safe :
    ∀ r, ReachableResult (Machine.init egEven) r → ¬ typeStuck r :=
  judge_sound_cert (by decide)
    (fun r hm => by
      simp only [egEvenCert, List.mem_singleton] at hm
      subst hm
      exact entryOkJ_even)
    (fun r hm => by
      simp only [egEvenCert, List.mem_singleton] at hm
      subst hm
      intro q hq
      simp [egEvenRow] at hq)
    egEven_mfrag egEven_judged

/-! ## Axiom hygiene -/

/-- info: 'RubyCore.Proof.Judgment.judge_sound_cert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms judge_sound_cert

/-- info: 'RubyCore.Proof.Judgment.egEven_judge_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms egEven_judge_safe

end Judgment
end Proof
end RubyCore
