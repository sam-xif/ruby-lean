import RubyCore.Proof.Cert.Sound
import RubyCore.Proof.Judgment.Sound

/-!
# The composed certificate theorem over the judgment (J24) — J1's exit

`validate_sound_of_ctl`'s open premise `hctl` was "the control clause, over
`infer`" (`Proof/Cert/Sound.lean`, C-1). The judgment layer replaces its supplier:
the control clause is a **derivation**, and the composed theorem needs no checker in
its statement at all —

    judge_sound_cert : rowsGuarded … → (residue, as `EntryOkJ` per claimed row) →
      MFrag A p → Judge A (c.table p) [] p true topJCtx τ Γ' D' →
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
theorem declsOkJ_table {A : SemAxioms} {c : Cert} {p : Expr} {h : Heap}
    (hD : DeclsOkJ A (declsOf p) h)
    (hg : rowsGuarded (declsOf p) c.deltaRows = true)
    (ha : ∀ r ∈ c.deltaRows, EntryOkJ A (c.table p) h (nomTy r.cls) r.name r.sig)
    (hgr : ∀ r ∈ c.deltaRows, ∀ q ∈ r.sig.params, groundTy q = true) :
    DeclsOkJ A (c.table p) h := by
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
theorem judge_sound_cert {A : SemAxioms} {c : Cert} {p : Expr} {τ : Ty} {Γ' : Env}
    {D' : Decls}
    (hax : SemAxiomsOk A)
    (hg : rowsGuarded (declsOf p) c.deltaRows = true)
    (ha : ∀ r ∈ c.deltaRows,
      EntryOkJ A (c.table p) Boot.initHeap (nomTy r.cls) r.name r.sig)
    (hgr : ∀ r ∈ c.deltaRows, ∀ q ∈ r.sig.params, groundTy q = true)
    (hmf : MFrag A p)
    (hfr : fragHead p = true)
    (hj : Judge A (c.table p) [] p true topJCtx τ Γ' D') :
    ∀ r, ReachableResult (Machine.init p) r → ¬ typeStuck r :=
  judge_sound hax (declsOkJ_table declsOkJ_declsOf hg ha hgr) hmf hfr hj

/-! ## `egEven`, unconditionally — the rung the C-ladder left open

`1.even?` with the claimed row `Integer#even? : () → Boolean`
(`Proof/Cert/Sound.lean`'s `egEvenCert`): the row's residue is *discharged* (the
same `entryOk_int_nullary` witness, whose builtin arm `EntryOk` and `EntryOkJ`
share), the derivation reads the claimed row back through `sigOf`, and the
conclusion is the real safety property — where `egEven_certified` waited on C-1,
this is that corollary, delivered through the judgment instead. -/

/-- The claimed row's J-residue: the discharged builtin witness, verbatim. -/
theorem entryOkJ_even {A : SemAxioms} {D : Decls} :
    EntryOkJ A D Boot.initHeap .int "even?" { params := [], ret := .bool } :=
  Or.inl (entryOk_int_nullary (f := fun x => .bool (x % 2 == 0)) intResolves_even
    (by decide) (by decide) (by decide)
    (fun _ _ => ValueTy.exact rfl)
    (fun _ _ => rfl)
    (fun _ _ => by
      simp [Builtins.deferTwin?, Builtins.reprDefer?, Builtins.coerceDefer?,
        Builtins.toAryDefer?]))

theorem egEven_judged : Judge [] (Cert.table egEvenCert egEven) [] egEven true topJCtx
    .bool [] (Cert.table egEvenCert egEven) := by
  have hsig : sigOf (Cert.table egEvenCert egEven) .int "even?"
      = some ([], .bool) := by decide
  exact .send (.expl .int) .nil hsig .nil

theorem egEven_mfrag : MFrag [] egEven :=
  mfragB_sound (A := []) (n := 4) (by decide)

/-- **The `egEven_certified` C-1 was waiting for.** -/
theorem egEven_judge_safe :
    ∀ r, ReachableResult (Machine.init egEven) r → ¬ typeStuck r :=
  judge_sound_cert semAxiomsOk_nil (by decide)
    (fun r hm => by
      simp only [egEvenCert, List.mem_singleton] at hm
      subst hm
      exact entryOkJ_even)
    (fun r hm => by
      simp only [egEvenCert, List.mem_singleton] at hm
      subst hm
      intro q hq
      simp [egEvenRow] at hq)
    egEven_mfrag (by decide) egEven_judged

/-! ## J38b: deciding a constant claim's residue at a concrete heap

A claimed constant's residue is `ConstOk`/`ScopedConstOk` at the boot heap — both
carry a `∀`-over-`ObjId` clause, bounded here by the heap's own size (an
out-of-range id has no class payload: `Heap.get` answers the default object,
whose payload is `.none`). Exact types only (`valueTy?`), which is all a
class-object or literal constant needs. -/

/-- An out-of-range id has no class payload. -/
theorem classPayload?_oob {h : Heap} {j : ObjId} (hj : ¬ j < h.objs.size) :
    h.classPayload? j = none := by
  unfold Heap.classPayload? Heap.get
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (Nat.le_of_not_lt hj)]
  rfl

/-- `ConstOk`, decided: the toplevel lookup answers a value of exactly `τ`, and no
    other class object in range owns the name. -/
def constOkB (h : Heap) (n : String) (τ : Ty) : Bool :=
  match constOwn h Boot.objectId n with
  | some v =>
    (valueTy? h v == some τ) &&
    (((List.range h.objs.size).filter fun j =>
        (h.classPayload? j).isSome && j != Boot.objectId).all fun j =>
      (constOwn h j n).isNone)
  | none => false


theorem constOkB_sound {h : Heap} {n : String} {τ : Ty}
    (hb : constOkB h n τ = true) : ConstOk h n τ := by
  unfold constOkB at hb
  split at hb
  case h_1 v hv =>
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hb
    refine ⟨v, hv, ValueTy.exact hb.1, ?_⟩
    intro j hj hjo
    by_cases hlt : j < h.objs.size
    · have hmem : j ∈ (List.range h.objs.size).filter fun j =>
          (h.classPayload? j).isSome && j != Boot.objectId := by
        rw [List.mem_filter]
        exact ⟨List.mem_range.mpr hlt, by simp [hj, hjo]⟩
      have := hb.2 j hmem
      simpa using this
    · rw [classPayload?_oob hlt] at hj
      exact absurd hj (by simp)
  case h_2 => exact Bool.noConfusion hb

/-- `ScopedConstOk`, decided: every in-range class object named `c` passes the
    privacy walk and answers a value of exactly `τ`. -/
def scopedConstOkB (h : Heap) (c n : String) (τ : Ty) : Bool :=
  ((List.range h.objs.size).filter fun o =>
      (h.classPayload? o).isSome && className h o == c).all fun o =>
    ((ancestors h o).all fun a =>
        match h.classPayload? a with
        | some cp => !cp.privateConsts.contains n
        | none => true) &&
      match constLookupFrom h o n with
      | some v => valueTy? h v == some τ
      | none => false

theorem scopedConstOkB_sound {h : Heap} {c n : String} {τ : Ty}
    (hb : scopedConstOkB h c n τ = true) : ScopedConstOk h c n τ := by
  unfold scopedConstOkB at hb
  rw [List.all_eq_true] at hb
  intro o hpay hcn
  by_cases hlt : o < h.objs.size
  · have hmem : o ∈ (List.range h.objs.size).filter fun o =>
        (h.classPayload? o).isSome && className h o == c := by
      rw [List.mem_filter]
      exact ⟨List.mem_range.mpr hlt, by simp [hpay, hcn]⟩
    have := hb o hmem
    simp only [Bool.and_eq_true] at this
    refine ⟨this.1, ?_⟩
    have h2 := this.2
    split at h2
    case h_1 v hv => exact ⟨v, hv, ValueTy.exact (by simpa using h2)⟩
    case h_2 => exact Bool.noConfusion h2
  · rw [classPayload?_oob hlt] at hpay
    exact absurd hpay (by simp)

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
