import RubyCore.Cert.Validate
import RubyCore.Proof.Static.Assn

namespace RubyCore
namespace Proof
namespace Cert

open Interp
open RubyCore.Types
open RubyCore.Cert
open RubyCore.Proof.Static

set_option maxRecDepth 100000

/-- The fold, spelled once. -/
abbrev rowFold (D : Decls) (rows : List RowClaim) : Decls :=
  rows.foldl (fun D r => addRow D r.cls r.name r.sig) D

theorem rowFold_nil (D : Decls) : rowFold D [] = D := rfl

theorem rowFold_cons (D : Decls) (r : RowClaim) (rest : List RowClaim) :
    rowFold D (r :: rest) = rowFold (addRow D r.cls r.name r.sig) rest := rfl

theorem rowGuards_fresh {D : Decls} {r : RowClaim} (h : rowGuards D r = true) :
    declaresName D r.name = false := by
  unfold rowGuards at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact h.1.1

theorem subDecls_rowFold : ∀ (rows : List RowClaim) (D : Decls),
    rowsGuarded D rows = true → SubDecls D (rowFold D rows)
  | [], D, _ => SubDecls.refl D
  | r :: rest, D, hg => by
    simp only [rowsGuarded, Bool.and_eq_true] at hg
    rw [rowFold_cons]
    exact SubDecls.trans (subDecls_addRow (rowGuards_fresh hg.1))
      (subDecls_rowFold rest _ hg.2)

/-- **Every row of the extended table is either a claim or one the base table had.**
    The induction the certificate's `DeclsOk` runs on. -/
theorem declFor_rowFold_inv : ∀ (rows : List RowClaim) (D : Decls) {τ : Ty} {n : String}
      {d : MethodDecl}, rowsGuarded D rows = true →
      declFor (rowFold D rows) τ n = some d →
      (∃ r ∈ rows, tyClassNames τ = [r.cls] ∧ n = r.name ∧ d = r.sig)
        ∨ declFor D τ n = some d
  | [], D, τ, n, d, _, hdf => Or.inr hdf
  | r :: rest, D, τ, n, d, hg, hdf => by
    simp only [rowsGuarded, Bool.and_eq_true] at hg
    rw [rowFold_cons] at hdf
    rcases declFor_rowFold_inv rest _ hg.2 hdf with ⟨r', hm, hk⟩ | hd2
    · exact Or.inl ⟨r', List.mem_cons_of_mem _ hm, hk⟩
    · by_cases hn : n = r.name
      · subst hn
        obtain ⟨hk, rfl⟩ := declFor_addRow_self_inv (rowGuards_fresh hg.1) hd2
        exact Or.inl ⟨r, List.mem_cons_self, hk, rfl, rfl⟩
      · exact Or.inr (by
          rw [← declFor_addRow_other (D := D) (c := r.cls) (σ := r.sig) hn τ]; exact hd2)

/-! ## The carried residue, extracted

`Cert.rowAssn` is the sub-assertion `validate_sound` is conditional on: one `decl`
atom per claimed row. Two directions, and both are one `denote_all` step:

* `denote_rowAssn` reads the atoms *out*, which is what the `DeclsOk` step consumes;
* `rowAssn_of_assumes` gets `rowAssn` *from* `assumes`, which is what `rowsDeclared`
  is for — and is why the theorem can be stated in §3's shape (conditional on the
  whole printed assertion) as well as in the sharper one (conditional on the rows
  alone). -/

theorem denote_rowAssn {c : Cert} {D : Decls} {θ : TyVar → Ty} {h : Heap}
    (hd : denote D θ c.rowAssn h) :
    ∀ r ∈ c.deltaRows, EntryOk D h (nomTy r.cls) r.name r.sig := by
  intro r hm
  exact ((denote_all _).mp hd) (Assn.decl (nomTy r.cls) r.name r.sig)
    (List.mem_map_of_mem (f := fun r : RowClaim => Assn.decl (nomTy r.cls) r.name r.sig) hm)

theorem rowAssn_of_assumes {c : Cert} {D : Decls} {θ : TyVar → Ty} {h : Heap}
    (hrd : rowsDeclared c = true) (ha : denote D θ c.assumes h) :
    denote D θ c.rowAssn h := by
  refine (denote_all _).mpr ?_
  intro A hA
  obtain ⟨r, hm, rfl⟩ := List.mem_map.mp hA
  exact entailAtom_sound ha ((List.all_eq_true.mp hrd) r hm)

/-- **The certificate's table is sound at the heap the base table is sound at.**

    C1's first obligation, and the only one that reads the certificate. -/
theorem declsOk_table {c : Cert} {p : Expr} {h : Heap} {θ : TyVar → Ty}
    (hD : DeclsOk (declsOf p) h)
    (hg : rowsGuarded (declsOf p) c.deltaRows = true)
    (ha : denote (c.table p) θ c.rowAssn h) :
    DeclsOk (c.table p) h := by
  refine DeclsOk_of_subDecls hD (subDecls_rowFold c.deltaRows _ hg) ?_
  intro τ n d hnone hsome
  rcases declFor_rowFold_inv c.deltaRows _ hg hsome with ⟨r, hm, hk, rfl, rfl⟩ | hd2
  · have hτ : τ = nomTy r.cls := tyClassNames_singleton_inv hk
    subst hτ
    exact denote_rowAssn ha r hm
  · rw [hd2] at hnone; exact absurd hnone (by simp)

end Cert
end Proof
end RubyCore
