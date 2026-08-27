import RubyCore.Proof.Judgment.Values
import RubyCore.Judgment.Frag

/-!
# `DeclsOkJ` — the table invariant with the user arm restated over `Judge` (J20)

`DeclsOk`'s five halves (Proof/Static/Decls.lean) are reused verbatim except one
clause of one: `UserConforms` discharges a user row's conformance by `infer`, and the
J-spine's user-dispatch case must instead produce a `Judge` derivation for the body it
is about to run (and the `def`-promotion case must *install* one). So `EntryOkJ`
swaps `UserConforms` for `UserConformsJ` — same three guards, same heap-freeness, the
checker's verdict replaced by a derivation plus the fragment gate — and everything
else (builtin conformance, iterator rows, constants, ivars, scoped constants,
supers) is the old predicate consumed by import.
-/

namespace RubyCore
namespace Proof
namespace Judgment

open Interp
open RubyCore.Types
open RubyCore.Judgment
open RubyCore.Proof.Static

/-- `UserConforms` over `Judge`: the body judges below the declared return, in the
    context `enterUserMethod` builds, **and sits in the machine-typed fragment**
    (the body becomes `ctl` at dispatch, so the eval arm's gate must already hold).
    Heap-free, like the original — which is what keeps every transport below one
    pass-through. -/
def UserConformsJ (D : Decls) (c mname : String) (md : MethodDef) (d : MethodDecl) :
    Prop :=
  d.params = [] ∧ d.blk = none ∧ defFree md.body = true ∧ MFrag md.body ∧
  ∃ Γ' r τb, Judge D [] md.body false
      { cls := c, selfCls := some c, ret := r, meth := some mname,
        params := some [] } τb Γ' D ∧
    SubJ τb d.ret ∧ (∀ σ, r = some σ → σ = d.ret)

/-- The user witness, with conformance over `Judge`. -/
def UserEntryOkJ (D : Decls) (h : Heap) (τr : Ty) (mname : String) (d : MethodDecl) :
    Prop :=
  ∃ md c, UserKey τr c ∧ (∀ k, TyClass h τr k → ResolvesUser h k mname md) ∧
    className h md.owner = c ∧ UserConformsJ D c mname md d

/-- `EntryOk` with the user arm swapped; the builtin and iterator arms are the old
    predicates unchanged. -/
def EntryOkJ (D : Decls) (h : Heap) (τr : Ty) (mname : String) (d : MethodDecl) : Prop :=
  BuiltinEntryOk h τr mname d ∨ UserEntryOkJ D h τr mname d ∨ IterEntryOk h τr mname d

/-- A blockless row is witnessed by one of the two resolving arms —
    `EntryOk.blockless`, restated. -/
theorem EntryOkJ.blockless {D : Decls} {h : Heap} {τr : Ty} {mname : String}
    {ps : List Ty} {τret : Ty}
    (he : EntryOkJ D h τr mname { params := ps, ret := τret, blk := none }) :
    BuiltinEntryOk h τr mname { params := ps, ret := τret, blk := none } ∨
      UserEntryOkJ D h τr mname { params := ps, ret := τret, blk := none } := by
  rcases he with h1 | h2 | ⟨-, -, -, -, ⟨br, hdb⟩, -⟩
  · exact Or.inl h1
  · exact Or.inr h2
  · exact absurd hdb (by simp)

def MethodRowsOkJ (D : Decls) (h : Heap) : Prop :=
  ∀ τr mname d, declFor D τr mname = some d → EntryOkJ D h τr mname d

/-- The refinement invariant's table half, J-flavored: `DeclsOk` with its first
    conjunct restated, the other four consumed unchanged. -/
def DeclsOkJ (D : Decls) (h : Heap) : Prop :=
  MethodRowsOkJ D h ∧
  (∀ n τ, constTy? D n = some τ → ConstOk h n τ) ∧
  (∀ c x τ, ivarTy? D c x = some τ → IvarOk h c x τ) ∧
  (∀ c n τ, scopedConstTy? D c n = some τ → ScopedConstOk h c n τ) ∧
  (∀ c n d, superDecl? D c n = some d → SuperOk h c n d) ∧
  -- **The rows' parameters are ground** (J22) — heap-free, so it rides every
  -- transport untouched. The dispatch cases convert their `VTys` argument facts
  -- back to the `ValuesTy` the old conformance witnesses consume
  -- (`VTys.toValuesTy`), and groundness of the declared parameters is exactly the
  -- side condition; a certificate row with a union parameter is unwitnessable by a
  -- `ValueTy`-based conformance anyway, so nothing expressible is lost.
  (∀ τr mname d, declFor D τr mname = some d → ∀ p ∈ d.params, groundTy p = true) ∧
  -- …and so are the declared ivar and global rows (their conformance clauses are
  -- `ValueTy`-based, so the write cases collapse `VTy` through groundness).
  (∀ c x τ, ivarTy? D c x = some τ → groundTy τ = true) ∧
  (∀ x τ, globalTy? D x = some τ → groundTy τ = true)

/-- **The J-table invariant survives an allocating step** — `DeclsOk_grow` with the
    user arm's conformance passing straight through (`UserConformsJ` mentions no
    heap, exactly as `UserConforms` did). -/
theorem DeclsOkJ_grow {D : Decls} {h h' : Heap} (hg : PlainGrow h h')
    (hsat : Saturated h) (hd : DeclsOkJ D h) : DeclsOkJ D h' := by
  refine ⟨?_, fun n τ hn => constOk_grow hg hsat (hd.2.1 n τ hn),
    fun c x τ hn => ivarOk_grow hg hsat (hd.2.2.1 c x τ hn),
    fun c nn τ hn => scopedConstOk_grow hg hsat (hd.2.2.2.1 c nn τ hn),
    fun c nn dd hn => superOk_grow hg hsat (hd.2.2.2.2.1 c nn dd hn),
    hd.2.2.2.2.2.1, hd.2.2.2.2.2.2.1, hd.2.2.2.2.2.2.2⟩
  intro τr mname decl hdecl
  rcases hd.1 τr mname decl hdecl with ⟨bid, hres, hconf⟩ |
    ⟨mdu, cu, htys, hres, hnm, hconf⟩ | ⟨hτ, hmn, hdp, hdr, hdb, hmiss⟩
  · exact Or.inl ⟨bid,
      fun k ht => ResolvesAt_grow hg hsat (hres k (TyClass_grow hg ht)), hconf⟩
  · exact Or.inr (Or.inl ⟨mdu, cu, htys,
      fun k ht => ResolvesUser_grow hg hsat (hres k (TyClass_grow hg ht)),
      by rw [hg.className_eq]; exact hnm, hconf⟩)
  · exact Or.inr (Or.inr ⟨hτ, hmn, hdp, hdr, hdb, fun k ht => by
      have hm0 := hmiss k (TyClass_grow hg ht)
      unfold MissesAt lookupIn at hm0 ⊢
      rw [hg.ancestors_eq hsat, lookup_go_grow hg]
      exact hm0⟩)

/-! ## The `IvarOnly` transports (J26) — an ivar write moves no table read -/

theorem ivarOnly_entryOkJ {h h' : Heap} (hi : IvarOnly h h') {D : Decls} {τr : Ty}
    {mname : String} {d : MethodDecl} (he : EntryOkJ D h τr mname d) :
    EntryOkJ D h' τr mname d := by
  rcases he with ⟨bid, hres, hconf⟩ | ⟨md, c, hkey, hres, hown, hconf⟩ |
    ⟨hτ, hmn, hdp, hdr, hdb, hmiss⟩
  · exact Or.inl ⟨bid, fun k hk => hi.resolvesAt (hres k (hi.tyClass hk)), hconf⟩
  · exact Or.inr (Or.inl ⟨md, c, hkey,
      fun k hk => hi.resolvesUser (hres k (hi.tyClass hk)),
      by rw [hi.className_eq]; exact hown, hconf⟩)
  · exact Or.inr (Or.inr ⟨hτ, hmn, hdp, hdr, hdb, fun k hk => by
      have hm0 := hmiss k (hi.tyClass hk)
      unfold MissesAt at hm0 ⊢
      rw [hi.lookupIn_eq]; exact hm0⟩)

/-- `IvarOnly.rowsAndConsts`, J-flavored — everything but the ivar half, which the
    write's own conformance check re-establishes. -/
theorem ivarOnly_rowsAndConstsJ {h h' : Heap} (hi : IvarOnly h h') {D : Decls}
    (hd : DeclsOkJ D h) :
    MethodRowsOkJ D h' ∧ (∀ n τ, constTy? D n = some τ → ConstOk h' n τ) ∧
      (∀ c n τ, scopedConstTy? D c n = some τ → ScopedConstOk h' c n τ) ∧
      (∀ c n d, superDecl? D c n = some d → SuperOk h' c n d) :=
  ⟨fun τr mname d hf => ivarOnly_entryOkJ hi (hd.1 τr mname d hf),
   fun n τ hn => hi.constOk (hd.2.1 n τ hn),
   fun c n τ hn => hi.scopedConstOk (hd.2.2.2.1 c n τ hn),
   fun c n dd hn => hi.superOk (hd.2.2.2.2.1 c n dd hn)⟩

end Judgment
end Proof
end RubyCore
