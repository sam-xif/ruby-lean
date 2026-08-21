import RubyCore.Proof.StaticSoundness
import RubyCore.Types.Assn

/-!
# Layer 2 — `⟦·⟧`, and the soundness of the assertion language

`homebrew/assertion-language.md` §9. This file supplies the middle layer of that
document's three, and then proves the thing §9.3 says nothing proves:

> `⟦·⟧` is a *definition*, and nothing checks that it means what it is supposed
> to. If `⟦p ~ n : σ⟧` is subtly weaker than "this dispatch does not type-stick",
> the theorem stays true and stops being about anything.

**`denote_declAssn` is that check, for the declaration fragment.** It says the
syntax-to-semantics map is not merely *sound* but **faithful**:

```
⟦declAssn D⟧ h  ↔  DeclsOk D h
```

An `iff`, both directions, over the artifact `Inv` already carries. So the new
unchecked surface §9.3 warns about is, for the fragment R1–R4 covers, *empty*:
the assertion means the invariant clause, provably, and not by inspection of a
definition. What remains genuinely unchecked is only the requirement/obligation
fragment's *intent* — and even there `denote` is defined over `EntryOk`, so the
atoms are the existing predicates rather than new ones (§9.1's mitigation, taken
literally).

## What this file does **not** do, and why that is the design rather than a gap

It does not change `Inv`. §12 R5 prices that as *"large: every closed consecution
case re-opens"*, and constraint 4 (`HANDOFF.md`) says that cannot be done
incrementally. The faithfulness theorem is what makes the change unnecessary:
because `⟦declAssn F⟧ h` and `DeclsOk F h` are the **same proposition**, the
assertion-shaped invariant `InvA` below is *equivalent* to `Inv`, so
`sound_from`'s eleven consecution cases transfer with no re-proof at all
(`assn_sound_from`). R5's stated payoff — *"the assertion means something to the
proof"* — is obtained here without R5's stated cost.
-/

namespace RubyCore
namespace Proof
namespace Static

open Interp
open RubyCore.Types

set_option maxRecDepth 100000

/-! ## 1. `⟦·⟧` (§9.1)

The atoms are `EntryOk`, **deliberately**. §9.1 writes them as
`ResolvesAt h C n ∧ ConformsAt C n σ`, and `EntryOk` is exactly that pair,
class-indexed, in the shape L146/L147 arrived at — plus the user arm L157 added,
which §9.1 predates. Defining `⟦·⟧` over anything new would be new unchecked
surface for no benefit; defining it over `EntryOk` is what makes the faithfulness
theorem below a `rfl`-shaped unfolding rather than a bridge.

`θ` is the substitution §9.1 quantifies over. It is a *parameter* here and
quantified in `denoteClosed`, so that a requirement on an unresolved receiver can
be read either as an open predicate (what `require`'s row case records) or as the
closed assertion §9.1 writes (what the method boundary universally closes). -/
def denote (D : Decls) (θ : TyVar → Ty) : Assn → Heap → Prop
  | .emp, _ => True
  | .and A B, h => denote D θ A h ∧ denote D θ B h
  | .decl τ n σ, h => EntryOk D h τ n σ
  | .req τ n σ, h => EntryOk D h (τ.subst θ) n (σ.subst θ)
  | .obl c R, h => ∀ e ∈ R.entries, EntryOk D h (nomTy c) e.1 (e.2.subst θ)

/-- §9.1's `⟦ var α ~ n : σ ⟧ h := ∀ θ, ⟦ θα ~ n : σ ⟧ h` — *universally closed at
    the method boundary*, applied to the whole assertion. This is the reading a
    **certificate** has: an assertion with a free row variable claims something
    about every instantiation. -/
def denoteClosed (D : Decls) (A : Assn) (h : Heap) : Prop := ∀ θ, denote D θ A h

/-- `RowsOk P h := ⟦P⟧ h` generalizes `DeclsOk` (§9.2). Named separately because
    that is the name §9.2 gives the conjunct `Inv` would carry. -/
abbrev RowsOk (D : Decls) (θ : TyVar → Ty) (P : Assn) (h : Heap) : Prop :=
  denote D θ P h

/-! ## 2. Conjunction -/

theorem denote_all {D : Decls} {θ : TyVar → Ty} {h : Heap} :
    ∀ (L : List Assn), denote D θ (Assn.all L) h ↔ ∀ A ∈ L, denote D θ A h := by
  intro L
  induction L with
  | nil => simp [Assn.all, denote]
  | cons A rest ih =>
    cases rest with
    | nil => simp [Assn.all]
    | cons B rest' =>
      simp only [Assn.all, denote, List.mem_cons] at *
      constructor
      · rintro ⟨hA, hR⟩ C hC
        rcases hC with rfl | hC
        · exact hA
        · exact (ih.mp hR) C hC
      · intro hall
        exact ⟨hall A (Or.inl rfl), ih.mpr fun C hC => hall C (Or.inr hC)⟩

/-! ## 3. The graph of `declFor`, enumerated — and the enumeration is exact

The one non-trivial computation in this file. `DeclsOk` quantifies over
`declFor D τ n` for **every** `τ`, of which there are infinitely many (`Ty.cls`
takes a `String`); `declAtoms D` is a finite list. That the two agree is what
makes the re-notation faithful, and it rests on three clauses of `tyClassNames`
(`Types/Assn.lean` §4 names them). -/

/-- `declsFor` answers non-empty only at a key the table has. -/
theorem mem_declTys_of_declsFor {D : Decls} {c : String} {n : String} {d : MethodDecl}
    (h : declOf? D c n = some d) : ∃ ms, (c, ms) ∈ D.rows ∧ (n, d) ∈ ms := by
  unfold declOf? declsFor at h
  cases hf : D.rows.find? (·.1 == c) with
  | none => rw [hf] at h; simp at h
  | some cd =>
    rw [hf] at h
    obtain ⟨c', ms⟩ := cd
    have hmem : (c', ms) ∈ D.rows := List.mem_of_find?_eq_some hf
    have hc : c' = c := by
      have := List.find?_some hf
      simpa using this
    subst hc
    refine ⟨ms, hmem, ?_⟩
    simp only at h
    cases hf2 : ms.find? (·.1 == n) with
    | none => rw [hf2] at h; simp at h
    | some e =>
      rw [hf2] at h
      simp only [Option.map_some, Option.some.injEq] at h
      have hmem2 : e ∈ ms := List.mem_of_find?_eq_some hf2
      have : e.1 = n := by have := List.find?_some hf2; simpa using this
      obtain ⟨a, b⟩ := e
      simp only at this h
      subst this; subst h
      exact hmem2

theorem mem_declNames {D : Decls} {τ : Ty} {c n : String} {d : MethodDecl}
    (hc : c ∈ tyClassNames τ) (h : declOf? D c n = some d) : n ∈ declNames D τ := by
  unfold declNames
  refine List.mem_flatMap.mpr ⟨c, hc, ?_⟩
  unfold declOf? at h
  cases hf : (declsFor D c).find? (·.1 == n) with
  | none => rw [hf] at h; simp at h
  | some e =>
    have hmem : e ∈ declsFor D c := List.mem_of_find?_eq_some hf
    have : e.1 = n := by have := List.find?_some hf; simpa using this
    exact this ▸ List.mem_map_of_mem hmem

/-- **The enumeration is exactly the graph of `declFor`.** Both directions, and
    the backward one is the one that matters: it is what says `declAssn` leaves
    nothing out, hence that `⟦declAssn D⟧ → DeclsOk D` — the direction a
    certificate is read in. -/
theorem mem_declAtoms_iff {D : Decls} {τ : Ty} {n : String} {d : MethodDecl} :
    (τ, n, d) ∈ declAtoms D ↔ declFor D τ n = some d := by
  constructor
  · intro hm
    unfold declAtoms at hm
    obtain ⟨τ', _, hm2⟩ := List.mem_flatMap.mp hm
    obtain ⟨n', _, hm3⟩ := List.mem_filterMap.mp hm2
    cases hdf : declFor D τ' n' with
    | none => rw [hdf] at hm3; simp at hm3
    | some d' =>
      rw [hdf] at hm3
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hm3
      obtain ⟨rfl, rfl, rfl⟩ := hm3
      exact hdf
  · intro hdf
    -- `declFor` answered `some`, so `tyClassNames τ` is `c :: cs` and `c` declares `n`.
    have hsplit : ∃ c, c ∈ tyClassNames τ ∧ declOf? D c n = some d := by
      unfold declFor at hdf
      cases hcn : tyClassNames τ with
      | nil => rw [hcn] at hdf; simp at hdf
      | cons c cs =>
        rw [hcn] at hdf
        dsimp only at hdf
        cases hd : declOf? D c n with
        | none => rw [hd] at hdf; simp at hdf
        | some d' =>
          rw [hd] at hdf
          dsimp only at hdf
          by_cases hall : (cs.all fun c' => declOf? D c' n == some d') = true
          · rw [hall] at hdf
            simp only [if_true, Option.some.injEq] at hdf
            exact ⟨c, List.mem_cons_self, by rw [hd, hdf]⟩
          · simp only [Bool.not_eq_true] at hall
            rw [hall] at hdf; simp at hdf
    obtain ⟨c, hc, hdc⟩ := hsplit
    have hn : n ∈ declNames D τ := mem_declNames hc hdc
    have hτ : τ ∈ declTys D := by
      cases τ with
      | int => simp [declTys]
      | bool => simp [declTys]
      | nilT => simp [declTys]
      | sym => simp [declTys]
      -- L183: `tyClassNames .any = []`, so `hc` is contradictory — which is also
      -- why `declTys` need not list `.any`: `declFor D .any n` is `none` for every
      -- `n`, so both sides of the biconditional are false there.
      | any => exact absurd hc (by simp [tyClassNames])
      -- L184: same, at the class-object arm.
      | clsOf n => exact absurd hc (by simp [tyClassNames])
      -- L193: same, at the nilable arm.
      | nilable _ => exact absurd hc (by simp [tyClassNames])
      | cls c' =>
        -- `tyClassNames (.cls c')` is `[]` or `[c']`, and `c` is in it.
        have hcc : c = c' := by
          simp only [tyClassNames] at hc
          split at hc
          · simp at hc
          · simpa using hc
        subst hcc
        obtain ⟨ms, hms, _⟩ := mem_declTys_of_declsFor hdc
        refine List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ?_)))
        exact List.mem_map_of_mem (f := fun cd => Ty.cls cd.1) hms
    unfold declAtoms
    refine List.mem_flatMap.mpr ⟨τ, hτ, ?_⟩
    refine List.mem_filterMap.mpr ⟨n, hn, ?_⟩
    rw [hdf]; rfl

/-! ## 4. The faithfulness theorem

§9.3's honest weak point, closed for the declaration fragment. -/

theorem denote_declAssn {D : Decls} {θ : TyVar → Ty} {h : Heap} :
    denote D θ (declAssn D) h ↔ DeclsOk D h := by
  unfold declAssn
  rw [denote_all]
  constructor
  · intro hall τ n d hdf
    have hm : (τ, n, d) ∈ declAtoms D := mem_declAtoms_iff.mpr hdf
    exact hall (.decl τ n d) (List.mem_map_of_mem (f := fun a => Assn.decl a.1 a.2.1 a.2.2) hm)
  · intro hok A hA
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hA
    exact hok a.1 a.2.1 a.2.2 (mem_declAtoms_iff.mp ha)

/-! ### Substitution on a variable-free signature is the identity

The bridge between §8.2's decidable discharge (which compares against the
**table**, hence needs a `Sig`) and §9.1's denotation (which is stated under a
substitution). Three lines of content and it is what keeps `dischargeRow` honest:
a row entry is discharged only when it has no variables left, and then it means
the same thing under every `θ` — which is §9.1's `∀ θ` reading, satisfied
trivially rather than vacuously. -/

theorem ATy.subst_of_toNom? {θ : TyVar → Ty} {a : ATy} {τ : Ty}
    (h : a.toNom? = some τ) : a.subst θ = τ := by
  induction a generalizing τ with
  | nom τ' => simp [ATy.toNom?] at h; simp [ATy.subst, h]
  | var α => simp [ATy.toNom?] at h
  -- L193b: `toNom?` normalizes on the way out and `subst` normalizes on the way
  -- down, which is exactly what makes this arm an application of the IH rather than
  -- a second definition to keep in step.
  | nilOf a ih =>
    simp only [ATy.toNom?, Option.map_eq_some_iff] at h
    obtain ⟨σ, hσ, rfl⟩ := h
    simp [ATy.subst, ih hσ]

theorem ATy.map_subst_of_nomList? {θ : TyVar → Ty} :
    ∀ {ps : List ATy} {qs : List Ty}, ATy.nomList? ps = some qs →
      ps.map (ATy.subst θ) = qs := by
  intro ps
  induction ps with
  | nil => intro qs h; simp [ATy.nomList?] at h; simp [h]
  | cons a rest ih =>
    intro qs h
    cases ha : a.toNom? <;> cases hr : ATy.nomList? rest <;>
      simp [ATy.nomList?, ha, hr] at h
    subst h
    simp [List.map_cons, ATy.subst_of_toNom? ha, ih hr]

theorem ASig.subst_of_toNom? {θ : TyVar → Ty} {σ : ASig} {σn : Sig}
    (h : σ.toNom? = some σn) : σ.subst θ = σn := by
  cases hr : σ.ret.toNom? <;> cases hp : ATy.nomList? σ.params <;>
    simp [ASig.toNom?, hr, hp] at h
  subst h
  simp [ASig.subst, ATy.map_subst_of_nomList? (θ := θ) hp, ATy.subst_of_toNom? hr]

/-! ## 5. Discharge is sound (§7.6, §8.2)

The two decidable jobs of §8.2, each proved to imply its atom's denotation. This
is what makes Layer 3 **fully untrusted** (§9.3): the checker's `Bool` is
re-validated here, so a wrong `entail` cannot make a wrong theorem. -/

theorem dischargeNom_sound {D : Decls} {h : Heap} {τ : Ty} {n : String}
    {σ : Sig} (hok : DeclsOk D h) (hd : dischargeNom D τ n σ = true) :
    EntryOk D h τ n σ := by
  unfold dischargeNom at hd
  exact hok τ n σ (by simpa using hd)

theorem dischargeRow_sound {D : Decls} {θ : TyVar → Ty} {h : Heap} {c : String} {R : Row}
    (hok : DeclsOk D h) (hd : dischargeRow D c R = true) :
    denote D θ (.obl c R) h := by
  intro e he
  unfold dischargeRow at hd
  have hthis := (List.all_eq_true.mp hd) e he
  cases hn : e.2.toNom? with
  | none => rw [hn] at hthis; simp at hthis
  | some σ =>
    rw [hn] at hthis
    rw [ASig.subst_of_toNom? (θ := θ) hn]
    exact dischargeNom_sound hok hthis

/-- **Every requirement and obligation an assertion carries, discharged at once**
    — §7.7's `accept` condition. Note the `var` case is `false` in
    `dischargeAll`, which is §7.7's *"`Σ` has no free type variable at
    toplevel"*: a residual requirement on an unresolved receiver is not a verdict,
    it is the precondition §11 prints. -/
theorem dischargeAll_sound {D : Decls} {θ : TyVar → Ty} {h : Heap} {A : Assn}
    (hok : DeclsOk D h) (hd : dischargeAll D A = true) :
    (∀ r ∈ A.reqAtoms, denote D θ (.req r.1 r.2.1 r.2.2) h) ∧
      (∀ o ∈ A.oblAtoms, denote D θ (.obl o.1 o.2) h) := by
  unfold dischargeAll at hd
  obtain ⟨h1, h2⟩ := Bool.and_eq_true .. |>.mp hd
  refine ⟨fun r hr => ?_, fun o ho => dischargeRow_sound hok ((List.all_eq_true.mp h2) o ho)⟩
  have hthis := (List.all_eq_true.mp h1) r hr
  cases hty : r.1 with
  | var α => rw [hty] at hthis; simp at hthis
  | nilOf a => rw [hty] at hthis; simp at hthis
  | nom τ =>
    rw [hty] at hthis
    cases hn : r.2.2.toNom? with
    | none => rw [hn] at hthis; simp at hthis
    | some σ =>
      rw [hn] at hthis
      dsimp only at hthis ⊢
      show EntryOk D h ((ATy.nom τ).subst θ) r.2.1 (r.2.2.subst θ)
      rw [ASig.subst_of_toNom? (θ := θ) hn]
      exact dischargeNom_sound hok hthis

/-! ## 6. Entailment is sound (§9.2's fourth owed item)

`entail_sound : entail P Q = true → ∀ m, ⟦P⟧ m → ⟦Q⟧ m`. -/

theorem denote_of_mem_declAtoms {D : Decls} {θ : TyVar → Ty} {h : Heap} :
    ∀ {A : Assn} {τ : Ty} {n : String} {σ : Sig},
      denote D θ A h → (τ, n, σ) ∈ A.declAtoms → EntryOk D h τ n σ := by
  intro A
  induction A with
  | emp => intro _ _ _ _ hm; simp [Assn.declAtoms] at hm
  | and A B ihA ihB =>
    intro τ n σ hd hm
    rcases List.mem_append.mp hm with hm | hm
    · exact ihA hd.1 hm
    · exact ihB hd.2 hm
  | decl τ' n' σ' =>
    intro τ n σ hd hm
    simp only [Assn.declAtoms, List.mem_singleton, Prod.mk.injEq] at hm
    obtain ⟨rfl, rfl, rfl⟩ := hm
    exact hd
  | req => intro _ _ _ _ hm; simp [Assn.declAtoms] at hm
  | obl => intro _ _ _ _ hm; simp [Assn.declAtoms] at hm

theorem entailAtom_sound {D : Decls} {θ : TyVar → Ty} {h : Heap} {A : Assn}
    {τ : Ty} {n : String} {σ : Sig}
    (hd : denote D θ A h) (he : entailAtom A τ n σ = true) : EntryOk D h τ n σ := by
  unfold entailAtom at he
  exact denote_of_mem_declAtoms hd (by simpa using List.mem_of_elem_eq_true he)

/-- The induction that `entail_sound` is the specialization of. The three
    premises are arguments rather than context hypotheses because they mention
    `Q`, and an `induction Q` that reverts them produces a dependent `match` in
    every case — the shape of the statement is doing real work here. -/
theorem entail_sound' {D : Decls} {θ : TyVar → Ty} {h : Heap} {P : Assn}
    (hp : denote D θ P h) : ∀ Q : Assn,
    (Q.declAtoms.all fun a => entailAtom P a.1 a.2.1 a.2.2) = true →
    (Q.reqAtoms.all fun r =>
        match r.1, r.2.2.toNom? with
        | .nom τ, some σ => entailAtom P τ r.2.1 σ
        | _, _ => false) = true →
    (Q.oblAtoms.all fun o =>
        o.2.entries.all fun e =>
          match e.2.toNom? with
          | some σ => entailAtom P (nomTy o.1) e.1 σ
          | none => false) = true →
    denote D θ Q h := by
  intro Q
  induction Q with
  | emp => intro _ _ _; trivial
  | and A B ihA ihB =>
    intro h1 h2 h3
    simp only [Assn.declAtoms, Assn.reqAtoms, Assn.oblAtoms, List.all_append,
      Bool.and_eq_true] at h1 h2 h3
    exact ⟨ihA h1.1 h2.1 h3.1, ihB h1.2 h2.2 h3.2⟩
  | decl τ n σ =>
    intro h1 _ _
    exact entailAtom_sound hp (by simpa [Assn.declAtoms] using h1)
  | req aτ n σ =>
    intro _ h2 _
    simp only [Assn.reqAtoms, List.all_cons, List.all_nil, Bool.and_true] at h2
    cases hn : σ.toNom? with
    | none => cases aτ <;> rw [hn] at h2 <;> simp at h2
    | some σn =>
      cases aτ with
      | var α => rw [hn] at h2; simp at h2
      | nilOf a => rw [hn] at h2; simp at h2
      | nom τ =>
        rw [hn] at h2
        show EntryOk D h ((ATy.nom τ).subst θ) n (σ.subst θ)
        rw [ASig.subst_of_toNom? (θ := θ) hn]
        exact entailAtom_sound hp h2
  | obl c R =>
    intro _ _ h3
    simp only [Assn.oblAtoms, List.all_cons, List.all_nil, Bool.and_true] at h3
    intro e he'
    have h2 := (List.all_eq_true.mp h3) e he'
    cases hn : e.2.toNom? with
    | none => rw [hn] at h2; simp at h2
    | some σn =>
      rw [hn] at h2
      rw [ASig.subst_of_toNom? (θ := θ) hn]
      exact entailAtom_sound hp h2

/-- **`entail_sound`** — §9.2's item 4, and the reason Layer 3 can be untrusted:
    whatever search produced the entailment, the theorem is re-derived here from
    `⟦P⟧` alone. -/
theorem entail_sound {D : Decls} {θ : TyVar → Ty} {h : Heap} {P Q : Assn}
    (he : entail P Q = true) (hp : denote D θ P h) : denote D θ Q h := by
  unfold entail at he
  obtain ⟨he12, he3⟩ := Bool.and_eq_true .. |>.mp he
  obtain ⟨he1, he2⟩ := Bool.and_eq_true .. |>.mp he12
  exact entail_sound' hp Q he1 he2 he3

/-! ## 7. The invariant, in assertion form — and soundness, inherited

This is §9.2's `Inv` with `RowsOk P m.heap` where `DeclsOk F m.heap` stood, and
`P` existentially quantified beside `F`. The point of `denote_declAssn` is that
this costs **nothing**: `InvA` and `Inv` are the same predicate, so `sound_from`'s
eleven consecution cases apply unchanged. §12 R5's payoff, without R5's bill. -/

/-- **The certificate condition.** `P` is *any* assertion strong enough to supply
    the table's atoms — not necessarily the canonical `declAssn F`. That
    generality is Layer 3's whole job: an untrusted engine emits some `P`, and
    `entail_sound` plus this predicate is what a validator re-checks
    (`type-safety-by-reachability.md` §4, and §8.4's certifying stance). -/
def Certifies (F : Decls) (θ : TyVar → Ty) (P : Assn) (h : Heap) : Prop :=
  denote F θ P h ∧ ∀ τ n d, declFor F τ n = some d → entailAtom P τ n d = true

theorem Certifies.declsOk {F : Decls} {θ : TyVar → Ty} {P : Assn} {h : Heap}
    (hc : Certifies F θ P h) : DeclsOk F h :=
  fun τ n d hdf => entailAtom_sound hc.1 (hc.2 τ n d hdf)

/-- The canonical certificate: the table's own re-notation certifies it. -/
theorem certifies_declAssn {F : Decls} {θ : TyVar → Ty} {h : Heap} (hok : DeclsOk F h) :
    Certifies F θ (declAssn F) h :=
  ⟨denote_declAssn.mpr hok,
   fun τ n d hdf => by
     unfold entailAtom
     have hm : Assn.decl τ n d ∈ (declAtoms F).map (fun a => Assn.decl a.1 a.2.1 a.2.2) :=
       List.mem_map_of_mem (f := fun a => Assn.decl a.1 a.2.1 a.2.2)
         (mem_declAtoms_iff.mpr hdf)
     have : (τ, n, d) ∈ (declAssn F).declAtoms := by
       unfold declAssn
       rw [show ∀ (L : List Assn), (Assn.all L).declAtoms
             = L.flatMap Assn.declAtoms from ?_]
       · exact List.mem_flatMap.mpr ⟨_, hm, by simp [Assn.declAtoms]⟩
       · intro L
         induction L with
         | nil => simp [Assn.all, Assn.declAtoms]
         | cons A rest ih =>
           cases rest with
           | nil => simp [Assn.all]
           | cons B rest' => simp only [Assn.all, Assn.declAtoms, List.flatMap_cons] at *; rw [ih]
     simpa using List.elem_eq_true_of_mem this⟩

/-- **`Inv`, stated over the assertion language.** Compare `Static/Konts.lean`'s
    `Inv`: the `DeclsOk F m.heap` conjunct has become *there exists a certificate
    `P` whose denotation supplies it*. -/
def InvA (m : Machine) : Prop :=
  NoHook m.heap ∧ Saturated m.heap ∧ LitClsOk m.heap ∧
    ClassOk m.heap ∧ BottomObj m.frames m.stack ∧
    ∃ (F : Decls) (P : Assn) (θ : TyVar → Ty) (c : FrameCtx) (Γ : Env)
      (Γs : List (FrameCtx × Env)),
      Certifies F θ P m.heap ∧
      FramesOk m.heap m.frames m.stack (Γ :: Γs.map Prod.snd) ∧
      StackCtx m.heap m.frames m.stack (c :: Γs.map Prod.fst) ∧
      CtlOk F c Γ Γs m

/-- **The two invariants are the same predicate.** The forward direction is
    `Certifies.declsOk`; the backward one is `certifies_declAssn`, which is where
    faithfulness is spent. -/
theorem invA_iff_inv {m : Machine} : InvA m ↔ Inv m := by
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, F, P, θ, c, Γ, Γs, hcert, hf, hs, hctl⟩
    exact ⟨h1, h2, h3, h4, h5, F, c, Γ, Γs, hcert.declsOk, hf, hs, hctl⟩
  · rintro ⟨h1, h2, h3, h4, h5, F, c, Γ, Γs, hok, hf, hs, hctl⟩
    exact ⟨h1, h2, h3, h4, h5, F, declAssn F, fun _ => .int, c, Γ, Γs,
      certifies_declAssn hok, hf, hs, hctl⟩

/-- **Soundness of the assertion-language invariant**, inherited rather than
    re-proved. Every consecution case `Static/Preservation.lean` already closes is
    reused verbatim — which is the whole argument of this file's header. -/
theorem assn_sound_from {m₀ : Machine} (h : InvA m₀) :
    ∀ r, ReachableResult m₀ r → ¬ typeStuck r :=
  sound_from (invA_iff_inv.mp h)

/-- The two facts available at an accepting program's starting configuration.

    **Read the `∧` as a conjunction, not as a chain.** The first conjunct is this
    file's contribution — §9.2's `init` obligation, discharged: an
    assertion-language certificate holds at the boot heap. The second is
    `check_sound` **verbatim**, and the assertion language contributes *nothing*
    to it.

    Stated together because a certificate is only interesting alongside the
    theorem it certifies for, and stated with this warning because the obvious
    misreading — *"the assertion language proves `¬ typeStuck`"* — is false. It
    proves that the assertion is a faithful re-notation of the invariant that
    already proved it (`denote_declAssn`), which is a different and weaker claim,
    and the honest one. **The set of programs known not to type-stick is
    unchanged**: exactly those `check` accepts, which is why `--check` is
    byte-identical across this rung. -/
theorem assn_check_sound {p : Expr} (hc : check p = .accept) :
    (∃ P : Assn, ∀ θ, Certifies (declsOf p) θ P (Machine.init p).heap) ∧
      ∀ r, ReachableResult (Machine.init p) r → ¬ typeStuck r := by
  -- `initiation` pins the table the run starts at to `declsOf p`, and the
  -- `DeclsOk` it establishes there is F1a's own — `tableOk_declsOk` at the boot
  -- heap. `certifies_declAssn` turns it into a certificate; `check_sound` is
  -- unchanged and does the rest.
  exact ⟨⟨declAssn (declsOf p),
          fun θ => certifies_declAssn (tableOk_declsOk tableOk_initHeap)⟩,
         check_sound hc⟩

/-! ## 8. Checked facts -/

/-- The base table's re-notation certifies it at the boot heap — the concrete
    instance of §9.2's `init` obligation, and the first assertion in this project
    with a proof that it holds of a real heap. -/
theorem certifies_base_initHeap (θ : TyVar → Ty) :
    Certifies baseDecls θ (declAssn baseDecls) Boot.initHeap :=
  certifies_declAssn (tableOk_declsOk tableOk_initHeap)

/-- An entailment used, end to end: the base table's assertion entails the
    requirement `Integer ~ + : (Integer) → Integer`, and `entail_sound` turns
    that `Bool` into the `EntryOk` the send case consumes. -/
example (θ : TyVar → Ty) :
    denote baseDecls θ
        (.req (.nom .int) "+" { params := [.nom .int], ret := .nom .int })
      Boot.initHeap :=
  entail_sound (P := declAssn baseDecls)
    (by decide) (certifies_base_initHeap θ).1

/-! Axiom hygiene — the same three, and in particular the faithfulness theorem
and the inherited soundness carry nothing new. -/
/-- info: 'RubyCore.Proof.Static.denote_declAssn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms denote_declAssn

/-- info: 'RubyCore.Proof.Static.assn_check_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms assn_check_sound

end Static
end Proof
end RubyCore
