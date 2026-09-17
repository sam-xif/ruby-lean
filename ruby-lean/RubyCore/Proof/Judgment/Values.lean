import RubyCore.Proof.Static.Konts
import RubyCore.Judgment.Sub

/-!
# `VTy` — the value judgment of the machine-typing layer (J19)

the judgment-layer note §3's machine typing is authored over `Judge`, whose type language
includes unions (L269) — and `ValueTy` is `subTy`-up-closed, so `ValueTy h v (.union
a b)` is *uninhabited* (`subTy` compares a union by equality and `valueTy?` never
answers one). This is the union disjunction arm J14 named as "the J1 obligation", paid
without touching `ValueTy`: `VTy` closes `ValueTy` under `SubJ` instead —

    VTy h v τ  :=  ∃ σ, ValueTy h v σ ∧ SubJ σ τ

Everything the old spine knows about values transfers by one composition each
(`weaken` is `SubJ.trans`, `congr` is `ValueTy.congr`), and the bridge *back* —
`VTy.toValueTy`, at a `groundTy` (union- and arrow-free) type — is what lets every
dispatch lemma of `Proof/Static/` be reused verbatim: `sigOf` answers only at ground
receiver types, so the send cases convert and proceed as before.

Arrows deliberately have **no** value-level witness here (a `VTy` at an arrow type is
uninhabited, like `ValueTy` at one): the machine-typed fragment of J1 excludes the
lambda-arrow mint, so no reachable value needs one. The proc-atom disjunct is the
named bill of widening the fragment to `sendLambdaArrow`/`sendCall` (J16's bill,
unchanged in position).
-/

namespace RubyCore
namespace Proof
namespace Judgment

open Interp
open RubyCore.Types
open RubyCore.Judgment
open RubyCore.Proof.Static

/-- The value judgment: the exact-type layer (`ValueTy`, unchanged) below the
    declarative subtype relation. -/
def VTy (h : Heap) (v : Value) (τ : Ty) : Prop :=
  ∃ σ, ValueTy h v σ ∧ SubJ σ τ

theorem VTy.ofValueTy {h : Heap} {v : Value} {τ : Ty} (hv : ValueTy h v τ) :
    VTy h v τ := ⟨τ, hv, SubJ.refl τ⟩

theorem VTy.exact {h : Heap} {v : Value} {τ : Ty} (he : valueTy? h v = some τ) :
    VTy h v τ := .ofValueTy (ValueTy.exact he)

theorem VTy.any {h : Heap} {v : Value} : VTy h v .any := .ofValueTy ValueTy.any

theorem VTy.weaken {h : Heap} {v : Value} {σ τ : Ty} (hv : VTy h v σ)
    (hs : SubJ σ τ) : VTy h v τ :=
  let ⟨σ₀, hv₀, hs₀⟩ := hv
  ⟨σ₀, hv₀, hs₀.trans hs⟩

theorem VTy.weakenB {h : Heap} {v : Value} {σ τ : Ty} (hv : VTy h v σ)
    (hs : subTy σ τ = true) : VTy h v τ := hv.weaken (.base hs)

theorem VTy.congr {h h' : Heap} {v : Value} {τ : Ty} (ha : TypeAgree h h')
    (hv : VTy h v τ) : VTy h' v τ :=
  let ⟨σ, hv₀, hs⟩ := hv
  ⟨σ, ValueTy.congr ha hv₀, hs⟩

/-! ## The ground fragment of the type language, and the bridge back to `ValueTy` -/

/-- `valueTy?`'s whole range is ground — it answers primitive atoms and class
    names, never a union, arrow, or nilable. -/
theorem valueTy?_ground {h : Heap} {v : Value} {σ : Ty}
    (he : valueTy? h v = some σ) : groundTy σ = true := by
  cases v <;> simp only [valueTy?, Option.some.injEq] at he
  case ref o =>
    split at he
    · simp only [Option.some.injEq] at he
      subst he
      simp [groundTy]
    · split at he
      · simp only [Option.some.injEq] at he
        subst he
        simp [groundTy]
      · exact absurd he (by simp)
  all_goals (subst he; simp [groundTy])

/-- `ValueTy` at a union is uninhabited — the fact that makes `SubJ`'s `unionL`
    case of the bridge vacuous, and the reason `VTy` exists at all. -/
theorem valueTy_union_false {h : Heap} {v : Value} {a b : Ty}
    (hv : ValueTy h v (.union a b)) : False := by
  rcases hv with hany | ⟨σ', o, xs, hup, -⟩ | ⟨σ, hσ, hs⟩
  · exact absurd hany (by simp [subTy])
  · exact absurd hup (by simp [subTy])
  · simp only [subTy, beq_iff_eq] at hs
    subst hs
    exact absurd (valueTy?_ground hσ) (by simp [groundTy])

/-- `ValueTy` at a `.nilable`, decomposed with no side conditions: the value
    inhabits `nilT`, or it inhabits the payload. (`valueTy_nilable_inv` answers `v =
    .nil ∨ …` but demands the payload be atomic; the bridge below recurses through
    nested nilables, so it needs this shape.) -/
theorem valueTy_nilable_cases {h : Heap} {v : Value} {s : Ty}
    (hv : ValueTy h v (.nilable s)) : ValueTy h v .nilT ∨ ValueTy h v s := by
  rcases hv with hany | ⟨σ', o, xs, hup, hvo, hb, hex, hpay, hall⟩ | ⟨σ, hσ, hs⟩
  · simp only [subTy, Bool.or_eq_true, beq_iff_eq] at hany
    rcases hany with (h1 | h1) | h1
    · exact absurd h1 (by simp)
    · exact absurd h1 (by simp)
    · exact Or.inr (Or.inl h1)
  · simp only [subTy, Bool.or_eq_true, beq_iff_eq] at hup
    rcases hup with (h1 | h1) | h1
    · exact absurd h1 (by simp)
    · exact absurd h1 (by simp)
    · exact Or.inr (Or.inr (Or.inl ⟨σ', o, xs, h1, hvo, hb, hex, hpay, hall⟩))
  · simp only [subTy, Bool.or_eq_true, beq_iff_eq] at hs
    rcases hs with (rfl | rfl) | h1
    · exact Or.inl (ValueTy.exact hσ)
    · exact absurd hσ (fun hq => (valueTy_not_nilable hq).elim)
    · exact Or.inr (Or.inr (Or.inr ⟨σ, hσ, h1⟩))

/-- **The bridge**: below a ground type, the declarative widening adds nothing —
    `ValueTy` transports along `SubJ`. Induction on the derivation; the union rules
    are refuted on one side or the other, `nilableL` steps through
    `valueTy_nilable_cases`, `nilableR` re-weakens by `subTy`. -/
theorem valueTy_subJ {h : Heap} {v : Value} : ∀ {σ τ : Ty}, ValueTy h v σ →
    SubJ σ τ → groundTy τ = true → ValueTy h v τ := by
  intro σ τ hv hs
  induction hs with
  | base hb => exact fun _ => ValueTy.weaken hv hb
  | unionL _ _ _ _ => exact absurd hv valueTy_union_false
  | unionR1 _ _ => intro hg; exact absurd hg (by simp [groundTy])
  | unionR2 _ _ => intro hg; exact absurd hg (by simp [groundTy])
  | nilableL _ _ ihn ihs =>
    intro hg
    rcases valueTy_nilable_cases hv with h1 | h1
    · exact ihn h1 hg
    · exact ihs h1 hg
  | nilableR _ ih =>
    intro hg
    simp only [groundTy] at hg
    exact ValueTy.weaken (ih hv hg) (by simp [subTy])
  | arrow0 _ _ => intro hg; exact absurd hg (by simp [groundTy])
  | arrowCons _ _ _ _ => intro hg; exact absurd hg (by simp [groundTy])

theorem VTy.toValueTy {h : Heap} {v : Value} {τ : Ty} (hv : VTy h v τ)
    (hg : groundTy τ = true) : ValueTy h v τ :=
  let ⟨σ, hv₀, hs⟩ := hv
  valueTy_subJ hv₀ hs hg

/-! ## The narrowing kit's value side (J27) -/

/-- Falsiness has exactly two shapes. -/
theorem truthy_false_cases {v : Value} (h : v.truthy = false) :
    v = .nil ∨ v = .bool false := by
  cases v with
  | nil => exact Or.inl rfl
  | bool b =>
    cases b with
    | false => exact Or.inr rfl
    | true => exact absurd h (by simp [Value.truthy])
  | _ => exact absurd h (by simp [Value.truthy])

/-- A `nilT`-typed value is `nil` — through the ground bridge. -/
theorem vty_nilT_eq {h : Heap} {v : Value} (hv : VTy h v .nilT) : v = .nil :=
  valueTy_nilT (ValueTy.atomic (by simp) (by simp) (by simp)
    (hv.toValueTy (by simp [groundTy])))

/-- `nil` sits below anything it inhabits, at `nilT`. -/
theorem vty_nil_subJ {h : Heap} {τ : Ty} (hv : VTy h (.nil : Value) τ) :
    SubJ .nilT τ := by
  obtain ⟨σ, hσ, hs⟩ := hv
  rcases hσ with hany | ⟨σ', o, xs, hup, hvo, -⟩ | ⟨σ', h', hsub⟩
  · exact SubJ.trans (.base (subTy_trans (by simp [subTy]) hany)) hs
  · exact absurd hvo (by simp)
  · have hq : σ' = .nilT := by
      have := h'
      simp only [valueTy?, Option.some.injEq] at this
      exact this.symm
    subst hq
    exact SubJ.trans (.base hsub) hs

/-- …and `false`, at `bool`. -/
theorem vty_false_subJ {h : Heap} {τ : Ty} (hv : VTy h (.bool false) τ) :
    SubJ .bool τ := by
  obtain ⟨σ, hσ, hs⟩ := hv
  rcases hσ with hany | ⟨σ', o, xs, hup, hvo, -⟩ | ⟨σ', h', hsub⟩
  · exact SubJ.trans (.base (subTy_trans (by simp [subTy]) hany)) hs
  · exact absurd hvo (by simp)
  · have hq : σ' = .bool := by
      have := h'
      simp only [valueTy?, Option.some.injEq] at this
      exact this.symm
    subst hq
    exact SubJ.trans (.base hsub) hs

/-- Nothing `SubJ`-below `nilT`… (the wrong-direction twin lives in `Sub.lean`);
    here: nothing atom-shaped has `nilT` below it. -/
theorem subJ_nilT_below {a : Ty} (h : SubJ .nilT a) (h1 : a ≠ .nilT) (h2 : a ≠ .any)
    (h3 : ∀ τ', a ≠ .nilable τ') (h4 : ∀ x y, a ≠ .union x y) : False := by
  cases h with
  | base hb =>
    cases a <;> simp_all [subTy]
  | unionR1 _ => exact h4 _ _ rfl
  | unionR2 _ => exact h4 _ _ rfl
  | nilableR _ => exact h3 _ rfl

theorem subJ_bool_below {a : Ty} (h : SubJ .bool a) (h1 : a ≠ .bool) (h2 : a ≠ .any)
    (h3 : ∀ τ', a ≠ .nilable τ') (h4 : ∀ x y, a ≠ .union x y) : False := by
  cases h with
  | base hb =>
    cases a <;> simp_all [subTy]
  | unionR1 _ => exact h4 _ _ rfl
  | unionR2 _ => exact h4 _ _ rfl
  | nilableR _ => exact h3 _ rfl

/-- **The push-time atom analysis** (J27): every conforming value yields an atom
    `a` — its exact type, `.any`, or an `arrayOf` — carrying exactly the four
    facts the narrowing kont's delivery spends: the atom is below the original,
    below `dropNil` unless it *is* `nilT`, and below `elseNarrow` whenever the
    delivered value could be falsy (read off `SubJ nilT/bool a`). -/
theorem vty_narrow_kit {h : Heap} {v : Value} {τ₀ : Ty} (hv : VTy h v τ₀) :
    ∃ a, VTy h v a ∧ SubJ a τ₀ ∧
      (a = .nilT ∨ SubJ a (dropNil τ₀)) ∧
      (SubJ .nilT a → SubJ a (elseNarrow τ₀)) ∧
      (SubJ .bool a → SubJ a (elseNarrow τ₀)) := by
  obtain ⟨σ, hσ, hs⟩ := hv
  have helse : ∀ b : Ty, SubJ b τ₀ → boolFree τ₀ = false → SubJ b (elseNarrow τ₀) := by
    intro b hb hbf
    unfold elseNarrow
    rw [hbf]
    simpa using hb
  rcases hσ with hany | ⟨σ', o, xs, hup, hvo, hb, hex, hpay, hall⟩ | ⟨a, h', hsub⟩
  · -- The `.any` disjunct: the atom is `.any` itself.
    refine ⟨.any, VTy.any, ?_, Or.inr ?_, fun _ => ?_, fun _ => ?_⟩
    · exact SubJ.trans (.base hany) hs
    · exact subJ_dropNil (SubJ.trans (.base hany) hs) (by simp) (by simp) (by simp)
    · exact helse _ (SubJ.trans (.base hany) hs)
        (boolFree_false_of_subJ (SubJ.trans (.base hany) hs) (Or.inr rfl))
    · exact helse _ (SubJ.trans (.base hany) hs)
        (boolFree_false_of_subJ (SubJ.trans (.base hany) hs) (Or.inr rfl))
  · -- The `arrayOf` disjunct: the atom is the parameterised type itself.
    refine ⟨.arrayOf σ', ?_, ?_, Or.inr ?_, fun hn => ?_, fun hf => ?_⟩
    · exact ⟨.arrayOf σ',
        Or.inr (Or.inl ⟨σ', o, xs, by simp, hvo, hb, hex, hpay, hall⟩), SubJ.refl _⟩
    · exact SubJ.trans (.base hup) hs
    · exact subJ_dropNil (SubJ.trans (.base hup) hs) (by simp) (by simp) (by simp)
    · exact absurd hn (fun hq => subJ_nilT_below hq (by simp) (by simp) (by simp) (by simp))
    · exact absurd hf (fun hq => subJ_bool_below hq (by simp) (by simp) (by simp) (by simp))
  · -- The exact disjunct: the atom is `valueTy?`'s answer.
    have ha0 : SubJ a τ₀ := SubJ.trans (.base hsub) hs
    have hgnd := valueTy?_ground h'
    have hnn : ∀ τ', a ≠ .nilable τ' := fun τ' hq =>
      (valueTy_not_nilable (hq ▸ h')).elim
    have hnu : ∀ x y, a ≠ .union x y := fun x y hq => by
      rw [hq] at hgnd
      simp [groundTy] at hgnd
    have hna : a ≠ .any := fun hq => by
      cases v <;> simp only [valueTy?, Option.some.injEq] at h'
      case ref o =>
        split at h'
        · simp only [Option.some.injEq] at h'; rw [hq] at h'; simp at h'
        · split at h'
          · simp only [Option.some.injEq] at h'; rw [hq] at h'; simp at h'
          · exact absurd h' (by simp)
      all_goals (rw [hq] at h'; simp at h')
    refine ⟨a, VTy.exact h', ha0, ?_, fun hn => ?_, fun hf => ?_⟩
    · by_cases hq : a = .nilT
      · exact Or.inl hq
      · exact Or.inr (subJ_dropNil ha0 hq hnn hnu)
    · by_cases hq : a = .nilT
      · subst hq
        by_cases hbf : boolFree τ₀ = true
        · unfold elseNarrow
          rw [hbf]
          exact SubJ.refl _
        · exact helse _ ha0 (by simpa using hbf)
      · exact absurd hn (fun hh => subJ_nilT_below hh hq hna hnn hnu)
    · by_cases hq : a = .bool
      · subst hq
        exact helse _ ha0 (boolFree_false_of_subJ ha0 (Or.inl rfl))
      · exact absurd hf (fun hh => subJ_bool_below hh hq hna hnn hnu)

/-! ## The list forms -/

/-- Pointwise `VTy`, arity-forcing — `ValuesTy`'s shape over the widened value
    judgment. -/
def VTys (h : Heap) : List Value → List Ty → Prop
  | [], [] => True
  | v :: vs, τ :: τs => VTy h v τ ∧ VTys h vs τs
  | _, _ => False

theorem VTys.ofValuesTy {h : Heap} : ∀ {vs : List Value} {τs : List Ty},
    ValuesTy h vs τs → VTys h vs τs
  | [], [], _ => trivial
  | _ :: _, _ :: _, h' => by
    obtain ⟨⟨σ, hv, hs⟩, hrest⟩ := h'
    exact ⟨⟨σ, hv, .base hs⟩, VTys.ofValuesTy hrest⟩
  | [], _ :: _, h' => absurd h' (by simp [ValuesTy])
  | _ :: _, [], h' => absurd h' (by simp [ValuesTy])

theorem VTys.weaken {h : Heap} : ∀ {vs : List Value} {σs τs : List Ty},
    VTys h vs σs → SubJs σs τs → VTys h vs τs
  | [], [], [], _, .nil => trivial
  | _ :: _, _ :: _, _ :: _, hv, .cons hs hss =>
    ⟨hv.1.weaken hs, VTys.weaken hv.2 hss⟩
  | [], _ :: _, _, hv, _ => absurd hv (by simp [VTys])
  | _ :: _, [], _, hv, _ => absurd hv (by simp [VTys])

theorem VTys.congr {h h' : Heap} (ha : TypeAgree h h') : ∀ {vs : List Value}
    {τs : List Ty}, VTys h vs τs → VTys h' vs τs
  | [], [], _ => trivial
  | _ :: _, _ :: _, hv => ⟨hv.1.congr ha, VTys.congr ha hv.2⟩
  | [], _ :: _, hv => absurd hv (by simp [VTys])
  | _ :: _, [], hv => absurd hv (by simp [VTys])

theorem VTys.snoc {h : Heap} : ∀ {vs : List Value} {τs : List Ty} {v : Value} {τ : Ty},
    VTys h vs τs → VTy h v τ → VTys h (vs ++ [v]) (τs ++ [τ])
  | [], [], _, _, _, hv => ⟨hv, trivial⟩
  | _ :: _, _ :: _, _, _, hvs, hv => ⟨hvs.1, VTys.snoc hvs.2 hv⟩
  | [], _ :: _, _, _, hvs, _ => absurd hvs (by simp [VTys])
  | _ :: _, [], _, _, hvs, _ => absurd hvs (by simp [VTys])

/-- The bridge back for argument lists: below ground parameter types, `VTys` *is*
    `ValuesTy` — which is what lets `entry_dispatch` be reused unchanged. -/
theorem VTys.toValuesTy {h : Heap} : ∀ {vs : List Value} {τs : List Ty},
    VTys h vs τs → (∀ τ ∈ τs, groundTy τ = true) → ValuesTy h vs τs
  | [], [], _, _ => trivial
  | _ :: _, τ :: _, hv, hg =>
    ⟨⟨τ, hv.1.toValueTy (hg τ (by simp)), subTy_refl τ⟩,
     VTys.toValuesTy hv.2 (fun τ' hm => hg τ' (by simp [hm]))⟩
  | [], _ :: _, hv, _ => absurd hv (by simp [VTys])
  | _ :: _, [], hv, _ => absurd hv (by simp [VTys])

end Judgment
end Proof
end RubyCore
