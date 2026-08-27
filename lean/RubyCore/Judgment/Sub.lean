import RubyCore.Types.Core

/-!
# `SubJ` — declarative subtyping, and the narrowing operators

The union arm of `Ty` (L269) is **inert on the checker path**: `subTy` compares it
by equality, so `chk`/`infer` behavior is byte-identical and `subTy` stays
structurally recursive (norm 5). The union's *meaning* lives here, as an inductive
relation — the declarative counterpart, with `subTy` embedded by `base` (so `SubJ`
is a strict widening: everything `subTy` admits, plus union/nilable decomposition
on both sides).

Why a relation and not a widened `subTy`: a left-decomposing `subTy` cannot stay
structurally recursive on `τ` (it must recurse on `σ` too), and a well-founded
`subTy` stops kernel-reducing under `chk` — the L73 trap, hit at design time
instead of at build time. The judgment does not need decidability; the eventual
algorithmic form is a `Deriv`-checker concern (J2), where the derivation itself
records which rule applies.
-/

namespace RubyCore.Judgment

open RubyCore.Types

/-- Declarative subtyping. `base` embeds the checker-path `subTy` whole (including
    its `any`/`nilable` clauses); the four structural rules decompose unions on
    both sides and a nilable on the left (`nilable σ` = `nilT ∪ σ`, so it goes
    below `τ` when both halves do — the clause `subTy` cannot state because its
    left side never decomposes). -/
inductive SubJ : Ty → Ty → Prop where
  | base {σ τ} : subTy σ τ = true → SubJ σ τ
  | unionL {a b τ} : SubJ a τ → SubJ b τ → SubJ (.union a b) τ
  | unionR1 {σ a b} : SubJ σ a → SubJ σ (.union a b)
  | unionR2 {σ a b} : SubJ σ b → SubJ σ (.union a b)
  | nilableL {σ τ} : SubJ .nilT τ → SubJ σ τ → SubJ (.nilable σ) τ
  -- L270: the arrow spine's variance, cell by cell — **contravariant** parameters
  -- (the wider arrow must accept at least what the narrower accepted, so the premise
  -- runs q ≤ p, right-to-left) and **covariant** return. Arity mismatches refuse
  -- structurally: an `arrowCons` is never below an `arrow0`, which is the
  -- `ArgumentError` family's condition showing up as a shape constraint.
  | arrow0 {r s} : SubJ r s → SubJ (.arrow0 r) (.arrow0 s)
  | arrowCons {p q rest rest'} :
      SubJ q p → SubJ rest rest' → SubJ (.arrowCons p rest) (.arrowCons q rest')
  -- **J18: the nilable-*right* lift, added because its absence breaks transitivity.**
  -- Without it `int ≤ int ∪ bool` (unionR1) and `int ∪ bool ≤ nilable (int ∪ bool)`
  -- (base, `subTy`'s reflexive third disjunct) compose to a judgment with no
  -- derivation: `base` computes to `int = int ∪ bool`, `unionR` needs a union on the
  -- right, `nilableL` a nilable on the left. Semantically free — `nilable τ` is
  -- "nil or τ", so a subset of `τ` is a subset of it — and a strict widening, so
  -- every existing derivation stands. `SubJ.trans` below is the consumer.
  | nilableR {σ τ} : SubJ σ τ → SubJ σ (.nilable τ)

theorem SubJ.refl (τ : Ty) : SubJ τ τ := .base (subTy_refl τ)

/-- `subTy`'s shape, read backwards — the case split `SubJ.trans` runs on whenever a
    `base` step meets a structural one. Directly from the definition: everything is
    below `.any`, a `.nilable` admits its three disjuncts, and every other right side
    is equality. -/
theorem subTy_cases {σ τ : Ty} (h : subTy σ τ = true) :
    τ = .any ∨ (∃ τ', τ = .nilable τ' ∧
      (σ = .nilT ∨ σ = .nilable τ' ∨ subTy σ τ' = true)) ∨ σ = τ := by
  cases τ with
  | any => exact Or.inl rfl
  | nilable τ' =>
    refine Or.inr (Or.inl ⟨τ', rfl, ?_⟩)
    simpa [subTy, or_assoc] using h
  | _ => exact Or.inr (Or.inr (by simpa [subTy] using h))

/-- Every type's size is positive — the arithmetic side conditions of `SubJ.trans`
    need it where a premise's type is a fixed constructor (`nilT`). -/
theorem ty_sizeOf_pos (t : Ty) : 0 < sizeOf t := by
  cases t <;> simp <;> omega

/-- **Transitivity** (J18). By strong induction on the summed sizes of the three
    types: every structural rule's premises are about strictly smaller types, and a
    `base` step against a structural one is decided by `subTy_cases` — with
    `nilableR` supplying exactly the lift the un-widened relation lacked. -/
theorem SubJ.trans : ∀ {a b c : Ty}, SubJ a b → SubJ b c → SubJ a c := by
  intro a b c h1 h2
  induction hn : sizeOf a + sizeOf b + sizeOf c using Nat.strongRecOn
    generalizing a b c with
  | _ n ih =>
  subst hn
  -- The recursive entry point, at a smaller triple.
  have trc : ∀ {a' b' c' : Ty}, SubJ a' b' → SubJ b' c' →
      sizeOf a' + sizeOf b' + sizeOf c' < sizeOf a + sizeOf b + sizeOf c →
      SubJ a' c' := fun h1' h2' hlt => ih _ hlt h1' h2' rfl
  cases h1 with
  | base s1 =>
    cases h2 with
    | base s2 => exact .base (subTy_trans s1 s2)
    | unionL hx hy =>
      -- `subTy a (union x y)` is equality at a union, so `a` *is* the middle.
      simp only [subTy, beq_iff_eq] at s1
      subst s1
      exact .unionL hx hy
    | unionR1 hu => exact .unionR1 (trc (.base s1) hu (by simp <;> omega))
    | unionR2 hv => exact .unionR2 (trc (.base s1) hv (by simp <;> omega))
    | nilableL hn hs =>
      rename_i s
      simp only [subTy, Bool.or_eq_true, beq_iff_eq] at s1
      rcases s1 with (rfl | rfl) | hd
      · exact hn
      · exact .nilableL hn hs
      · exact trc (.base hd) hs (by simp <;> omega)
    | nilableR hc => exact .nilableR (trc (.base s1) hc (by simp <;> omega))
    | arrow0 hr =>
      simp only [subTy, beq_iff_eq] at s1
      subst s1
      exact .arrow0 hr
    | arrowCons hq hr =>
      simp only [subTy, beq_iff_eq] at s1
      subst s1
      exact .arrowCons hq hr
  | unionL hx hy =>
    exact .unionL (trc hx h2 (by simp <;> omega)) (trc hy h2 (by simp <;> omega))
  | unionR1 hu =>
    rename_i x y
    -- `b = union x y`, `a ≤ x`; strip the middle by cases on the second derivation.
    cases h2 with
    | base s2 =>
      rcases subTy_cases s2 with heq | ⟨τ', rfl, hd⟩ | rfl
      · rw [heq]; exact .base (by simp [subTy])
      · rcases hd with h' | h' | hd
        · exact absurd h' (by simp)
        · exact absurd h' (by simp)
        · exact .nilableR (trc (.unionR1 hu) (.base hd) (by simp <;> omega))
      · exact .unionR1 hu
    | unionL hx hy => exact trc hu hx (by simp <;> omega)
    | unionR1 hp => exact .unionR1 (trc (.unionR1 hu) hp (by simp <;> omega))
    | unionR2 hq => exact .unionR2 (trc (.unionR1 hu) hq (by simp <;> omega))
    | nilableR hc => exact .nilableR (trc (.unionR1 hu) hc (by simp <;> omega))
  | unionR2 hv =>
    rename_i x y
    cases h2 with
    | base s2 =>
      rcases subTy_cases s2 with heq | ⟨τ', rfl, hd⟩ | rfl
      · rw [heq]; exact .base (by simp [subTy])
      · rcases hd with h' | h' | hd
        · exact absurd h' (by simp)
        · exact absurd h' (by simp)
        · exact .nilableR (trc (.unionR2 hv) (.base hd) (by simp <;> omega))
      · exact .unionR2 hv
    | unionL hx hy => exact trc hv hy (by simp <;> omega)
    | unionR1 hp => exact .unionR1 (trc (.unionR2 hv) hp (by simp <;> omega))
    | unionR2 hq => exact .unionR2 (trc (.unionR2 hv) hq (by simp <;> omega))
    | nilableR hc => exact .nilableR (trc (.unionR2 hv) hc (by simp <;> omega))
  | nilableL hn hs =>
    rename_i s
    refine .nilableL (trc hn h2 ?_) (trc hs h2 (by simp <;> omega))
    have hp := ty_sizeOf_pos s
    simp <;> omega
  | nilableR hb =>
    rename_i b'
    cases h2 with
    | base s2 =>
      rcases subTy_cases s2 with heq | ⟨τ', rfl, hd⟩ | rfl
      · rw [heq]; exact .base (by simp [subTy])
      · rcases hd with h' | h' | hd
        · exact absurd h' (by simp)
        · injection h' with h'
          subst h'
          exact .nilableR hb
        · exact .nilableR (trc (.nilableR hb) (.base hd) (by simp <;> omega))
      · exact .nilableR hb
    | unionR1 hp => exact .unionR1 (trc (.nilableR hb) hp (by simp <;> omega))
    | unionR2 hq => exact .unionR2 (trc (.nilableR hb) hq (by simp <;> omega))
    | nilableL hn hs => exact trc hb hs (by simp <;> omega)
    | nilableR hc => exact .nilableR (trc (.nilableR hb) hc (by simp <;> omega))
  | arrow0 hr =>
    rename_i r s2'
    cases h2 with
    | base s =>
      rcases subTy_cases s with heq | ⟨τ', rfl, hd⟩ | rfl
      · rw [heq]; exact .base (by simp [subTy])
      · rcases hd with h' | h' | hd
        · exact absurd h' (by simp)
        · exact absurd h' (by simp)
        · exact .nilableR (trc (.arrow0 hr) (.base hd) (by simp <;> omega))
      · exact .arrow0 hr
    | unionR1 hp => exact .unionR1 (trc (.arrow0 hr) hp (by simp <;> omega))
    | unionR2 hq => exact .unionR2 (trc (.arrow0 hr) hq (by simp <;> omega))
    | nilableR hc => exact .nilableR (trc (.arrow0 hr) hc (by simp <;> omega))
    | arrow0 ht => exact .arrow0 (trc hr ht (by simp <;> omega))
  | arrowCons hq hr =>
    rename_i p q rest rest'
    cases h2 with
    | base s =>
      rcases subTy_cases s with heq | ⟨τ', rfl, hd⟩ | rfl
      · rw [heq]; exact .base (by simp [subTy])
      · rcases hd with h' | h' | hd
        · exact absurd h' (by simp)
        · exact absurd h' (by simp)
        · exact .nilableR (trc (.arrowCons hq hr) (.base hd) (by simp <;> omega))
      · exact .arrowCons hq hr
    | unionR1 hp => exact .unionR1 (trc (.arrowCons hq hr) hp (by simp <;> omega))
    | unionR2 hp => exact .unionR2 (trc (.arrowCons hq hr) hp (by simp <;> omega))
    | nilableR hc => exact .nilableR (trc (.arrowCons hq hr) hc (by simp <;> omega))
    | arrowCons hq2 hr2 =>
      exact .arrowCons (trc hq2 hq (by simp <;> omega)) (trc hr hr2 (by simp <;> omega))

/-- Pointwise, at the declared arity — `subTys`' shape over `SubJ`. -/
inductive SubJs : List Ty → List Ty → Prop where
  | nil : SubJs [] []
  | cons {σ τ σs τs} : SubJ σ τ → SubJs σs τs → SubJs (σ :: σs) (τ :: τs)

theorem SubJs.refl : ∀ (τs : List Ty), SubJs τs τs
  | [] => .nil
  | _ :: τs => .cons (SubJ.refl _) (SubJs.refl τs)

theorem SubJs.of_subTys : ∀ {σs τs : List Ty}, subTys σs τs = true → SubJs σs τs
  | [], [], _ => .nil
  | _ :: _, _ :: _, h => by
    simp only [subTys, Bool.and_eq_true] at h
    exact .cons (.base h.1) (SubJs.of_subTys h.2)
  | [], _ :: _, h => by simp [subTys] at h
  | _ :: _, [], h => by simp [subTys] at h

theorem SubJs.trans : ∀ {a b c : List Ty}, SubJs a b → SubJs b c → SubJs a c
  | [], [], [], .nil, .nil => .nil
  | _ :: _, _ :: _, _ :: _, .cons h hs, .cons h' hs' =>
      .cons (h.trans h') (SubJs.trans hs hs')

theorem SubJs.length : ∀ {a b : List Ty}, SubJs a b → a.length = b.length
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons _ hs => by simp [SubJs.length hs]

theorem SubJs.nil_inv {ps : List Ty} (h : SubJs [] ps) : ps = [] := by
  cases h; rfl

theorem SubJs.cons_inv {σ : Ty} {σs ps : List Ty} (h : SubJs (σ :: σs) ps) :
    ∃ τp psrest, ps = τp :: psrest ∧ SubJ σ τp ∧ SubJs σs psrest := by
  cases h with
  | cons h1 h2 => exact ⟨_, _, rfl, h1, h2⟩

/-- Union- and arrow-free — the types on which the widened value judgment and the
    old spine's `ValueTy` coincide (J19), and the groundness the certificate's row
    parameters must satisfy (J22/J24). `arrayOf` counts as ground: `subTy` compares
    it by equality, so nothing decomposes through its element. -/
def groundTy : Ty → Bool
  | .union _ _ => false
  | .arrow0 _ => false
  | .arrowCons _ _ => false
  | .nilable s => groundTy s
  | _ => true

/-! ## The algorithmic form, on fuel

`Deriv.check` (J2) needs a `Bool` that kernel-reduces (norm 5), so the recursion is
on fuel — the L73 discipline; a well-founded pair recursion would not reduce under
`decide`. Sound against `SubJ`; completeness is deliberately not a theorem (the
derivation checker only ever needs the sound direction), but each rule of `SubJ` has
a disjunct here, so a size-summed fuel is enough in practice. -/

def subJb : Nat → Ty → Ty → Bool
  | 0, _, _ => false
  | n + 1, σ, τ =>
    subTy σ τ ||
    (match σ with
     | .union a b => subJb n a τ && subJb n b τ
     | .nilable s => subJb n .nilT τ && subJb n s τ
     | _ => false) ||
    (match σ, τ with
     | .arrow0 r, .arrow0 t => subJb n r t
     | .arrowCons p r, .arrowCons q t => subJb n q p && subJb n r t
     | _, _ => false) ||
    (match τ with
     | .union a b => subJb n σ a || subJb n σ b
     | .nilable t => subJb n σ t
     | _ => false)

theorem subJb_sound : ∀ {n : Nat} {σ τ : Ty}, subJb n σ τ = true → SubJ σ τ := by
  intro n
  induction n with
  | zero => intro σ τ h; exact absurd h (by simp [subJb])
  | succ n ih =>
    intro σ τ h
    simp only [subJb, Bool.or_eq_true] at h
    rcases h with ((hb | hl) | ha) | hr
    · exact .base hb
    · cases σ <;> simp only [Bool.and_eq_true] at hl
      case union a b => exact .unionL (ih hl.1) (ih hl.2)
      case nilable s => exact .nilableL (ih hl.1) (ih hl.2)
      all_goals exact absurd hl (by simp)
    · cases σ <;> cases τ <;> simp only [Bool.and_eq_true] at ha
      case arrow0.arrow0 r t => exact .arrow0 (ih ha)
      case arrowCons.arrowCons p r q t => exact .arrowCons (ih ha.1) (ih ha.2)
      all_goals exact absurd ha (by simp)
    · cases τ <;> simp only [Bool.or_eq_true] at hr
      case union a b =>
        rcases hr with hr | hr
        · exact .unionR1 (ih hr)
        · exact .unionR2 (ih hr)
      case nilable t => exact .nilableR (ih hr)
      all_goals exact absurd hr (by simp)

/-- Pointwise `subJb`, arity-forcing — `SubJs`' algorithmic form. -/
def subJsb (n : Nat) : List Ty → List Ty → Bool
  | [], [] => true
  | σ :: σs, τ :: τs => subJb n σ τ && subJsb n σs τs
  | _, _ => false

theorem subJsb_sound : ∀ {σs τs : List Ty} {n : Nat}, subJsb n σs τs = true → SubJs σs τs
  | [], [], _, _ => .nil
  | _ :: _, _ :: _, n, h => by
    simp only [subJsb, Bool.and_eq_true] at h
    exact .cons (subJb_sound h.1) (subJsb_sound h.2)
  | [], _ :: _, _, h => by simp [subJsb] at h
  | _ :: _, [], _, h => by simp [subJsb] at h

/-! ## The arrow spine, assembled and read back -/

/-- `(A, B) → R` from its parts: `arrowOf [A, B] R = arrowCons A (arrowCons B
    (arrow0 R))`. The rules construct arrows only through this, so every arrow a
    derivation mentions is a well-formed spine. -/
def arrowOf : List Ty → Ty → Ty
  | [], r => .arrow0 r
  | p :: ps, r => .arrowCons p (arrowOf ps r)

/-- The parts back, or `none` off the well-formed spine — the `call` rule's reader. -/
def arrowParts? : Ty → Option (List Ty × Ty)
  | .arrow0 r => some ([], r)
  | .arrowCons p rest =>
    match arrowParts? rest with
    | some (ps, r) => some (p :: ps, r)
    | none => none
  | _ => none

@[simp] theorem arrowParts?_arrowOf (ps : List Ty) (r : Ty) :
    arrowParts? (arrowOf ps r) = some (ps, r) := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [arrowOf, arrowParts?, ih]

/-! ## The widening constructor -/

/-- The union, with the degenerate cases collapsed: equal sides answer the side, a
    `nilT` side normalizes to `.nilable` (one spelling of "or nil", so `dropNil`
    and the `subTy` nilable clause both keep working on joined optionals). This is
    emission guidance for derivations — the rules never require it, since `SubJ`
    relates the raw and collapsed forms anyway. -/
def mkUnion (σ τ : Ty) : Ty :=
  if σ == τ then σ
  else if σ == .nilT then mkNilable τ
  else if τ == .nilT then mkNilable σ
  else .union σ τ

/-- Both sides are below `mkUnion` — what makes it always eligible as a join's
    chosen bound. -/
theorem mkUnion_sub (σ τ : Ty) : SubJ σ (mkUnion σ τ) ∧ SubJ τ (mkUnion σ τ) := by
  unfold mkUnion
  by_cases h1 : σ == τ
  · simp only [h1, if_true]
    exact ⟨SubJ.refl σ, by rw [show τ = σ from (beq_iff_eq.mp h1).symm]; exact SubJ.refl σ⟩
  · simp only [h1, Bool.false_eq_true, if_false]
    by_cases h2 : σ == .nilT
    · simp only [h2, if_true]
      exact ⟨by rw [beq_iff_eq.mp h2]; exact .base (subTy_nilT_mkNilable τ),
             .base (subTy_mkNilable τ)⟩
    · simp only [h2, Bool.false_eq_true, if_false]
      by_cases h3 : τ == .nilT
      · simp only [h3, if_true]
        exact ⟨.base (subTy_mkNilable σ),
               by rw [beq_iff_eq.mp h3]; exact .base (subTy_nilT_mkNilable σ)⟩
      · simp only [h3, Bool.false_eq_true, if_false]
        exact ⟨.unionR1 (SubJ.refl σ), .unionR2 (SubJ.refl τ)⟩

/-! ## Narrowing operators

Truthiness is the one condition the machine tests **without a dispatch** — `if`
consults the value directly, so it cannot be forged the way a user-redefined
`nil?` can (a `def nil?; true; end` on any class makes `x.nil?`-based narrowing
lie, and the current invariant carries nothing that forbids the shadowing — the
reason there are no `nil?`-condition rules yet; see `implementation-notes.md`
J15). -/

/-- Remove the nil half of a type — what a **truthy** occurrence is known to
    inhabit. At `nilT` itself there is no bottom type to answer, so the no-op is
    the sound choice (the branch is unreachable; any claim about it is vacuous at
    runtime, and `nilT` is the weakest we can state). Sound for every `τ`
    including `.bool`: a truthy value is not nil, and dropping only nil keeps
    `false : bool` inhabiting the result. -/
def dropNil : Ty → Ty
  | .nilT => .nilT
  | .nilable σ => σ
  | .union a b =>
    if a == .nilT then dropNil b
    else if b == .nilT then dropNil a
    else .union (dropNil a) (dropNil b)
  | τ => τ

/-- No member of the type is `false`-inhabited (or unbounded): the side condition
    for narrowing the **falsy** branch to `nilT`. Conservative — `.bool` and
    `.any` fail it, everything ground succeeds, unions and nilables recurse.
    (`.cls "FalseClass"` cannot arise: `valueTy?` types `false` as `.bool`.) -/
def boolFree : Ty → Bool
  | .bool => false
  | .any => false
  | .nilable σ => boolFree σ
  | .union a b => boolFree a && boolFree b
  | _ => true

/-- The falsy-branch environment type: `nilT` when falsy can only mean nil
    (`boolFree`), unchanged otherwise. -/
def elseNarrow (τ : Ty) : Ty :=
  if boolFree τ then .nilT else τ

end RubyCore.Judgment
