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

theorem SubJ.refl (τ : Ty) : SubJ τ τ := .base (subTy_refl τ)

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
