import RubyCore.Proof.Static.Assn
import RubyCore.Types.OpenSelf

/-!
# R4's soundness — open-self typing factors through nominal typing

`homebrew/assertion-language.md` §4.3, §7.2, §7.5, §12 R4.

Two theorems, and the second is the rung:

1. **`inferOpen_mono`** — §7.5's owed lemma, *"`infer` is monotone in `Σ`"*, in
   the store's shape: the constraint store only ever **grows**, because
   requirements are positive facts. This is the row-level analogue of L161
   (`SubDecls F F' → defFree e → infer F … = infer F' …`), and it plays the same
   role: it is what lets a fact recorded early in a body be read at the store the
   body ends at.

2. **`inferOpen_factors`** — the factoring theorem:

   ```
   inferOpen D Γ e ctx s = .ok τ Γ' s'     (the open run succeeded)
   SatStore D θ stF                        (θ satisfies the residual store)
   θ ctx.self = .cls ctx.cls               (self is an instance of the definee)
   ⟹  infer D (substEnv θ Γ) e false ⟨ctx.cls, some ctx.cls⟩
          = some (τ.subst θ, substEnv θ Γ', D)
   ```

   *Every program open-self typing accepts, nominal typing accepts too, at the
   substituted type.* So R4 is **sound by reduction**, and adds no `KontOk`
   constructor and no consecution case: `HANDOFF.md`'s constraint 4 does not fire,
   because `infer` is untouched.

## Why that is the right statement, and not a weaker one

`SatStore` is what §8.2's discharge *checks*, restated as a proposition. So the
chain a checker actually runs is:

```
inferOpen  ⟶  residual store  ⟶  satStoreB D θ st = true  ⟶  SatStore   (§6)
           ⟶  inferOpen_factors ⟶  infer accepts this BODY
```

**And the chain stops there, which must be said out loud.** `check` does not call
`inferOpen`, so there is no theorem of the form *"open-self accepts `p` ⇒ `p` does not
type-stick"*, and there cannot be one until `check` routes through this function. What the
factoring theorem buys is composable one level down — `userConforms_of_inferBody` (§7) feeds
`Inv`'s user-method arm — but nothing here constructs a program-level `Inv`. So `--assn`'s
`accept` means **"types under this precondition"**, never **"is safe"**, and R4 as landed
**accepts no new programs**: `--check` is byte-identical across it. The value is that
`inferOpen` cannot accept a body nominal `infer` would reject, which is what makes it safe to
build on rather than a second opinion nobody can trust.

Every arrow but the first is proved here or already; the first is untrusted, which
is §8.4's stance and the whole point of putting the inference engine outside the
trusted base. `satStoreB_sound` (§6) is the arrow that joins the decidable check to
the proposition.
-/

namespace RubyCore
namespace Proof
namespace Static

open RubyCore.Types

set_option maxRecDepth 100000

/-! ## 1. The two relations on stores -/

/-- **The store grows.** One requirement recorded stays recorded, at the same
    signature — §7.5's *"`Σ₁ ⊎ Σ₂` is a union, not a merge with a side condition,
    and the reason is that the store only ever grows"*. -/
structure StoreLe (st st' : Store) : Prop where
  get : ∀ α n σ, (st.rowOf α).get? n = some σ → (st'.rowOf α).get? n = some σ

theorem StoreLe.refl (st : Store) : StoreLe st st := ⟨fun _ _ _ h => h⟩

theorem StoreLe.trans {a b c : Store} (h₁ : StoreLe a b) (h₂ : StoreLe b c) :
    StoreLe a c := ⟨fun α n σ h => h₂.get α n σ (h₁.get α n σ h)⟩

/-- **A substitution satisfies a store**: every requirement it records is met by
    the table at the substituted receiver type. This is exactly what
    `dischargeRow`/`dischargeNom` decide over one class; `satStoreB` (§6) decides it
    over a whole store, and `satStoreB_sound` is the bridge. -/
def SatStore (D : Decls) (θ : TyVar → Ty) (st : Store) : Prop :=
  ∀ α n σ, (st.rowOf α).get? n = some σ →
    sigOf D (θ α) n = some (σ.params.map (ATy.subst θ), σ.ret.subst θ)

theorem SatStore.mono {D : Decls} {θ : TyVar → Ty} {st st' : Store}
    (hle : StoreLe st st') (hs : SatStore D θ st') : SatStore D θ st :=
  fun α n σ h => hs α n σ (hle.get α n σ h)

/-! ## 2. Rows and the store, mechanically -/

theorem Row.get?_insert {R R' : Row} {n : String} {σ : ASig}
    (h : R.insert n σ = some R') :
    ∀ m τ, R.get? m = some τ → R'.get? m = some τ := by
  intro m τ hm
  unfold Row.insert at h
  cases hn : R.get? n with
  | some τ₀ =>
    rw [hn] at h
    dsimp only at h
    by_cases he : σ == τ₀
    · rw [if_pos he] at h; cases h; exact hm
    · rw [if_neg he] at h; exact absurd h (by simp)
  | none =>
    rw [hn] at h
    dsimp only at h
    cases h
    -- The new entry is prepended, so it can only shadow `n`, and `n` was absent.
    have hne : ¬ (n = m) := by
      intro hEq; subst hEq; rw [hn] at hm; exact absurd hm (by simp)
    unfold Row.get? at hm ⊢
    simp only [List.find?_cons]
    have : ((n, σ).1 == m) = false := by simpa using hne
    simp only [this]
    exact hm

theorem Store.rowOf_setRow_self (st : Store) (α : TyVar) (R : Row) :
    (st.setRow α R).rowOf α = R := by
  unfold Store.setRow Store.rowOf
  simp

theorem Store.rowOf_setRow_other (st : Store) {α β : TyVar} (R : Row) (h : β ≠ α) :
    (st.setRow α R).rowOf β = st.rowOf β := by
  unfold Store.setRow Store.rowOf
  simp only [List.find?_cons]
  have : ((α, R).1 == β) = false := by simpa using (Ne.symm h)
  simp [this]

/-- `requireRow` only grows the store — the atomic case of §7.5. -/
theorem requireRow_mono {st st' : Store} {α : TyVar} {n : String} {args : List ATy}
    {f : TyVar} {τ : ATy} (h : requireRow st α n args f = some (τ, st')) :
    StoreLe st st' := by
  unfold requireRow at h
  cases hg : (st.rowOf α).get? n with
  | some σ =>
    rw [hg] at h
    dsimp only at h
    by_cases hp : σ.params == args
    · rw [if_pos hp] at h; cases h; exact StoreLe.refl _
    · rw [if_neg hp] at h; exact absurd h (by simp)
  | none =>
    rw [hg] at h
    dsimp only at h
    cases hi : (st.rowOf α).insert n { params := args, ret := .var f } with
    | none => rw [hi] at h; simp at h
    | some R' =>
      rw [hi] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      refine ⟨fun β m σ' hm => ?_⟩
      by_cases hb : β = α
      · subst hb
        rw [Store.rowOf_setRow_self]
        exact Row.get?_insert hi m σ' hm
      · rw [Store.rowOf_setRow_other _ _ hb]; exact hm

/-- **`requireRow` records what the table must then supply.** The atomic case of
    the factoring theorem: if the requirement survives to a store `θ` satisfies,
    the *nominal* signature read is exactly the substituted one. -/
theorem requireRow_sat {D : Decls} {θ : TyVar → Ty} {st st' stF : Store} {α : TyVar}
    {n : String} {args : List ATy} {f : TyVar} {τ : ATy}
    (h : requireRow st α n args f = some (τ, st'))
    (hle : StoreLe st' stF) (hsat : SatStore D θ stF) :
    sigOf D (θ α) n = some (args.map (ATy.subst θ), τ.subst θ) := by
  unfold requireRow at h
  cases hg : (st.rowOf α).get? n with
  | some σ =>
    rw [hg] at h
    dsimp only at h
    by_cases hp : σ.params == args
    · rw [if_pos hp] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have := hsat α n σ (hle.get α n σ hg)
      rw [this]
      have : σ.params = args := by simpa using hp
      rw [this]
    · rw [if_neg hp] at h; exact absurd h (by simp)
  | none =>
    rw [hg] at h
    dsimp only at h
    cases hi : (st.rowOf α).insert n { params := args, ret := .var f } with
    | none => rw [hi] at h; simp at h
    | some R' =>
      rw [hi] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      -- The entry just inserted is in `R'`, hence in `stF`.
      have hin : R'.get? n = some { params := args, ret := ATy.var f } := by
        unfold Row.insert at hi
        rw [hg] at hi
        dsimp only at hi
        cases hi
        unfold Row.get?
        simp
      have hstF : (stF.rowOf α).get? n = some { params := args, ret := ATy.var f } := by
        refine hle.get α n _ ?_
        rw [Store.rowOf_setRow_self]
        exact hin
      exact hsat α n _ hstF

/-! ## 3. Environments under a substitution -/

def substEnv (θ : TyVar → Ty) (Γ : AEnv) : Env := Γ.map (fun e => (e.1, e.2.subst θ))

theorem aenvGet_subst {θ : TyVar → Ty} {Γ : AEnv} {x : String} {aτ : ATy}
    (h : aenvGet? Γ x = some aτ) : envGet? (substEnv θ Γ) x = some (aτ.subst θ) := by
  unfold aenvGet? at h
  unfold envGet? substEnv
  induction Γ with
  | nil => simp at h
  | cons e rest ih =>
    simp only [List.find?_cons, List.map_cons] at h ⊢
    by_cases hx : (e.1 == x)
    · simp only [hx, if_true] at h ⊢
      simp only [Option.map_some, Option.some.injEq] at h
      subst h; rfl
    · simp only [hx, Bool.false_eq_true, if_false] at h ⊢
      exact ih h

theorem substEnv_aenvSet {θ : TyVar → Ty} (Γ : AEnv) (x : String) (aτ : ATy) :
    substEnv θ (aenvSet Γ x aτ) = envSet (substEnv θ Γ) x (aτ.subst θ) := by
  induction Γ with
  | nil => rfl
  | cons e rest ih =>
    obtain ⟨y, σ⟩ := e
    unfold aenvSet envSet substEnv
    by_cases hy : (y == x)
    · simp [hy]
    · simp only [hy, Bool.false_eq_true, if_false, List.map_cons]
      unfold substEnv at ih
      rw [ih]

/-! ## 4. §7.5 — the store is monotone

The one lemma R4 owes the metatheory: *the constraint store only ever grows*,
because requirements are positive facts. §7.5 states it as the reason `Σ₁ ⊎ Σ₂`
can be a plain union with no side condition, and names L161 as the shape to prove
it in — a monotonicity result over `infer`'s whole case analysis.

Proved by the functional induction the mutual definition generates, so the case
split is exactly `inferOpen`'s own and no case can be forgotten: adding an arm to
`inferOpen` re-opens this proof, which is `HANDOFF.md` constraint 4's discipline
applied inside the untrusted layer. -/
theorem inferOpen_mono (D : Decls) (ctx : OCtx) (Γ : AEnv) (e : Expr) (s : OState) :
    ∀ τ Γ' s', inferOpen D Γ e ctx s = .ok τ Γ' s' → StoreLe s.st s'.st := by
  induction Γ, e, s using inferOpen.induct (D := D) (ctx := ctx)
    (motive2 := fun Γ t els s => ∀ τ Γ' s',
        inferOpenIf D Γ t els ctx s = .ok τ Γ' s' → StoreLe s.st s'.st)
    (motive3 := fun Γ es s => ∀ τ Γ' s',
        inferOpenSeq D Γ es ctx s = .ok τ Γ' s' → StoreLe s.st s'.st)
    -- **L175's argument traversal.** Same statement at the fourth motive; the send
    -- arms' chain is now `inferOpen recv → inferOpenArgs → requireRow`, so the
    -- transitivity alternatives below gained one link.
    (motive4 := fun Γ es s => ∀ τs Γ' s',
        inferOpenArgs D Γ es ctx s = .ok τs Γ' s' → StoreLe s.st s'.st) with
  | _ =>
    intros
    simp_all [inferOpen, inferOpenSeq, inferOpenIf, inferOpenArgs]
    try (rename_i hh; obtain ⟨-, -, rfl⟩ := hh)
    first
      | done
      | exact StoreLe.refl _
      | exact requireRow_mono (by assumption)
      | exact StoreLe.trans (by assumption) (by assumption)
      | exact StoreLe.trans (by assumption) (requireRow_mono (by assumption))
      | exact StoreLe.trans (StoreLe.trans (by assumption) (by assumption))
          (requireRow_mono (by assumption))
      | (rename_i ha; split at ha <;> simp_all)
      -- L201: the `return` arms record in `rets` and leave the store where it was, so
      -- the bound is the sub-expression's own (or reflexivity for a bare `return`).
      | (exact StoreLe.refl _)
      | (rename_i ha; exact ha)

/-- **And `rets` is monotone too** (L201), for the store's reason: a recorded return
    type is a positive fact, so the list only grows. Subset rather than sublist because
    that is all the consumer needs — `Factors`' premise is about *membership* in the
    final state's list, and the composition at every compound arm is exactly this
    lemma, the way `StoreLe` is for the store.

    Same induction, same uniform block, and the same discipline: adding an arm to
    `inferOpen` re-opens both proofs. -/
theorem inferOpen_rets (D : Decls) (ctx : OCtx) (Γ : AEnv) (e : Expr) (s : OState) :
    ∀ τ Γ' s', inferOpen D Γ e ctx s = .ok τ Γ' s' → ∀ x ∈ s.rets, x ∈ s'.rets := by
  induction Γ, e, s using inferOpen.induct (D := D) (ctx := ctx)
    (motive2 := fun Γ t els s => ∀ τ Γ' s',
        inferOpenIf D Γ t els ctx s = .ok τ Γ' s' → ∀ x ∈ s.rets, x ∈ s'.rets)
    (motive3 := fun Γ es s => ∀ τ Γ' s',
        inferOpenSeq D Γ es ctx s = .ok τ Γ' s' → ∀ x ∈ s.rets, x ∈ s'.rets)
    (motive4 := fun Γ es s => ∀ τs Γ' s',
        inferOpenArgs D Γ es ctx s = .ok τs Γ' s' → ∀ x ∈ s.rets, x ∈ s'.rets) with
  | _ =>
    intros
    simp_all [inferOpen, inferOpenSeq, inferOpenIf, inferOpenArgs]
    try (rename_i hh; obtain ⟨-, -, rfl⟩ := hh)
    first
      | done
      | assumption
      | (exact List.mem_cons_of_mem _ (by assumption))
      | (exact (by assumption : ∀ x ∈ _, x ∈ _) _ (by assumption))
      | (rename_i hx ha; exact ha _ hx)
      | (rename_i hx hb ha; exact hb _ (ha _ hx))
      | (rename_i hx hc hb ha; exact hc _ (hb _ (ha _ hx)))
      | (rename_i hx ha; exact List.mem_cons_of_mem _ (ha _ hx))
      | (rename_i hx ha hb; exact hb _ (ha _ hx))
      | (rename_i hy hx ha; split at ha <;> simp_all)
      -- the `requireRow` arms: the state is rebuilt with `rets` carried, so the
      -- membership is the hypothesis after one `obtain`.
      | (rename_i hx hq; obtain ⟨-, -, rfl⟩ := hq; exact hx)
      | (rename_i hq hx; obtain ⟨-, -, rfl⟩ := hq; exact hx)
      -- **The arms whose answer `simp_all` left as an unsplit equation** (L201),
      -- with the membership hypothesis *after* it — so the `obtain` has to name
      -- two, and the composition is then read off by unification.
      | (rename_i hh hmem
         obtain ⟨-, -, rfl⟩ := hh
         dsimp only
         first
           | exact hmem
           | exact List.mem_cons_of_mem _ hmem
           | exact (by assumption : ∀ x, x ∈ _ → x ∈ _) _ hmem
           | exact List.mem_cons_of_mem _ ((by assumption : ∀ x, x ∈ _ → x ∈ _) _ hmem)
           | (rename_i ih1 ih2; exact ih1 _ (ih2 _ hmem))
           | (rename_i ih2 ih1; exact ih1 _ (ih2 _ hmem)))

/-- The `if`-join's monotonicity, from the main lemma: `inferOpenIf` is not
    recursive, it only calls `inferOpen`. -/
theorem inferOpenIf_mono (D : Decls) (ctx : OCtx) (Γ : AEnv) (t : Expr)
    (els : Option Expr) (s : OState) :
    ∀ τ Γ' s', inferOpenIf D Γ t els ctx s = .ok τ Γ' s' → StoreLe s.st s'.st := by
  intro τ Γ' s' h
  unfold inferOpenIf at h
  cases els with
  | some e =>
    dsimp only at h
    cases ht : inferOpen D Γ t ctx s with
    | ok τt Γt st =>
      rw [ht] at h
      dsimp only at h
      cases he : inferOpen D Γ e ctx st with
      | ok τe Γe se =>
        rw [he] at h
        dsimp only at h
        split at h
        · -- L193b adds the join's own split; both accepting arms leave `se` alone,
          -- so the store bound is the same composition it was.
          split at h
          · simp only [OResult.ok.injEq] at h
            obtain ⟨-, -, rfl⟩ := h
            exact StoreLe.trans (inferOpen_mono D ctx Γ t s τt Γt st ht)
              (inferOpen_mono D ctx Γ e st τe Γe se he)
          · simp at h
        · simp at h
      | missing _ _ _ => rw [he] at h; simp at h
      | outOfFragment _ => rw [he] at h; simp at h
    | missing _ _ _ => rw [ht] at h; simp at h
    | outOfFragment _ => rw [ht] at h; simp at h
  | none =>
    dsimp only at h
    cases ht : inferOpen D Γ t ctx s with
    | ok τt Γt st =>
      rw [ht] at h
      dsimp only at h
      split at h
      · split at h
        · simp only [OResult.ok.injEq] at h
          obtain ⟨-, -, rfl⟩ := h
          exact inferOpen_mono D ctx Γ t s τt Γt st ht
        · simp at h
      · simp at h
    | missing _ _ _ => rw [ht] at h; simp at h
    | outOfFragment _ => rw [ht] at h; simp at h

/-- The statement sequence's, by induction on the list. -/
theorem inferOpenSeq_mono (D : Decls) (ctx : OCtx) :
    ∀ (es : List Expr) (Γ : AEnv) (s : OState) τ Γ' s',
      inferOpenSeq D Γ es ctx s = .ok τ Γ' s' → StoreLe s.st s'.st := by
  intro es
  induction es with
  | nil => intro Γ s τ Γ' s' h; unfold inferOpenSeq at h; cases h; exact StoreLe.refl _
  | cons e rest ih =>
    intro Γ s τ Γ' s' h
    unfold inferOpenSeq at h
    cases rest with
    | nil => exact inferOpen_mono D ctx Γ e s τ Γ' s' h
    | cons e2 rest2 =>
      dsimp only at h
      cases he : inferOpen D Γ e ctx s with
      | ok τ₁ Γ₁ s₁ =>
        rw [he] at h
        dsimp only at h
        exact StoreLe.trans (inferOpen_mono D ctx Γ e s τ₁ Γ₁ s₁ he)
          (ih Γ₁ s₁ τ Γ' s' h)
      | missing _ _ _ => rw [he] at h; simp at h
      | outOfFragment _ => rw [he] at h; simp at h

/-! ### Pushing a bound down to a subexpression

The shape every case of the factoring theorem needs, stated so that the tactic
can find it by unification alone: whatever store bounds the *node*'s output also
bounds its subexpressions', because the store only grows. -/

theorem storeLe_sub {D : Decls} {ctx : OCtx} {Γ : AEnv} {e : Expr} {s s' : OState}
    {τ : ATy} {Γ' : AEnv} {stF : Store}
    (h : inferOpen D Γ e ctx s = .ok τ Γ' s') (hle : StoreLe s'.st stF) :
    StoreLe s.st stF :=
  StoreLe.trans (inferOpen_mono D ctx Γ e s τ Γ' s' h) hle

theorem storeLe_subReq {st st' stF : Store} {α : TyVar} {n : String} {args : List ATy}
    {f : TyVar} {τ : ATy} (h : requireRow st α n args f = some (τ, st'))
    (hle : StoreLe st' stF) : StoreLe st stF :=
  StoreLe.trans (requireRow_mono h) hle

theorem storeLe_subIf {D : Decls} {ctx : OCtx} {Γ : AEnv} {t : Expr}
    {els : Option Expr} {s s' : OState} {τ : ATy} {Γ' : AEnv} {stF : Store}
    (h : inferOpenIf D Γ t els ctx s = .ok τ Γ' s') (hle : StoreLe s'.st stF) :
    StoreLe s.st stF :=
  StoreLe.trans (inferOpenIf_mono D ctx Γ t els s τ Γ' s' h) hle

theorem storeLe_subSeq {D : Decls} {ctx : OCtx} {Γ : AEnv} {es : List Expr}
    {s s' : OState} {τ : ATy} {Γ' : AEnv} {stF : Store}
    (h : inferOpenSeq D Γ es ctx s = .ok τ Γ' s') (hle : StoreLe s'.st stF) :
    StoreLe s.st stF :=
  StoreLe.trans (inferOpenSeq_mono D ctx es Γ s τ Γ' s' h) hle

/-- The argument list's monotonicity (L175), by list induction on top of
    `inferOpen_mono` — `inferOpenSeq_mono`'s twin, and needed for the same reason:
    a send's store bound has to reach its arguments. -/
theorem inferOpenArgs_mono (D : Decls) (ctx : OCtx) :
    ∀ (es : List Expr) (Γ : AEnv) (s : OState) τs Γ' s',
      inferOpenArgs D Γ es ctx s = .ok τs Γ' s' → StoreLe s.st s'.st := by
  intro es
  induction es with
  | nil => intro Γ s τs Γ' s' h; unfold inferOpenArgs at h; cases h; exact StoreLe.refl _
  | cons e rest ih =>
    intro Γ s τs Γ' s' h
    unfold inferOpenArgs at h
    cases he : inferOpen D Γ e ctx s with
    | ok τ₁ Γ₁ s₁ =>
      rw [he] at h
      dsimp only at h
      cases hr : inferOpenArgs D Γ₁ rest ctx s₁ with
      | ok τs₂ Γ₂ s₂ =>
        rw [hr] at h
        simp only [OArgs.ok.injEq] at h
        obtain ⟨-, -, rfl⟩ := h
        exact StoreLe.trans (inferOpen_mono D ctx Γ e s τ₁ Γ₁ s₁ he)
          (ih Γ₁ s₁ τs₂ Γ₂ s₂ hr)
      | missing _ _ _ => rw [hr] at h; simp at h
      | outOfFragment _ => rw [hr] at h; simp at h
    | missing _ _ _ => rw [he] at h; simp at h
    | outOfFragment _ => rw [he] at h; simp at h

theorem storeLe_subArgs {D : Decls} {ctx : OCtx} {Γ : AEnv} {es : List Expr}
    {s s' : OState} {τs : List ATy} {Γ' : AEnv} {stF : Store}
    (h : inferOpenArgs D Γ es ctx s = .ok τs Γ' s') (hle : StoreLe s'.st stF) :
    StoreLe s.st stF :=
  StoreLe.trans (inferOpenArgs_mono D ctx es Γ s τs Γ' s' h) hle

/-- The `if`-join's `rets` monotonicity — `inferOpenIf_mono`'s twin (L201). -/
theorem inferOpenIf_rets (D : Decls) (ctx : OCtx) (Γ : AEnv) (t : Expr)
    (els : Option Expr) (s : OState) :
    ∀ τ Γ' s', inferOpenIf D Γ t els ctx s = .ok τ Γ' s' → ∀ x ∈ s.rets, x ∈ s'.rets := by
  intro τ Γ' s' h
  unfold inferOpenIf at h
  cases els with
  | some e =>
    dsimp only at h
    cases ht : inferOpen D Γ t ctx s with
    | ok τt Γt st =>
      rw [ht] at h
      dsimp only at h
      cases he : inferOpen D Γ e ctx st with
      | ok τe Γe se =>
        rw [he] at h
        dsimp only at h
        split at h
        · split at h
          · simp only [OResult.ok.injEq] at h
            obtain ⟨-, -, rfl⟩ := h
            exact fun x hx => inferOpen_rets D ctx Γ e st τe Γe se he x
              (inferOpen_rets D ctx Γ t s τt Γt st ht x hx)
          · simp at h
        · simp at h
      | missing _ _ _ => rw [he] at h; simp at h
      | outOfFragment _ => rw [he] at h; simp at h
    | missing _ _ _ => rw [ht] at h; simp at h
    | outOfFragment _ => rw [ht] at h; simp at h
  | none =>
    dsimp only at h
    cases ht : inferOpen D Γ t ctx s with
    | ok τt Γt st =>
      rw [ht] at h
      dsimp only at h
      split at h
      · split at h
        · simp only [OResult.ok.injEq] at h
          obtain ⟨-, -, rfl⟩ := h
          exact inferOpen_rets D ctx Γ t s τt Γt st ht
        · simp at h
      · simp at h
    | missing _ _ _ => rw [ht] at h; simp at h
    | outOfFragment _ => rw [ht] at h; simp at h

/-- The sequence's (L201). -/
theorem inferOpenSeq_rets (D : Decls) (ctx : OCtx) :
    ∀ (es : List Expr) (Γ : AEnv) (s : OState) τ Γ' s',
      inferOpenSeq D Γ es ctx s = .ok τ Γ' s' → ∀ x ∈ s.rets, x ∈ s'.rets := by
  intro es
  induction es with
  | nil => intro Γ s τ Γ' s' h; unfold inferOpenSeq at h; cases h; exact fun x hx => hx
  | cons e rest ih =>
    intro Γ s τ Γ' s' h
    unfold inferOpenSeq at h
    cases rest with
    | nil => exact inferOpen_rets D ctx Γ e s τ Γ' s' h
    | cons e2 rest2 =>
      dsimp only at h
      cases he : inferOpen D Γ e ctx s with
      | ok τ₁ Γ₁ s₁ =>
        rw [he] at h
        dsimp only at h
        exact fun x hx => ih Γ₁ s₁ τ Γ' s' h x (inferOpen_rets D ctx Γ e s τ₁ Γ₁ s₁ he x hx)
      | missing _ _ _ => rw [he] at h; simp at h
      | outOfFragment _ => rw [he] at h; simp at h

/-- And the argument list's (L201). -/
theorem inferOpenArgs_rets (D : Decls) (ctx : OCtx) :
    ∀ (es : List Expr) (Γ : AEnv) (s : OState) τs Γ' s',
      inferOpenArgs D Γ es ctx s = .ok τs Γ' s' → ∀ x ∈ s.rets, x ∈ s'.rets := by
  intro es
  induction es with
  | nil => intro Γ s τs Γ' s' h; unfold inferOpenArgs at h; cases h; exact fun x hx => hx
  | cons e rest ih =>
    intro Γ s τs Γ' s' h
    unfold inferOpenArgs at h
    cases he : inferOpen D Γ e ctx s with
    | ok τ₁ Γ₁ s₁ =>
      rw [he] at h
      dsimp only at h
      cases hr : inferOpenArgs D Γ₁ rest ctx s₁ with
      | ok τs₂ Γ₂ s₂ =>
        rw [hr] at h
        simp only [OArgs.ok.injEq] at h
        obtain ⟨-, -, rfl⟩ := h
        exact fun x hx => ih Γ₁ s₁ τs₂ Γ₂ s₂ hr x (inferOpen_rets D ctx Γ e s τ₁ Γ₁ s₁ he x hx)
      | missing _ _ _ => rw [hr] at h; simp at h
      | outOfFragment _ => rw [hr] at h; simp at h
    | missing _ _ _ => rw [he] at h; simp at h
    | outOfFragment _ => rw [he] at h; simp at h

/-! ### Pushing the *return* bound down to a subexpression (L201)

`storeLe_sub`'s twin, for the second premise the factoring theorem now carries:
whatever bounds the *node*'s collected `return` types also bounds its
subexpressions', because `rets` only grows too. -/

theorem rets_sub {D : Decls} {ctx : OCtx} {Γ : AEnv} {e : Expr} {s s' : OState}
    {τ : ATy} {Γ' : AEnv} {θ : TyVar → Ty} {retF : Ty}
    (h : inferOpen D Γ e ctx s = .ok τ Γ' s')
    (hr : ∀ a ∈ s'.rets, subTy (ATy.subst θ a) retF = true) :
    ∀ a ∈ s.rets, subTy (ATy.subst θ a) retF = true :=
  fun a ha => hr a (inferOpen_rets D ctx Γ e s τ Γ' s' h a ha)

theorem rets_subIf {D : Decls} {ctx : OCtx} {Γ : AEnv} {t : Expr} {els : Option Expr}
    {s s' : OState} {τ : ATy} {Γ' : AEnv} {θ : TyVar → Ty} {retF : Ty}
    (h : inferOpenIf D Γ t els ctx s = .ok τ Γ' s')
    (hr : ∀ a ∈ s'.rets, subTy (ATy.subst θ a) retF = true) :
    ∀ a ∈ s.rets, subTy (ATy.subst θ a) retF = true :=
  fun a ha => hr a (inferOpenIf_rets D ctx Γ t els s τ Γ' s' h a ha)

theorem rets_subSeq {D : Decls} {ctx : OCtx} {Γ : AEnv} {es : List Expr}
    {s s' : OState} {τ : ATy} {Γ' : AEnv} {θ : TyVar → Ty} {retF : Ty}
    (h : inferOpenSeq D Γ es ctx s = .ok τ Γ' s')
    (hr : ∀ a ∈ s'.rets, subTy (ATy.subst θ a) retF = true) :
    ∀ a ∈ s.rets, subTy (ATy.subst θ a) retF = true :=
  fun a ha => hr a (inferOpenSeq_rets D ctx es Γ s τ Γ' s' h a ha)

theorem rets_subArgs {D : Decls} {ctx : OCtx} {Γ : AEnv} {es : List Expr}
    {s s' : OState} {τs : List ATy} {Γ' : AEnv} {θ : TyVar → Ty} {retF : Ty}
    (h : inferOpenArgs D Γ es ctx s = .ok τs Γ' s')
    (hr : ∀ a ∈ s'.rets, subTy (ATy.subst θ a) retF = true) :
    ∀ a ∈ s.rets, subTy (ATy.subst θ a) retF = true :=
  fun a ha => hr a (inferOpenArgs_rets D ctx es Γ s τs Γ' s' h a ha)

/-! ### Substitution, as simp lemmas

Stated rather than unfolded, so the induction's goals stay in terms of `substEnv`
and `ATy.subst` and the environment lemmas above can fire. -/

@[simp] theorem ATy.subst_nom (θ : TyVar → Ty) (τ : Ty) : (ATy.nom τ).subst θ = τ := rfl

@[simp] theorem ATy.subst_var (θ : TyVar → Ty) (α : TyVar) : (ATy.var α).subst θ = θ α := rfl

/-- The list form (L175): a send's *nominal* branch compares the open argument
    types against `ps.map ATy.nom`, so the substituted list is `ps` itself. Stated
    as a `simp` lemma because the composition is what the goal is left holding. -/
@[simp] theorem ATy.subst_nom_comp (θ : TyVar → Ty) :
    (ATy.subst θ ∘ ATy.nom) = id := by funext t; rfl

/-! ## 5. The factoring theorem — R4's soundness

*Open-self typing reduces to nominal typing.* Read the hypotheses as the checker's
own workflow: `inferOpen` ran and produced a residual store; a solver (untrusted,
§8.4) produced `θ`; the validator checked that `θ` satisfies the store and sends
`self` to the definee; and then **nominal `infer` accepts the same body at the
substituted type** — so `check`'s existing soundness applies verbatim and R4
costs no consecution case.

`Factors` states the conclusion as a predicate on the *result* rather than as
three universally-quantified components, which is what lets the functional
induction's cases reduce by `simp` alone: an arm that answers `.missing` or
`.outOfFragment` discharges its case definitionally, and there are twenty-odd of
those. -/
def Factors (D : Decls) (θ : TyVar → Ty) (stF : Store) (retF : Ty) (ctx : OCtx)
    (Γ : AEnv) (e : Expr) : OResult → Prop
  | .ok τ Γ' s' => StoreLe s'.st stF → (∀ a ∈ s'.rets, subTy (a.subst θ) retF = true) →
      infer D (substEnv θ Γ) e false
          { cls := ctx.cls, selfCls := some ctx.cls, ret := some retF }
        = some (τ.subst θ, substEnv θ Γ', D)
  | _ => True

/-- The `inferIf`/`inferSeq` forms, which differ only in which nominal function
    the conclusion names. -/
def FactorsIf (D : Decls) (θ : TyVar → Ty) (stF : Store) (retF : Ty) (ctx : OCtx)
    (Γ : AEnv) (t : Expr) (els : Option Expr) : OResult → Prop
  | .ok τ Γ' s' => StoreLe s'.st stF → (∀ a ∈ s'.rets, subTy (a.subst θ) retF = true) →
      inferIf D (substEnv θ Γ) t els false
          { cls := ctx.cls, selfCls := some ctx.cls, ret := some retF }
        = some (τ.subst θ, substEnv θ Γ', D)
  | _ => True

def FactorsSeq (D : Decls) (θ : TyVar → Ty) (stF : Store) (retF : Ty) (ctx : OCtx)
    (Γ : AEnv) (es : List Expr) : OResult → Prop
  | .ok τ Γ' s' => StoreLe s'.st stF → (∀ a ∈ s'.rets, subTy (a.subst θ) retF = true) →
      inferSeq D (substEnv θ Γ) es false
          { cls := ctx.cls, selfCls := some ctx.cls, ret := some retF }
        = some (τ.subst θ, substEnv θ Γ', D)
  | _ => True

/-- And the argument list's (L175). The only one whose conclusion is about a *list*
    of types, which is exactly why `inferArgs` is a separate traversal from
    `inferSeq`. -/
def FactorsArgs (D : Decls) (θ : TyVar → Ty) (stF : Store) (retF : Ty) (ctx : OCtx)
    (Γ : AEnv) (es : List Expr) : OArgs → Prop
  | .ok τs Γ' s' => StoreLe s'.st stF → (∀ a ∈ s'.rets, subTy (a.subst θ) retF = true) →
      inferArgs D (substEnv θ Γ) es false
          { cls := ctx.cls, selfCls := some ctx.cls, ret := some retF }
        = some (τs.map (ATy.subst θ), substEnv θ Γ', D)
  | _ => True

/-- **The `if` join's factoring step, packaged so `apply` can unify it** (L193b).
    `rw [joinATy_subst (by assumption)]` cannot work inside the uniform tactic block:
    `rw` elaborates its term before touching the goal, so `a`/`b`/`c` are still
    metavariables when `assumption` runs. Stating the whole equation lets `apply`
    fix them from the goal and leaves exactly the hypothesis to be found. -/
theorem mkNilable_join {a c : ATy} {θ : TyVar → Ty}
    (h : joinATy a (.nom .nilT) = some c) : mkNilable (a.subst θ) = c.subst θ := by
  have h1 := joinATy_subst (θ := θ) h
  rw [show (ATy.nom Ty.nilT).subst θ = Ty.nilT from rfl, joinTy_nilT_right] at h1
  simpa using h1

theorem inferOpen_factors (D : Decls) (ctx : OCtx) (θ : TyVar → Ty) (stF : Store)
    (retF : Ty) (hsat : SatStore D θ stF) (hself : θ ctx.self = .cls ctx.cls)
    (Γ : AEnv) (e : Expr) (s : OState) :
    Factors D θ stF retF ctx Γ e (inferOpen D Γ e ctx s) := by
  induction Γ, e, s using inferOpen.induct (D := D) (ctx := ctx)
    (motive2 := fun Γ t els s =>
      FactorsIf D θ stF retF ctx Γ t els (inferOpenIf D Γ t els ctx s))
    (motive3 := fun Γ es s => FactorsSeq D θ stF retF ctx Γ es (inferOpenSeq D Γ es ctx s))
    (motive4 := fun Γ es s =>
      FactorsArgs D θ stF retF ctx Γ es (inferOpenArgs D Γ es ctx s)) with
  | _ =>
    simp_all [inferOpen, inferOpenSeq, inferOpenIf, Factors, FactorsIf,
      FactorsSeq, FactorsArgs, infer, inferSeq, inferIf, inferArgs,
      substEnv_aenvSet, hself]
    all_goals (try intro hle)
    -- L201's second premise: the collected `return` types all agree with the
    -- body's, pushed down to the subexpressions by `rets_sub` below.
    all_goals (try intro hr)
    -- L193b: `joinATy_subst` is a *conditional* rewrite whose hypothesis is in the
    -- context, so `simp_all` can discharge it and close the join cases here. It has
    -- to be in this set rather than in the alternative block below, because
    -- `simp_all` is what leaves those goals in the first place.
    all_goals (try simp_all [joinATy_subst])
    all_goals (
      first
        | done
        -- **the `if` join** (L193b), both arms. The IHs are already applied by
        -- `simp_all`; what is left is that the *open* join and the *nominal* one agree
        -- under substitution, which is `joinATy_subst` and nothing else. Two variants
        -- because the one-armed `if` leaves the goal as a bare type equation.
        | (exact joinATy_subst (by assumption))
        | (rw [mkNilable_join (θ := θ) ‹joinATy _ _ = some _›]; done)
        -- a local read: the environment lemma, and nothing else
        | exact aenvGet_subst (by assumption)
        -- a `vcall`: the requirement on `self`, discharged at the definee's class
        | (rw [← hself, requireRow_sat (by assumption) (by assumption) hsat]; simp)
        -- a send on a variable receiver with nothing left to place
        | (rw [requireRow_sat (by assumption) (by assumption) hsat]; simp)
        -- one subexpression, nominal receiver
        | (rename_i ih1
           (first | rw [ih1 (storeLe_sub (by assumption) (by assumption)) (rets_sub (by assumption) (by assumption))] | rw [ih1 (storeLe_sub (by assumption) (by assumption))]); simp_all)
        -- two subexpressions, nominal receiver
        | (rename_i ih2 ih1
           (first | rw [ih2 (storeLe_sub (by assumption) (by assumption)) (rets_sub (by assumption) (by assumption))] | rw [ih2 (storeLe_sub (by assumption) (by assumption))]); simp_all)
        -- receiver, then the row requirement (zero-argument send on `var α`)
        | (rename_i ih1
           (first | rw [ih1 (storeLe_subReq (by assumption) (by assumption)) (by assumption)] | rw [ih1 (storeLe_subReq (by assumption) (by assumption))])
           dsimp only
           rw [requireRow_sat (by assumption) (by assumption) hsat]
           simp)
        -- **receiver, then the argument list** (L175), nominal receiver. Two
        -- variants, because `simp_all` may already have instantiated the argument
        -- list's IH with the bound it could find.
        | (rename_i ih2 ih1
           (first | rw [ih2 (storeLe_subArgs (by assumption) (by assumption)) (rets_subArgs (by assumption) (by assumption))] | rw [ih2 (storeLe_subArgs (by assumption) (by assumption))])
           dsimp only
           rw [ih1]
           simp_all)
        | (rename_i ih2 ih1
           (first | rw [ih2 (storeLe_subArgs (by assumption) (by assumption)) (rets_subArgs (by assumption) (by assumption))] | rw [ih2 (storeLe_subArgs (by assumption) (by assumption))])
           dsimp only
           (first | rw [ih1 (by assumption) (by assumption)] | rw [ih1 (by assumption)])
           simp_all)
        -- **receiver, argument list, then the row requirement** (L175), variable
        -- receiver.
        | (rename_i ih2 ih1
           (first | rw [ih2 (storeLe_subArgs (by assumption) (storeLe_subReq (by assumption) (by assumption))) (rets_subArgs (by assumption) (by assumption))] | rw [ih2 (storeLe_subArgs (by assumption) (storeLe_subReq (by assumption) (by assumption)))])
           dsimp only
           rw [ih1]
           dsimp only
           rw [requireRow_sat (by assumption) (by assumption) hsat]
           simp)
        | (rename_i ih2 ih1
           (first | rw [ih2 (storeLe_subArgs (by assumption) (storeLe_subReq (by assumption) (by assumption))) (rets_subArgs (by assumption) (by assumption))] | rw [ih2 (storeLe_subArgs (by assumption) (storeLe_subReq (by assumption) (by assumption)))])
           dsimp only
           (first | rw [ih1 (storeLe_subReq (by assumption) (by assumption)) (by assumption)] | rw [ih1 (storeLe_subReq (by assumption) (by assumption))])
           dsimp only
           rw [requireRow_sat (by assumption) (by assumption) hsat]
           simp)
        -- **the argument list, then the row requirement on `self`** (L175): the
        -- written receiverless call at positive arity.
        | (rename_i ih1
           (first | rw [ih1 (storeLe_subReq (by assumption) (by assumption)) (by assumption)] | rw [ih1 (storeLe_subReq (by assumption) (by assumption))])
           dsimp only
           rw [← hself, requireRow_sat (by assumption) (by assumption) hsat]
           simp)
        | (rename_i ih1
           rw [ih1]
           dsimp only
           rw [← hself, requireRow_sat (by assumption) (by assumption) hsat]
           simp)
        -- **`inferOpenArgs`' own two arms** (L175). `inferOpenArgs` is deliberately
        -- *not* in the `simp_all` list above: unfolding it there destroys the
        -- defining equation, and the send cases need that equation to push their
        -- store bound back through the argument list (`storeLe_subArgs`). So the
        -- traversal's own cases split on the answer and unfold it here instead.
        | (split
           all_goals (first
             | simp
             | (rename_i heq
                simp only [inferOpenArgs] at heq
                intro hle hr
                simp_all
                -- the recursive arm's residue: the head's IH (still an
                -- implication, discharged by the tail's monotonicity) and then the
                -- tail's, which `simp_all` has already instantiated.
                try (rename_i ih2 ih1
                     (first | rw [ih2 (storeLe_subArgs (by assumption) (by assumption)) (rets_subArgs (by assumption) (by assumption))] | rw [ih2 (storeLe_subArgs (by assumption) (by assumption))])
                     dsimp only
                     rw [ih1]
                     simp_all
                     -- the list equation the split left behind
                     try (rw [← heq.1]; simp)))
             | (rename_i heq
                simp only [inferOpenArgs] at heq
                simp_all)))
        -- **one argument, then the rest of the list** (L175): `inferArgs`' own
        -- recursive arm.
        | (rename_i ih2 ih1
           (first | rw [ih2 (storeLe_subArgs (by assumption) (by assumption)) (rets_subArgs (by assumption) (by assumption))] | rw [ih2 (storeLe_subArgs (by assumption) (by assumption))])
           dsimp only
           rw [ih1]
           simp_all)
        | (rename_i ih2 ih1
           (first | rw [ih2 (storeLe_subArgs (by assumption) (by assumption)) (rets_subArgs (by assumption) (by assumption))] | rw [ih2 (storeLe_subArgs (by assumption) (by assumption))])
           dsimp only
           (first | rw [ih1 (by assumption) (by assumption)] | rw [ih1 (by assumption)])
           simp_all)
        -- **one subexpression, then the row requirement on `self`** (L171): the
        -- unary written receiverless call, `foo(x)`. Same shape as the line above
        -- with `← hself` in front, because the receiver is `ctx.self` and the
        -- nominal rule reads `sigOf D (.cls ctx.cls)`.
        | (rename_i ih1
           (first | rw [ih1 (storeLe_subReq (by assumption) (by assumption)) (by assumption)] | rw [ih1 (storeLe_subReq (by assumption) (by assumption))])
           dsimp only
           rw [← hself, requireRow_sat (by assumption) (by assumption) hsat]
           simp)
        -- receiver, argument, then the row requirement (unary send on `var α`)
        | (rename_i ih2 ih1
           (first | rw [ih2 (storeLe_sub (by assumption) (storeLe_subReq (by assumption) (by assumption))) (rets_sub (by assumption) (by assumption))] | rw [ih2 (storeLe_sub (by assumption) (storeLe_subReq (by assumption) (by assumption)))])
           dsimp only
           (first | rw [ih1 (storeLe_subReq (by assumption) (by assumption)) (by assumption)] | rw [ih1 (storeLe_subReq (by assumption) (by assumption))])
           dsimp only
           rw [requireRow_sat (by assumption) (by assumption) hsat]
           simp)
        -- a condition, then the `if`-join
        | (rename_i ih2 ih1
           split
           all_goals (first
             | simp
             | (rename_i heq
                intro hle hr
                (first | rw [ih2 (storeLe_subIf heq hle) (rets_subIf heq hr)] | rw [ih2 (storeLe_subIf heq hle)])
                dsimp only
                rw [heq] at ih1
                (first | exact ih1 hle hr | exact ih1 hle))))
        -- a statement, then the rest of the sequence
        | (rename_i ih2 ih1
           split
           all_goals (first
             | simp
             | (rename_i heq
                intro hle hr
                (first | rw [ih2 (storeLe_subSeq heq hle) (rets_subSeq heq hr)] | rw [ih2 (storeLe_subSeq heq hle)])
                dsimp only
                rw [heq] at ih1
                (first | exact ih1 hle hr | exact ih1 hle))))
        | (trace_state; fail)
        -- the join's own refusal: the guard is false, so the arm is `True`
        | (split <;>
             (first
               | done
               | simp
               | (rename_i heq; split at heq <;> simp_all))))
    -- **A residual store bound** (L175). The variable-receiver send at positive
    -- arity leaves exactly one side goal — the `requireRow` step's own `StoreLe` —
    -- because the alternative that rewrote the rest of the arm could not name it.
    -- Discharged here rather than inside the alternative, so the alternatives stay
    -- one shape each.
    all_goals (try exact storeLe_subReq (by assumption) (by assumption))
    -- **And a residual *join*** (L193b), for exactly the reason above and found the
    -- same way: the two-subexpression alternative ends in `simp_all`, which reduces
    -- `inferIf` and leaves the join equation standing. It is a residual rather than an
    -- alternative because at the moment `first` runs, the goal is still the whole
    -- `FactorsIf` — the join equation does not exist yet.
    all_goals (try exact joinATy_subst (by assumption))

/-! ## 6. The decidable side — §8.2's discharge, and what it buys

`SatStore` is a proposition; `satStoreB` is the `Bool` a checker computes. The
lemma between them is what makes Layer 3 untrusted: the solver may produce `θ` by
any means, and the validator re-checks it by one `sigOf` lookup per row entry. -/

/-- §8.2's row job, over a whole store: one lookup per requirement. Linear, no
    search, and no `*`-elimination — which is §9.4's reason a checker can be
    extracted at all. -/
def satStoreB (D : Decls) (θ : TyVar → Ty) (st : Store) : Bool :=
  st.rows.all fun r => r.2.entries.all fun e =>
    sigOf D (θ r.1) e.1 == some (e.2.params.map (ATy.subst θ), e.2.ret.subst θ)

theorem rowOf_mem {st : Store} {α : TyVar} {n : String} {σ : ASig}
    (h : (st.rowOf α).get? n = some σ) :
    ∃ R, (α, R) ∈ st.rows ∧ (n, σ) ∈ R.entries := by
  unfold Store.rowOf at h
  cases hf : st.rows.find? (·.1 == α) with
  | none =>
    rw [hf] at h
    simp [Row.empty, Row.get?] at h
  | some p =>
    rw [hf] at h
    obtain ⟨a, R⟩ := p
    have hmem : (a, R) ∈ st.rows := List.mem_of_find?_eq_some hf
    have ha : a = α := by have := List.find?_some hf; simpa using this
    subst ha
    refine ⟨R, hmem, ?_⟩
    unfold Row.get? at h
    cases he : R.entries.find? (·.1 == n) with
    | none => rw [he] at h; simp at h
    | some e =>
      rw [he] at h
      simp only [Option.map_some, Option.some.injEq] at h
      have hme : e ∈ R.entries := List.mem_of_find?_eq_some he
      have hn : e.1 = n := by have := List.find?_some he; simpa using this
      obtain ⟨a', b'⟩ := e
      simp only at hn h
      subst hn; subst h
      exact hme

theorem satStoreB_sound {D : Decls} {θ : TyVar → Ty} {st : Store}
    (hb : satStoreB D θ st = true) : SatStore D θ st := by
  intro α n σ h
  obtain ⟨R, hR, he⟩ := rowOf_mem h
  have h1 := (List.all_eq_true.mp hb) (α, R) hR
  have h2 := (List.all_eq_true.mp h1) (n, σ) he
  simpa using h2

/-! ## 7. What R4 delivers to the metatheory

`UserConforms` (`Proof/Static/Decls.lean`) is the *checker's own verdict on a
method body, inside the soundness invariant* — the clause L157 introduced and
L163 first inhabited. Its premise is a successful nominal `infer` of the body.

`userConforms_of_inferBody` says **open-self inference discharges it**: type the
body with no row for its own class's accessors, produce `θ`, check the store, and
the invariant's clause follows. That is R4 landing in the metatheory's own
currency rather than beside it. -/

/-- **`inferBody`'s own `return` check, in the currency the factoring theorem wants**
    (L201). The check is a `List.all` over the collected types; the premise is a
    membership statement about their substitutions. One `beq` step apart. -/
theorem rets_of_all {rets : List ATy} {τ : ATy} {θ : TyVar → Ty}
    (h : rets.all (fun a => subATy a τ) = true) :
    ∀ a ∈ rets, subTy (ATy.subst θ a) (τ.subst θ) = true := by
  intro a ha
  exact subATy_subst (List.all_eq_true.mp h a ha)

/-- The body-level factoring theorem, at the store the body ends at.

    **L201 adds the return target to the conclusion**: the nominal context is now
    `ret := some (τ.subst θ)` — the body's own answer type. That is exactly the
    reading `inferBody`'s check enforces on the open side (`every collected return
    type equals the body's`), so the two halves say the same thing and the
    `return`-free case is unaffected: with no `return` in the body the nominal
    `infer` never reads `ctx.ret`. -/
theorem inferBody_sound {D : Decls} {c : String} {body : Expr} {τ : ATy} {Γ' : AEnv}
    {s' : OState} {θ : TyVar → Ty}
    (hb : inferBody D c body = .ok τ Γ' s')
    (hsat : SatStore D θ s'.st) (hself : θ 0 = .cls c) :
    infer D [] body false { cls := c, selfCls := some c, ret := some (τ.subst θ) }
      = some (τ.subst θ, substEnv θ Γ', D) := by
  have hf := inferOpen_factors D { cls := c, self := 0 } θ s'.st (τ.subst θ) hsat hself
    [] body { st := {}, fresh := 1 }
  unfold inferBody at hb
  cases hop : inferOpen D [] body { cls := c, self := 0 } { st := {}, fresh := 1 } with
  | ok τ₀ Γ₀ s₀ =>
    rw [hop] at hb
    dsimp only at hb
    split at hb
    · rename_i hall
      simp only [OResult.ok.injEq] at hb
      obtain ⟨rfl, rfl, rfl⟩ := hb
      rw [hop] at hf
      simpa [substEnv] using hf (StoreLe.refl _) (rets_of_all hall)
    · simp at hb
  | missing _ _ _ => rw [hop] at hb; simp at hb
  | outOfFragment _ => rw [hop] at hb; simp at hb

/-- **The parameter-open form** (L168), and it is the same theorem: the factoring
    theorem was quantified over `Γ` from the start, so binding parameters to fresh
    variables costs it nothing.

    Read the conclusion for exactly what it says and no more. The nominal
    judgement it lands in is `infer` **on the body**, in the environment the
    substitution gives the parameters — a judgement that exists today and is the
    one `infer`'s `def` arm would consult if it had parameters. It is *not* an
    `infer` accept of the `def`, because that arm requires `params.isEmpty`
    (`Types/Core.lean`). That gap is why `bodyVerdictWith` reports these bodies
    under their own constructor and their own census column: the body's typing is
    settled, its declaration is not, and merging the two counts would read as an
    accept-rate `check` does not have. -/
theorem inferBodyWith_sound {D : Decls} {c : String} {ps : List Param} {body : Expr}
    {Γb Γ' : AEnv} {τ : ATy} {s' : OState} {θ : TyVar → Ty}
    (hb : inferBodyWith D c ps body = some (Γb, .ok τ Γ' s'))
    (hsat : SatStore D θ s'.st) (hself : θ 0 = .cls c) :
    infer D (substEnv θ Γb) body false
        { cls := c, selfCls := some c, ret := some (τ.subst θ) }
      = some (τ.subst θ, substEnv θ Γ', D) := by
  unfold inferBodyWith at hb
  dsimp only at hb
  cases hop : openParams D { cls := c, self := 0 } ps [] { st := {}, fresh := 1 } with
  | none => rw [hop] at hb; simp at hb
  | some pf =>
    obtain ⟨Γ₀, s₀⟩ := pf
    rw [hop] at hb
    simp only [Option.some.injEq, Prod.mk.injEq] at hb
    obtain ⟨hΓ, hrun⟩ := hb
    subst hΓ
    have hf := inferOpen_factors D { cls := c, self := 0 } θ s'.st (τ.subst θ) hsat hself
      Γ₀ body s₀
    cases hr : inferOpen D Γ₀ body { cls := c, self := 0 } s₀ with
    | ok τ₀ Γ₁ s₁ =>
      rw [hr] at hrun
      dsimp only at hrun
      split at hrun
      · rename_i hall
        simp only [OResult.ok.injEq] at hrun
        obtain ⟨rfl, rfl, rfl⟩ := hrun
        rw [hr] at hf
        exact hf (StoreLe.refl _) (rets_of_all hall)
      · simp at hrun
    | missing _ _ _ => rw [hr] at hrun; simp at hrun
    | outOfFragment _ => rw [hr] at hrun; simp at hrun

/-- **The invariant's user-method clause, discharged by open-self inference.** -/
theorem userConforms_of_inferBody {D : Decls} {c : String} {md : MethodDef}
    {d : MethodDecl} {τ : ATy} {Γ' : AEnv} {s' : OState} {θ : TyVar → Ty}
    (hp : d.params = []) (hdf : defFree md.body = true)
    (hb : inferBody D c md.body = .ok τ Γ' s')
    (hsat : SatStore D θ s'.st) (hself : θ 0 = .cls c)
    (hret : τ.subst θ = d.ret) : UserConforms D c md d :=
  -- L201: `r = some d.ret` — the open front end now checks the body *against its own
  -- answer type*, so the row it discharges is one whose `return`s all agree with the
  -- declared return, and the clause's side condition is `hret` itself.
  ⟨hp, hdf, ⟨substEnv θ Γ', some d.ret,
    by rw [← hret]; exact inferBody_sound hb hsat hself,
    fun _ h => by simpa using h.symm⟩⟩

/-! ## 8. §4.3, end to end

The document's own example, run through every layer: `inferOpen` types the body
against an unresolved receiver, a substitution is produced, `satStoreB` checks it
by two table lookups, and **nominal `infer` accepts the same body** — which is the
factoring theorem doing its job on a real program rather than in the abstract. -/

/-- A table declaring `String#value : () → Integer`. `String` because it is the
    one class the fragment can both reopen and produce a value of
    (`reopenableClasses`, L151/L156). -/
def egRowD : Decls := addRow baseDecls "String" "value" { params := [], ret := .int }

/-- `value.zero?` — §4.3's shape (`value.hash`), with `zero?` in place of `hash`
    because `Integer#zero?` is the nullary row `baseDecls` actually declares. -/
def egRowBody : Expr := .send (some (.vcall "value")) "zero?" [] none

/-- The open run: type `α2`, and two rows — `α0 ⊒ ⟨value : () → α1⟩`,
    `α1 ⊒ ⟨zero? : () → α2⟩`. **No declaration for `value` is read.** -/
def egRowStore : Store :=
  { rows := [(1, { entries := [("zero?", { params := [], ret := .var 2 })] }),
             (0, { entries := [("value", { params := [], ret := .var 1 })] })] }

theorem egRow_open :
    inferBody egRowD "String" egRowBody = .ok (.var 2) [] { st := egRowStore, fresh := 3 } := by
  simp [inferBody, egRowBody, egRowStore, inferOpen, isSelf, requireRow,
    Store.rowOf, Row.get?, Row.insert, Store.setRow, Row.empty]

/-- The solver's answer: `self` is a `String`, what `value` returns is an
    `Integer`, what `zero?` returns is a `Boolean`. -/
def egTheta : TyVar → Ty
  | 0 => .cls "String"
  | 1 => .int
  | _ => .bool

/-- The validator's check — two `sigOf` lookups, decided in the kernel. -/
theorem egRow_sat : SatStore egRowD egTheta egRowStore :=
  satStoreB_sound (by decide)

/-- **And therefore nominal `infer` accepts the body**, at `Boolean`. Obtained
    from the factoring theorem, not by running `infer`. -/
theorem egRow_nominal :
    infer egRowD [] egRowBody false
        { cls := "String", selfCls := some "String", ret := some .bool }
      = some (.bool, [], egRowD) := by
  have := inferBody_sound egRow_open egRow_sat (by rfl)
  simpa [substEnv, egTheta] using this

/-! ## 8b. §7.3's `Γ_b`, end to end (L168)

The same four layers over a body with a **parameter**, which is the shape 58 of
the slice's 112 method bodies have (`homebrew/fragment-gap.py`'s third ratchet).
The point of the witness is which layer moved: `inferOpen` is unchanged, the
factoring theorem is unchanged, and the nominal judgement the parameter lands in
is `infer` at a *non-empty* environment — the one `infer` has always had. -/

/-- `def eq?(other) = other.zero?` — a parameter in receiver position, so the
    requirement is recorded against the **parameter's** variable and the residual
    row on `self` is empty. That is the case §7.3's `Γ_b` is for, and it is the
    one a class-level precondition cannot express. -/
def egParamBody : Expr := .send (some (.var .lvar "other")) "zero?" [] none

def egParamStore : Store :=
  { rows := [(1, { entries := [("zero?", { params := [], ret := .var 2 })] })] }

theorem egParam_open :
    inferBodyWith baseDecls "String" [.req "other"] egParamBody
      = some ([("other", .var 1)], .ok (.var 2) [("other", .var 1)]
          { st := egParamStore, fresh := 3 }) := by
  simp [inferBodyWith, openParams, egParamBody, egParamStore, inferOpen, isSelf,
    requireRow, Store.rowOf, Row.get?, Row.insert, Store.setRow, Row.empty,
    aenvGet?]

/-- The solver's answer: the parameter is an `Integer`, and `zero?` returns a
    `Boolean`. Note `θ 0` is still constrained — `self`'s variable exists whether
    or not the body mentions it. -/
def egParamTheta : TyVar → Ty
  | 0 => .cls "String"
  | 1 => .int
  | _ => .bool

theorem egParam_sat : SatStore baseDecls egParamTheta egParamStore :=
  satStoreB_sound (by decide)

/-- **Nominal `infer` accepts the body at `other : Integer`.** Obtained from
    `inferBodyWith_sound`, not by running `infer` — and note what it is *not*: an
    accept of the enclosing `def`, whose rule still requires `params.isEmpty`. -/
theorem egParam_nominal :
    infer baseDecls [("other", Ty.int)] egParamBody false
        { cls := "String", selfCls := some "String", ret := some .bool }
      = some (.bool, [("other", Ty.int)], baseDecls) := by
  have := inferBodyWith_sound egParam_open egParam_sat (by rfl)
  simpa [substEnv, egParamTheta] using this

/-! ## 9. Axiom hygiene -/

/-- info: 'RubyCore.Proof.Static.inferOpen_factors' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms inferOpen_factors

/-- info: 'RubyCore.Proof.Static.userConforms_of_inferBody' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms userConforms_of_inferBody

/-- info: 'RubyCore.Proof.Static.inferBodyWith_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms inferBodyWith_sound

/-- info: 'RubyCore.Proof.Static.egParam_nominal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms egParam_nominal

end Static
end Proof
end RubyCore
