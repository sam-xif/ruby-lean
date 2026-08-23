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
   inferOpen D Γ e ctx il s = .ok τ Γ' s'     (the open run succeeded)
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
  /-- **And every equality requirement survives** (L206). The second field for the
      second field of `Store`, and monotone for the same reason: `addEq` only
      prepends, so a later store asks for at least as much. -/
  eqs : ∀ p, p ∈ st.eqs → p ∈ st'.eqs

theorem StoreLe.refl (st : Store) : StoreLe st st := ⟨fun _ _ _ h => h, fun _ h => h⟩

theorem StoreLe.trans {a b c : Store} (h₁ : StoreLe a b) (h₂ : StoreLe b c) :
    StoreLe a c :=
  ⟨fun α n σ h => h₂.get α n σ (h₁.get α n σ h), fun p h => h₂.eqs p (h₁.eqs p h)⟩

/-- **A substitution satisfies a store**: every requirement it records is met by
    the table at the substituted receiver type. This is exactly what
    `dischargeRow`/`dischargeNom` decide over one class; `satStoreB` (§6) decides it
    over a whole store, and `satStoreB_sound` is the bridge. -/
def SatStore (D : Decls) (θ : TyVar → Ty) (st : Store) : Prop :=
  (∀ α n σ, (st.rowOf α).get? n = some σ →
    sigOf D (θ α) n = some (σ.params.map (ATy.subst θ), σ.ret.subst θ)) ∧
  -- **L206's equalities.** Not a capability but a *pin*: the join recorded that `α` has
  -- no freedom left, and this is where the solver's choice is held to it.
  (∀ α a, (α, a) ∈ st.eqs → θ α = a.subst θ)

theorem SatStore.mono {D : Decls} {θ : TyVar → Ty} {st st' : Store}
    (hle : StoreLe st st') (hs : SatStore D θ st') : SatStore D θ st :=
  ⟨fun α n σ h => hs.1 α n σ (hle.get α n σ h), fun α a h => hs.2 α a (hle.eqs _ h)⟩

/-- **`addEq` only grows the store** (L206) — the `rows` half is untouched (a record
    update at a different field) and the `eqs` half gains one entry. -/
theorem storeLe_addEq (st : Store) (α : TyVar) (a : ATy) : StoreLe st (st.addEq α a) := by
  unfold Store.addEq
  split
  · exact StoreLe.refl _
  · exact ⟨fun _ _ _ h => h, fun _ hp => List.mem_cons_of_mem _ hp⟩

/-- **And so does the join** (L206). Two of `joinOpen`'s three answers leave the store
    alone; the third is one `addEq`. -/
theorem joinOpen_mono {st st' : Store} {a b c : ATy}
    (h : Store.joinOpen st a b = some (c, st')) : StoreLe st st' := by
  unfold Store.joinOpen at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact StoreLe.refl _
  · split at h <;>
      first
        | (simp only [Option.some.injEq, Prod.mk.injEq] at h
           obtain ⟨-, rfl⟩ := h
           exact storeLe_addEq _ _ _)
        | exact absurd h (by simp)

/-- **The equality the join just recorded is in the store it produced** (L206) — one
    `split` on `addEq`'s idempotence guard. -/
theorem mem_addEq (st : Store) (α : TyVar) (a : ATy) : (α, a) ∈ (st.addEq α a).eqs := by
  unfold Store.addEq
  split
  · rename_i hc; simpa using List.mem_of_elem_eq_true (by simpa using hc)
  · exact List.mem_cons_self

/-- The two shapes the recorded equality is spent at, stated so the case can be one
    `exact` and unification can supply `α` and `c` from the goal. -/
theorem joinTy_of_eq {θ : TyVar → Ty} {α : TyVar} {c : ATy} (h : θ α = c.subst θ) :
    joinTy (θ α) (c.subst θ) = some (c.subst θ) := by rw [h]; simp [joinTy]

theorem joinTy_of_eq' {θ : TyVar → Ty} {β : TyVar} {c : ATy} (h : θ β = c.subst θ) :
    joinTy (c.subst θ) (θ β) = some (c.subst θ) := by rw [h]; simp [joinTy]

/-- **`joinOpen` agrees with `joinTy` under a satisfying substitution** (L206) — the
    factoring theorem's join step, and the reason the store carries equalities at all.

    Where `joinATy` answered, this is `joinATy_subst`. Where it did not, the answer came
    with a *requirement*, and the requirement is exactly what makes the nominal join's
    **first** branch fire: `θ α = b.subst θ`, so the two sides are equal and the join is
    reflexivity. That is the whole content of the rung — a refusal turned into a
    condition on `θ`, discharged by the validator rather than by the checker. -/
theorem joinOpen_subst {D : Decls} {θ : TyVar → Ty} {stF st st' : Store} {a b c : ATy}
    (h : Store.joinOpen st a b = some (c, st'))
    (hle : StoreLe st' stF) (hsat : SatStore D θ stF) :
    joinTy (a.subst θ) (b.subst θ) = some (c.subst θ) := by
  unfold Store.joinOpen at h
  split at h
  · rename_i c' hj
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact joinATy_subst hj
  · split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact joinTy_of_eq (hsat.2 _ _ (hle.eqs _ (mem_addEq _ _ _)))
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact joinTy_of_eq' (hsat.2 _ _ (hle.eqs _ (mem_addEq _ _ _)))
    · exact absurd h (by simp)

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
      refine ⟨fun β m σ' hm => ?_, fun p hp => hp⟩
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
      have := hsat.1 α n σ (hle.get α n σ hg)
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
      exact hsat.1 α n _ hstF

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
theorem inferOpen_mono (D : Decls) (ctx : OCtx) (Γ : AEnv) (e : Expr) (il : Option AEnv)
    (s : OState) :
    ∀ τ Γ' s', inferOpen D Γ e ctx il s = .ok τ Γ' s' → StoreLe s.st s'.st := by
  induction Γ, e, il, s using inferOpen.induct (D := D) (ctx := ctx)
    (motive2 := fun Γ t els il s => ∀ τ Γ' s',
        inferOpenIf D Γ t els ctx il s = .ok τ Γ' s' → StoreLe s.st s'.st)
    (motive3 := fun Γ es il s => ∀ τ Γ' s',
        inferOpenSeq D Γ es ctx il s = .ok τ Γ' s' → StoreLe s.st s'.st)
    -- **L175's argument traversal.** Same statement at the fourth motive; the send
    -- arms' chain is now `inferOpen recv → inferOpenArgs → requireRow`, so the
    -- transitivity alternatives below gained one link.
    -- **L230: `motive4` is `inferOpenElems` and `motive5` is `inferOpenArgs`** — the
    -- order is the mutual block's, not the file's, and the two have the same signature so
    -- a swapped assignment type-checks and only the IHs reveal it. Measured, twice: the
    -- nominal side has the same trap (`Mono.lean`).
    (motive4 := fun Γ es il s => ∀ τ Γ' s',
        inferOpenElems D Γ es ctx il s = .ok τ Γ' s' → StoreLe s.st s'.st)
    (motive5 := fun Γ es il s => ∀ τs Γ' s',
        inferOpenArgs D Γ es ctx il s = .ok τs Γ' s' → StoreLe s.st s'.st) with
  | _ =>
    intros
    simp_all [inferOpen, inferOpenSeq, inferOpenIf, inferOpenArgs, inferOpenElems]
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
      -- **L206: the `if`-join may now grow the store**, so the two `inferOpenIf` arms
      -- gain a link — `joinOpen_mono` — at the end of their chain.
      | exact StoreLe.trans (by assumption) (joinOpen_mono (by assumption))
      | exact StoreLe.trans (StoreLe.trans (by assumption) (by assumption))
          (joinOpen_mono (by assumption))
      | exact joinOpen_mono (by assumption)
      -- **L237: the splat operand's `addEq`**, and it is the only arm that grows the
      -- store outside a join — one extra link in the same chain shape.
      | exact StoreLe.trans (by assumption)
          (StoreLe.trans (storeLe_addEq _ _ _) (by assumption))

/-- **And `rets` is monotone too** (L201), for the store's reason: a recorded return
    type is a positive fact, so the list only grows. Subset rather than sublist because
    that is all the consumer needs — `Factors`' premise is about *membership* in the
    final state's list, and the composition at every compound arm is exactly this
    lemma, the way `StoreLe` is for the store.

    Same induction, same uniform block, and the same discipline: adding an arm to
    `inferOpen` re-opens both proofs. -/
theorem inferOpen_rets (D : Decls) (ctx : OCtx) (Γ : AEnv) (e : Expr) (il : Option AEnv)
    (s : OState) :
    ∀ τ Γ' s', inferOpen D Γ e ctx il s = .ok τ Γ' s' → ∀ x ∈ s.rets, x ∈ s'.rets := by
  induction Γ, e, il, s using inferOpen.induct (D := D) (ctx := ctx)
    (motive2 := fun Γ t els il s => ∀ τ Γ' s',
        inferOpenIf D Γ t els ctx il s = .ok τ Γ' s' → ∀ x ∈ s.rets, x ∈ s'.rets)
    (motive3 := fun Γ es il s => ∀ τ Γ' s',
        inferOpenSeq D Γ es ctx il s = .ok τ Γ' s' → ∀ x ∈ s.rets, x ∈ s'.rets)
    (motive4 := fun Γ es il s => ∀ τ Γ' s',
        inferOpenElems D Γ es ctx il s = .ok τ Γ' s' → ∀ x ∈ s.rets, x ∈ s'.rets)
    (motive5 := fun Γ es il s => ∀ τs Γ' s',
        inferOpenArgs D Γ es ctx il s = .ok τs Γ' s' → ∀ x ∈ s.rets, x ∈ s'.rets) with
  | _ =>
    intros
    simp_all [inferOpen, inferOpenSeq, inferOpenIf, inferOpenArgs, inferOpenElems]
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
      -- **L236: the `if`'s guard is a conjunction `simp_all` cannot decide**, so the
      -- answer stays wrapped in an `ite` and the equation cannot be destructured until
      -- one `split` has chosen a side. Before the alternative below, which would try the
      -- `obtain` and fail hard rather than backtrack.
      | (rename_i hh hmem; split at hh <;> simp_all)
      | (rename_i hh; split at hh <;> simp_all)
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
theorem inferOpenIf_mono (D : Decls) (ctx : OCtx) (il : Option AEnv) (Γ : AEnv) (t : Expr)
    (els : Option Expr) (s : OState) :
    ∀ τ Γ' s', inferOpenIf D Γ t els ctx il s = .ok τ Γ' s' → StoreLe s.st s'.st := by
  intro τ Γ' s' h
  unfold inferOpenIf at h
  cases els with
  | some e =>
    dsimp only at h
    cases ht : inferOpen D Γ t ctx il s with
    | ok τt Γt st =>
      rw [ht] at h
      dsimp only at h
      cases he : inferOpen D Γ e ctx il st with
      | ok τe Γe se =>
        rw [he] at h
        dsimp only at h
        split at h
        · -- L193b adds the join's own split; both accepting arms leave `se` alone,
          -- so the store bound is the same composition it was.
          -- L206: and the join's own step, which may record an equality.
          split at h
          · rename_i hj
            simp only [OResult.ok.injEq] at h
            obtain ⟨-, -, rfl⟩ := h
            exact StoreLe.trans (inferOpen_mono D ctx Γ t il s τt Γt st ht)
              (StoreLe.trans (inferOpen_mono D ctx Γ e il st τe Γe se he)
                (joinOpen_mono hj))
          · simp at h
        · simp at h
      | missing _ _ _ => rw [he] at h; simp at h
      | outOfFragment _ => rw [he] at h; simp at h
    | missing _ _ _ => rw [ht] at h; simp at h
    | outOfFragment _ => rw [ht] at h; simp at h
  | none =>
    dsimp only at h
    cases ht : inferOpen D Γ t ctx il s with
    | ok τt Γt st =>
      rw [ht] at h
      dsimp only at h
      split at h
      · split at h
        · rename_i hj
          simp only [OResult.ok.injEq] at h
          obtain ⟨-, -, rfl⟩ := h
          exact StoreLe.trans (inferOpen_mono D ctx Γ t il s τt Γt st ht) (joinOpen_mono hj)
        · simp at h
      · simp at h
    | missing _ _ _ => rw [ht] at h; simp at h
    | outOfFragment _ => rw [ht] at h; simp at h

/-- The statement sequence's, by induction on the list. -/
theorem inferOpenSeq_mono (D : Decls) (ctx : OCtx) (il : Option AEnv) :
    ∀ (es : List Expr) (Γ : AEnv) (s : OState) τ Γ' s',
      inferOpenSeq D Γ es ctx il s = .ok τ Γ' s' → StoreLe s.st s'.st := by
  intro es
  induction es with
  | nil => intro Γ s τ Γ' s' h; unfold inferOpenSeq at h; cases h; exact StoreLe.refl _
  | cons e rest ih =>
    intro Γ s τ Γ' s' h
    unfold inferOpenSeq at h
    cases rest with
    | nil => exact inferOpen_mono D ctx Γ e il s τ Γ' s' h
    | cons e2 rest2 =>
      dsimp only at h
      cases he : inferOpen D Γ e ctx il s with
      | ok τ₁ Γ₁ s₁ =>
        rw [he] at h
        dsimp only at h
        exact StoreLe.trans (inferOpen_mono D ctx Γ e il s τ₁ Γ₁ s₁ he)
          (ih Γ₁ s₁ τ Γ' s' h)
      | missing _ _ _ => rw [he] at h; simp at h
      | outOfFragment _ => rw [he] at h; simp at h

/-! ### Pushing a bound down to a subexpression

The shape every case of the factoring theorem needs, stated so that the tactic
can find it by unification alone: whatever store bounds the *node*'s output also
bounds its subexpressions', because the store only grows. -/

theorem storeLe_sub {D : Decls} {ctx : OCtx} {il : Option AEnv} {Γ : AEnv} {e : Expr} {s s' : OState}
    {τ : ATy} {Γ' : AEnv} {stF : Store}
    (h : inferOpen D Γ e ctx il s = .ok τ Γ' s') (hle : StoreLe s'.st stF) :
    StoreLe s.st stF :=
  StoreLe.trans (inferOpen_mono D ctx Γ e il s τ Γ' s' h) hle

theorem storeLe_subReq {st st' stF : Store} {α : TyVar} {n : String} {args : List ATy}
    {f : TyVar} {τ : ATy} (h : requireRow st α n args f = some (τ, st'))
    (hle : StoreLe st' stF) : StoreLe st stF :=
  StoreLe.trans (requireRow_mono h) hle

theorem storeLe_subIf {D : Decls} {ctx : OCtx} {il : Option AEnv} {Γ : AEnv} {t : Expr}
    {els : Option Expr} {s s' : OState} {τ : ATy} {Γ' : AEnv} {stF : Store}
    (h : inferOpenIf D Γ t els ctx il s = .ok τ Γ' s') (hle : StoreLe s'.st stF) :
    StoreLe s.st stF :=
  StoreLe.trans (inferOpenIf_mono D ctx il Γ t els s τ Γ' s' h) hle

theorem storeLe_subSeq {D : Decls} {ctx : OCtx} {il : Option AEnv} {Γ : AEnv} {es : List Expr}
    {s s' : OState} {τ : ATy} {Γ' : AEnv} {stF : Store}
    (h : inferOpenSeq D Γ es ctx il s = .ok τ Γ' s') (hle : StoreLe s'.st stF) :
    StoreLe s.st stF :=
  StoreLe.trans (inferOpenSeq_mono D ctx il es Γ s τ Γ' s' h) hle

/-- **L230's element traversal, monotone** — `inferOpenSeq_mono`'s twin at the fifth
    function, and shorter: there is no `[e]` special case, and the splat arm's operand is
    an `inferOpen` like any other. -/
theorem inferOpenElems_mono (D : Decls) (ctx : OCtx) (il : Option AEnv) :
    ∀ (es : List Expr) (Γ : AEnv) (s : OState) τ Γ' s',
      inferOpenElems D Γ es ctx il s = .ok τ Γ' s' → StoreLe s.st s'.st := by
  intro es
  induction es with
  | nil => intro Γ s τ Γ' s' h; unfold inferOpenElems at h; cases h; exact StoreLe.refl _
  | cons e rest ih =>
    intro Γ s τ Γ' s' h
    unfold inferOpenElems at h
    cases e
    case splat oe =>
      cases oe with
      | none => simp only at h; exact absurd h (by simp [inferOpen])
      | some o =>
        simp only at h
        cases ho : inferOpen D Γ o ctx il s with
        | ok τ₁ Γ₁ s₁ =>
          rw [ho] at h
          cases τ₁ with
          | nom t =>
            cases t with
            | cls nm =>
              by_cases hnm : nm = "Array"
              · subst hnm
                exact StoreLe.trans (inferOpen_mono D ctx Γ o il s _ _ _ ho)
                  (ih Γ₁ s₁ τ Γ' s' h)
              · simp_all
            | _ => simp_all
          -- **L237: the variable operand**, and it is the one arm of this proof that
          -- grows the store rather than only threading it — one `storeLe_addEq` between
          -- the operand's chain and the rest of the list's.
          | var β =>
            exact StoreLe.trans (inferOpen_mono D ctx Γ o il s _ _ _ ho)
              (StoreLe.trans (storeLe_addEq _ β _) (ih Γ₁ _ τ Γ' s' h))
          | nilOf _ => simp_all
        | missing a b c => rw [ho] at h; exact absurd h (by simp)
        | outOfFragment hd => rw [ho] at h; exact absurd h (by simp)
    all_goals
      (simp only at h
       first
         | (cases he : inferOpen D Γ _ ctx il s with
            | ok τ₁ Γ₁ s₁ =>
              rw [he] at h
              exact StoreLe.trans (inferOpen_mono D ctx Γ _ il s _ _ _ he)
                (ih Γ₁ s₁ τ Γ' s' h)
            | missing a b c => rw [he] at h; exact absurd h (by simp)
            | outOfFragment hd => rw [he] at h; exact absurd h (by simp))
         | simp_all)

theorem storeLe_subElems {D : Decls} {ctx : OCtx} {il : Option AEnv} {Γ : AEnv}
    {es : List Expr} {s s' : OState} {τ : ATy} {Γ' : AEnv} {stF : Store}
    (h : inferOpenElems D Γ es ctx il s = .ok τ Γ' s') (hle : StoreLe s'.st stF) :
    StoreLe s.st stF :=
  StoreLe.trans (inferOpenElems_mono D ctx il es Γ s τ Γ' s' h) hle

/-- The argument list's monotonicity (L175), by list induction on top of
    `inferOpen_mono` — `inferOpenSeq_mono`'s twin, and needed for the same reason:
    a send's store bound has to reach its arguments. -/
theorem inferOpenArgs_mono (D : Decls) (ctx : OCtx) (il : Option AEnv) :
    ∀ (es : List Expr) (Γ : AEnv) (s : OState) τs Γ' s',
      inferOpenArgs D Γ es ctx il s = .ok τs Γ' s' → StoreLe s.st s'.st := by
  intro es
  induction es with
  | nil => intro Γ s τs Γ' s' h; unfold inferOpenArgs at h; cases h; exact StoreLe.refl _
  | cons e rest ih =>
    intro Γ s τs Γ' s' h
    unfold inferOpenArgs at h
    cases he : inferOpen D Γ e ctx il s with
    | ok τ₁ Γ₁ s₁ =>
      rw [he] at h
      dsimp only at h
      cases hr : inferOpenArgs D Γ₁ rest ctx il s₁ with
      | ok τs₂ Γ₂ s₂ =>
        rw [hr] at h
        simp only [OArgs.ok.injEq] at h
        obtain ⟨-, -, rfl⟩ := h
        exact StoreLe.trans (inferOpen_mono D ctx Γ e il s τ₁ Γ₁ s₁ he)
          (ih Γ₁ s₁ τs₂ Γ₂ s₂ hr)
      | missing _ _ _ => rw [hr] at h; simp at h
      | outOfFragment _ => rw [hr] at h; simp at h
    | missing _ _ _ => rw [he] at h; simp at h
    | outOfFragment _ => rw [he] at h; simp at h

theorem storeLe_subArgs {D : Decls} {ctx : OCtx} {il : Option AEnv} {Γ : AEnv} {es : List Expr}
    {s s' : OState} {τs : List ATy} {Γ' : AEnv} {stF : Store}
    (h : inferOpenArgs D Γ es ctx il s = .ok τs Γ' s') (hle : StoreLe s'.st stF) :
    StoreLe s.st stF :=
  StoreLe.trans (inferOpenArgs_mono D ctx il es Γ s τs Γ' s' h) hle

/-- The `if`-join's `rets` monotonicity — `inferOpenIf_mono`'s twin (L201). -/
theorem inferOpenIf_rets (D : Decls) (ctx : OCtx) (il : Option AEnv) (Γ : AEnv) (t : Expr)
    (els : Option Expr) (s : OState) :
    ∀ τ Γ' s', inferOpenIf D Γ t els ctx il s = .ok τ Γ' s' → ∀ x ∈ s.rets, x ∈ s'.rets := by
  intro τ Γ' s' h
  unfold inferOpenIf at h
  cases els with
  | some e =>
    dsimp only at h
    cases ht : inferOpen D Γ t ctx il s with
    | ok τt Γt st =>
      rw [ht] at h
      dsimp only at h
      cases he : inferOpen D Γ e ctx il st with
      | ok τe Γe se =>
        rw [he] at h
        dsimp only at h
        split at h
        · split at h
          · simp only [OResult.ok.injEq] at h
            obtain ⟨-, -, rfl⟩ := h
            exact fun x hx => inferOpen_rets D ctx Γ e il st τe Γe se he x
              (inferOpen_rets D ctx Γ t il s τt Γt st ht x hx)
          · simp at h
        · simp at h
      | missing _ _ _ => rw [he] at h; simp at h
      | outOfFragment _ => rw [he] at h; simp at h
    | missing _ _ _ => rw [ht] at h; simp at h
    | outOfFragment _ => rw [ht] at h; simp at h
  | none =>
    dsimp only at h
    cases ht : inferOpen D Γ t ctx il s with
    | ok τt Γt st =>
      rw [ht] at h
      dsimp only at h
      split at h
      · split at h
        · simp only [OResult.ok.injEq] at h
          obtain ⟨-, -, rfl⟩ := h
          exact inferOpen_rets D ctx Γ t il s τt Γt st ht
        · simp at h
      · simp at h
    | missing _ _ _ => rw [ht] at h; simp at h
    | outOfFragment _ => rw [ht] at h; simp at h

/-- The sequence's (L201). -/
theorem inferOpenSeq_rets (D : Decls) (ctx : OCtx) (il : Option AEnv) :
    ∀ (es : List Expr) (Γ : AEnv) (s : OState) τ Γ' s',
      inferOpenSeq D Γ es ctx il s = .ok τ Γ' s' → ∀ x ∈ s.rets, x ∈ s'.rets := by
  intro es
  induction es with
  | nil => intro Γ s τ Γ' s' h; unfold inferOpenSeq at h; cases h; exact fun x hx => hx
  | cons e rest ih =>
    intro Γ s τ Γ' s' h
    unfold inferOpenSeq at h
    cases rest with
    | nil => exact inferOpen_rets D ctx Γ e il s τ Γ' s' h
    | cons e2 rest2 =>
      dsimp only at h
      cases he : inferOpen D Γ e ctx il s with
      | ok τ₁ Γ₁ s₁ =>
        rw [he] at h
        dsimp only at h
        exact fun x hx => ih Γ₁ s₁ τ Γ' s' h x (inferOpen_rets D ctx Γ e il s τ₁ Γ₁ s₁ he x hx)
      | missing _ _ _ => rw [he] at h; simp at h
      | outOfFragment _ => rw [he] at h; simp at h

/-- **And L230's element traversal's** — `inferOpenElems_mono`'s shape at `rets`. -/
theorem inferOpenElems_rets (D : Decls) (ctx : OCtx) (il : Option AEnv) :
    ∀ (es : List Expr) (Γ : AEnv) (s : OState) τ Γ' s',
      inferOpenElems D Γ es ctx il s = .ok τ Γ' s' → ∀ x ∈ s.rets, x ∈ s'.rets := by
  intro es
  induction es with
  | nil => intro Γ s τ Γ' s' h; unfold inferOpenElems at h; cases h; exact fun x hx => hx
  | cons e rest ih =>
    intro Γ s τ Γ' s' h
    unfold inferOpenElems at h
    cases e
    case splat oe =>
      cases oe with
      | none => simp only at h; exact absurd h (by simp [inferOpen])
      | some o =>
        simp only at h
        cases ho : inferOpen D Γ o ctx il s with
        | ok τ₁ Γ₁ s₁ =>
          rw [ho] at h
          cases τ₁ with
          | nom t =>
            cases t with
            | cls nm =>
              by_cases hnm : nm = "Array"
              · subst hnm
                exact fun x hx => ih Γ₁ s₁ τ Γ' s' h x
                  (inferOpen_rets D ctx Γ o il s _ _ _ ho x hx)
              · simp_all
            | _ => simp_all
          -- L237: `addEq` touches the store, not `rets`, so the composition is the same
          -- two steps the `Array` arm has.
          | var _ =>
            exact fun x hx => ih Γ₁ _ τ Γ' s' h x
              (inferOpen_rets D ctx Γ o il s _ _ _ ho x hx)
          | nilOf _ => simp_all
        | missing a b c => rw [ho] at h; exact absurd h (by simp)
        | outOfFragment hd => rw [ho] at h; exact absurd h (by simp)
    all_goals
      (simp only at h
       first
         | (cases he : inferOpen D Γ _ ctx il s with
            | ok τ₁ Γ₁ s₁ =>
              rw [he] at h
              exact fun x hx => ih Γ₁ s₁ τ Γ' s' h x
                (inferOpen_rets D ctx Γ _ il s _ _ _ he x hx)
            | missing a b c => rw [he] at h; exact absurd h (by simp)
            | outOfFragment hd => rw [he] at h; exact absurd h (by simp))
         | simp_all)

/-- And the argument list's (L201). -/
theorem inferOpenArgs_rets (D : Decls) (ctx : OCtx) (il : Option AEnv) :
    ∀ (es : List Expr) (Γ : AEnv) (s : OState) τs Γ' s',
      inferOpenArgs D Γ es ctx il s = .ok τs Γ' s' → ∀ x ∈ s.rets, x ∈ s'.rets := by
  intro es
  induction es with
  | nil => intro Γ s τs Γ' s' h; unfold inferOpenArgs at h; cases h; exact fun x hx => hx
  | cons e rest ih =>
    intro Γ s τs Γ' s' h
    unfold inferOpenArgs at h
    cases he : inferOpen D Γ e ctx il s with
    | ok τ₁ Γ₁ s₁ =>
      rw [he] at h
      dsimp only at h
      cases hr : inferOpenArgs D Γ₁ rest ctx il s₁ with
      | ok τs₂ Γ₂ s₂ =>
        rw [hr] at h
        simp only [OArgs.ok.injEq] at h
        obtain ⟨-, -, rfl⟩ := h
        exact fun x hx => ih Γ₁ s₁ τs₂ Γ₂ s₂ hr x (inferOpen_rets D ctx Γ e il s τ₁ Γ₁ s₁ he x hx)
      | missing _ _ _ => rw [hr] at h; simp at h
      | outOfFragment _ => rw [hr] at h; simp at h
    | missing _ _ _ => rw [he] at h; simp at h
    | outOfFragment _ => rw [he] at h; simp at h

/-! ### Pushing the *return* bound down to a subexpression (L201)

`storeLe_sub`'s twin, for the second premise the factoring theorem now carries:
whatever bounds the *node*'s collected `return` types also bounds its
subexpressions', because `rets` only grows too. -/

theorem rets_sub {D : Decls} {ctx : OCtx} {il : Option AEnv} {Γ : AEnv} {e : Expr} {s s' : OState}
    {τ : ATy} {Γ' : AEnv} {θ : TyVar → Ty} {retF : Ty}
    (h : inferOpen D Γ e ctx il s = .ok τ Γ' s')
    (hr : ∀ a ∈ s'.rets, subTy (ATy.subst θ a) retF = true) :
    ∀ a ∈ s.rets, subTy (ATy.subst θ a) retF = true :=
  fun a ha => hr a (inferOpen_rets D ctx Γ e il s τ Γ' s' h a ha)

theorem rets_subIf {D : Decls} {ctx : OCtx} {il : Option AEnv} {Γ : AEnv} {t : Expr} {els : Option Expr}
    {s s' : OState} {τ : ATy} {Γ' : AEnv} {θ : TyVar → Ty} {retF : Ty}
    (h : inferOpenIf D Γ t els ctx il s = .ok τ Γ' s')
    (hr : ∀ a ∈ s'.rets, subTy (ATy.subst θ a) retF = true) :
    ∀ a ∈ s.rets, subTy (ATy.subst θ a) retF = true :=
  fun a ha => hr a (inferOpenIf_rets D ctx il Γ t els s τ Γ' s' h a ha)

theorem rets_subSeq {D : Decls} {ctx : OCtx} {il : Option AEnv} {Γ : AEnv} {es : List Expr}
    {s s' : OState} {τ : ATy} {Γ' : AEnv} {θ : TyVar → Ty} {retF : Ty}
    (h : inferOpenSeq D Γ es ctx il s = .ok τ Γ' s')
    (hr : ∀ a ∈ s'.rets, subTy (ATy.subst θ a) retF = true) :
    ∀ a ∈ s.rets, subTy (ATy.subst θ a) retF = true :=
  fun a ha => hr a (inferOpenSeq_rets D ctx il es Γ s τ Γ' s' h a ha)

/-- **L237: the same two bridges across the splat operand's `addEq`.** The factoring's
    elems alternative composes its bound through the *recursive* call, and after L237 that
    call runs at a store one `addEq` up — so the bridge has to step over it. Stated rather
    than inlined because the alternative cannot name the state. -/
theorem storeLe_subElemsEq {D : Decls} {ctx : OCtx} {il : Option AEnv} {Γ : AEnv}
    {es : List Expr} {s s' : OState} {τ : ATy} {Γ' : AEnv} {stF : Store} {α : TyVar} {a : ATy}
    (h : inferOpenElems D Γ es ctx il { s with st := s.st.addEq α a } = .ok τ Γ' s')
    (hle : StoreLe s'.st stF) : StoreLe s.st stF :=
  StoreLe.trans (storeLe_addEq _ α a) (storeLe_subElems h hle)

/-- **L237: the splat operand's requirement, discharged.** `θ α = t`, from the equality the
    rule recorded before recursing — carried to `stF` by the elems bridge and satisfied by
    `hsat`. Stated as a lemma rather than assembled in the factoring proof because the
    tactic block cannot name `α`: a `have` whose *type* mentions it would leave a
    placeholder, and an unsolvable placeholder inside `have … : T := by …` is a **logged**
    error rather than a backtrackable failure, so it would abort the alternative block
    instead of falling through to the next shape. -/
theorem eq_of_addEq_subElems {D : Decls} {θ : TyVar → Ty} {stF : Store} {ctx : OCtx}
    {il : Option AEnv} {Γ : AEnv} {es : List Expr} {s s' : OState} {τ : ATy} {Γ' : AEnv}
    {α : TyVar} {t : Ty}
    (heq : inferOpenElems D Γ es ctx il { s with st := s.st.addEq α (.nom t) } = .ok τ Γ' s')
    (hle : StoreLe s'.st stF) (hsat : SatStore D θ stF) : θ α = t :=
  hsat.2 _ _ ((storeLe_subElems heq hle).eqs _ (mem_addEq _ _ _))

theorem rets_subElems {D : Decls} {ctx : OCtx} {il : Option AEnv} {Γ : AEnv} {es : List Expr}
    {s s' : OState} {τ : ATy} {Γ' : AEnv} {θ : TyVar → Ty} {retF : Ty}
    (h : inferOpenElems D Γ es ctx il s = .ok τ Γ' s')
    (hr : ∀ a ∈ s'.rets, subTy (ATy.subst θ a) retF = true) :
    ∀ a ∈ s.rets, subTy (ATy.subst θ a) retF = true :=
  fun a ha => hr a (inferOpenElems_rets D ctx il es Γ s τ Γ' s' h a ha)

theorem rets_subArgs {D : Decls} {ctx : OCtx} {il : Option AEnv} {Γ : AEnv} {es : List Expr}
    {s s' : OState} {τs : List ATy} {Γ' : AEnv} {θ : TyVar → Ty} {retF : Ty}
    (h : inferOpenArgs D Γ es ctx il s = .ok τs Γ' s')
    (hr : ∀ a ∈ s'.rets, subTy (ATy.subst θ a) retF = true) :
    ∀ a ∈ s.rets, subTy (ATy.subst θ a) retF = true :=
  fun a ha => hr a (inferOpenArgs_rets D ctx il es Γ s τs Γ' s' h a ha)

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
    (il : Option AEnv) (Γ : AEnv) (e : Expr) : OResult → Prop
  | .ok τ Γ' s' => StoreLe s'.st stF → (∀ a ∈ s'.rets, subTy (a.subst θ) retF = true) →
      infer D (substEnv θ Γ) e false
          { cls := ctx.cls, selfCls := some ctx.cls, ret := some retF, meth := ctx.meth,
            params := ctx.params.map (List.map (ATy.subst θ)),
            inLoop := il.map (substEnv θ) }
        = some (τ.subst θ, substEnv θ Γ', D)
  | _ => True

/-- The `inferIf`/`inferSeq` forms, which differ only in which nominal function
    the conclusion names. -/
def FactorsIf (D : Decls) (θ : TyVar → Ty) (stF : Store) (retF : Ty) (ctx : OCtx)
    (il : Option AEnv) (Γ : AEnv) (t : Expr) (els : Option Expr) : OResult → Prop
  | .ok τ Γ' s' => StoreLe s'.st stF → (∀ a ∈ s'.rets, subTy (a.subst θ) retF = true) →
      inferIf D (substEnv θ Γ) t els false
          { cls := ctx.cls, selfCls := some ctx.cls, ret := some retF, meth := ctx.meth,
            params := ctx.params.map (List.map (ATy.subst θ)),
            inLoop := il.map (substEnv θ) }
        = some (τ.subst θ, substEnv θ Γ', D)
  | _ => True

def FactorsSeq (D : Decls) (θ : TyVar → Ty) (stF : Store) (retF : Ty) (ctx : OCtx)
    (il : Option AEnv) (Γ : AEnv) (es : List Expr) : OResult → Prop
  | .ok τ Γ' s' => StoreLe s'.st stF → (∀ a ∈ s'.rets, subTy (a.subst θ) retF = true) →
      inferSeq D (substEnv θ Γ) es false
          { cls := ctx.cls, selfCls := some ctx.cls, ret := some retF, meth := ctx.meth,
            params := ctx.params.map (List.map (ATy.subst θ)),
            inLoop := il.map (substEnv θ) }
        = some (τ.subst θ, substEnv θ Γ', D)
  | _ => True

/-- And the argument list's (L175). The only one whose conclusion is about a *list*
    of types, which is exactly why `inferArgs` is a separate traversal from
    `inferSeq`. -/
def FactorsArgs (D : Decls) (θ : TyVar → Ty) (stF : Store) (retF : Ty) (ctx : OCtx)
    (il : Option AEnv) (Γ : AEnv) (es : List Expr) : OArgs → Prop
  | .ok τs Γ' s' => StoreLe s'.st stF → (∀ a ∈ s'.rets, subTy (a.subst θ) retF = true) →
      inferArgs D (substEnv θ Γ) es false
          { cls := ctx.cls, selfCls := some ctx.cls, ret := some retF, meth := ctx.meth,
            params := ctx.params.map (List.map (ATy.subst θ)),
            inLoop := il.map (substEnv θ) }
        = some (τs.map (ATy.subst θ), substEnv θ Γ', D)
  | _ => True

/-- **And the array literal's elements** (L230), the fifth — `FactorsSeq`'s statement at
    `inferElems`, and the type component is **`.nilT` on both sides**.

    That is not a normalization: both traversals *always* answer `.nilT`, because an array
    literal's element types are erased (the empty case answers it and every other case
    hands the tail's answer through). Writing it out rather than quantifying it
    existentially is what lets this motive share the sequence's alternatives in the proof
    below — the existential version needed its own, and could not be closed by them. -/
def FactorsElems (D : Decls) (θ : TyVar → Ty) (stF : Store) (retF : Ty) (ctx : OCtx)
    (il : Option AEnv) (Γ : AEnv) (es : List Expr) : OResult → Prop
  | .ok _ Γ' s' => StoreLe s'.st stF → (∀ a ∈ s'.rets, subTy (a.subst θ) retF = true) →
      inferElems D (substEnv θ Γ) es false
          { cls := ctx.cls, selfCls := some ctx.cls, ret := some retF, meth := ctx.meth,
            params := ctx.params.map (List.map (ATy.subst θ)),
            inLoop := il.map (substEnv θ) }
        = some (.nilT, substEnv θ Γ', D)
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

/-- **The one-armed `if`, with the store** (L206) — `mkNilable_join`'s twin at
    `joinOpen`, and stated for the same reason: the goal is a bare type equation, so the
    equation has to be handed over rather than rewritten with. -/
theorem mkNilable_joinOpen {D : Decls} {θ : TyVar → Ty} {stF st st' : Store} {a c : ATy}
    (h : Store.joinOpen st a (.nom .nilT) = some (c, st'))
    (hle : StoreLe st' stF) (hsat : SatStore D θ stF) :
    mkNilable (a.subst θ) = c.subst θ := by
  have h1 := joinOpen_subst h hle hsat
  rw [show (ATy.nom Ty.nilT).subst θ = Ty.nilT from rfl, joinTy_nilT_right] at h1
  simpa using h1

/-- **The open environment check is stronger than the nominal one** (L227) — the whole
    soundness content of the open `next` rule, and it is one implication: `subAEnvB`
    compares `ATy`s syntactically, so a matching entry keeps matching after `θ` is applied,
    while `subEnvB` only ever asks about the *substituted* types. The converse is false and
    is not needed: the open pass is allowed to be conservative. -/
theorem subAEnvB_subst {θ : TyVar → Ty} {Γl Γ : AEnv} (h : subAEnvB Γl Γ = true) :
    subEnvB (substEnv θ Γl) (substEnv θ Γ) = true := by
  unfold subEnvB substEnv
  rw [List.all_map]
  refine List.all_eq_true.mpr ?_
  intro e he
  -- L236: the check compares *lookups*, so both sides are `aenvGet_subst` at the same
  -- witness — the entry's own payload never appears.
  have hq := List.all_eq_true.mp h e he
  simp only [beq_iff_eq] at hq
  obtain ⟨a, ha⟩ := aenvGet?_of_mem he
  rw [ha] at hq
  show (_ == _) = true
  simp only [beq_iff_eq]
  rw [show envGet? (List.map (fun e => (e.1, ATy.subst θ e.2)) Γ) e.1 = some (a.subst θ) from
        by simpa [substEnv] using aenvGet_subst (θ := θ) hq,
      show envGet? (List.map (fun e => (e.1, ATy.subst θ e.2)) Γl) e.1 = some (a.subst θ) from
        by simpa [substEnv] using aenvGet_subst (θ := θ) ha]

theorem inferOpen_factors (D : Decls) (ctx : OCtx) (θ : TyVar → Ty) (stF : Store)
    (retF : Ty) (hsat : SatStore D θ stF) (hself : θ ctx.self = .cls ctx.cls)
    (Γ : AEnv) (e : Expr) (il : Option AEnv) (s : OState) :
    Factors D θ stF retF ctx il Γ e (inferOpen D Γ e ctx il s) := by
  induction Γ, e, il, s using inferOpen.induct (D := D) (ctx := ctx)
    (motive2 := fun Γ t els il s =>
      FactorsIf D θ stF retF ctx il Γ t els (inferOpenIf D Γ t els ctx il s))
    (motive3 := fun Γ es il s =>
      FactorsSeq D θ stF retF ctx il Γ es (inferOpenSeq D Γ es ctx il s))
    -- L230: `motive4` is the *elements* traversal and `motive5` the argument list — the
    -- mutual block's order, not the file's. See `inferOpen_mono`'s note.
    (motive4 := fun Γ es il s =>
      FactorsElems D θ stF retF ctx il Γ es (inferOpenElems D Γ es ctx il s))
    (motive5 := fun Γ es il s =>
      FactorsArgs D θ stF retF ctx il Γ es (inferOpenArgs D Γ es ctx il s)) with
  | _ =>
    simp_all [inferOpen, inferOpenSeq, inferOpenIf, inferOpenElems, Factors, FactorsIf,
      FactorsSeq, FactorsArgs, FactorsElems, infer, inferSeq, inferIf, inferArgs,
      inferElems, substEnv_aenvSet, hself]
    all_goals (try intro hle)
    -- L201's second premise: the collected `return` types all agree with the
    -- body's, pushed down to the subexpressions by `rets_sub` below.
    all_goals (try intro hr)
    -- L193b: `joinATy_subst` is a *conditional* rewrite whose hypothesis is in the
    -- context, so `simp_all` can discharge it and close the join cases here. It has
    -- to be in this set rather than in the alternative block below, because
    -- `simp_all` is what leaves those goals in the first place.
    -- L206: and `joinOpen_subst`, which is the same conditional rewrite with the
    -- store's satisfaction as a second hypothesis — also in context, so also
    -- dischargeable here.
    all_goals (try simp_all [joinATy_subst, joinOpen_subst, subAEnvB_subst])
    all_goals (
      first
        | done
        -- **L227's environment check.** The arm is a guard `simp_all` reduces away, leaving
        -- exactly the `subEnvB` obligation the nominal `next` rule asks for — and the whole
        -- factoring is that the open check is the stronger one. An *alternative* rather
        -- than a residual, because the alternatives below `split` and would consume the
        -- goal before a residual ran.
        | exact subAEnvB_subst (by assumption)
        -- **L228's global write.** The open arm decides `subATy τ (.nom σ)` and the
        -- nominal one asks for `subTy (τ.subst θ) σ` — which is `subATy_subst`, the
        -- lemma that arm exists to use.
        | exact subATy_subst (by assumption)
        -- **The `if` join with a *recorded* equality** (L206). The store now changes at
        -- the join, so the two IHs' bounds are one `joinOpen_mono` further away than
        -- they were and `simp_all` cannot find them. Supplying the three composed
        -- hypotheses first is all this case needs; `joinOpen_subst` then closes it as
        -- `joinATy_subst` used to.
        -- **L236: the `if`'s environment guard, both arms.** The open rule decides
        -- `subAEnvB` and the nominal one asks for `subEnvB` at the substituted
        -- environments, which is `subAEnvB_subst` — the same lemma L227's `next` uses,
        -- now with the store threading of L206 stacked in front of it. Two alternatives
        -- because the two-armed `if` leaves a conjunction and the one-armed one a
        -- `mkNilable` equation.
        | (have hle2 := StoreLe.trans (joinOpen_mono (by assumption)) hle
           have hle3 := storeLe_sub (by assumption) hle2
           have hr2 := rets_sub (by assumption) hr
           simp_all [subAEnvB_subst]
           exact joinOpen_subst (by assumption) hle hsat)
        | (have hle2 := StoreLe.trans (joinOpen_mono (by assumption)) hle
           have hle3 := storeLe_sub (by assumption) hle2
           have hr2 := rets_sub (by assumption) hr
           simp_all [subAEnvB_subst]
           exact mkNilable_joinOpen (by assumption) hle hsat)
        | (have hle2 := StoreLe.trans (joinOpen_mono (by assumption)) hle
           have hle3 := storeLe_sub (by assumption) hle2
           have hr2 := rets_sub (by assumption) hr
           simp_all [subAEnvB_subst])
        | (have hle2 := StoreLe.trans (joinOpen_mono (by assumption)) hle
           simp_all
           exact joinOpen_subst (by assumption) hle hsat)
        | (have hle2 := StoreLe.trans (joinOpen_mono (by assumption)) hle
           simp_all)
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
        -- **L230's array elements**, both accepting arms — the sequence alternative's
        -- shape with `storeLe_subElems`/`rets_subElems` in place of the `Seq` twins. The
        -- *splat* arm's operand IH lands where the element's does, because the arm's
        -- nominal shape is the same match one indirection in.
        | (rename_i ih2 ih1
           split
           all_goals (first
             | simp
             | (rename_i heq
                intro hle hr
                -- **L237: the store bound is *named* before it is used**, and that is not
                -- style: the recursive call runs one `addEq` up in the splat-operand arm,
                -- so two bridges are possible — and a `rw` whose argument fails to
                -- elaborate is a *logged* error rather than a backtrackable failure, so
                -- `first | rw … | rw …` would abort the block instead of trying the
                -- second. An `exact` inside a `have` backtracks.
                have hb := by
                  first
                    -- the `addEq` bridge *first*: its premise pins the state to a
                    -- record update, so it cannot fire on the plain shape, while the
                    -- plain one unifies with either.
                    | exact storeLe_subElemsEq heq hle
                    | exact storeLe_subElems heq hle
                (first
                  | rw [ih2 hb (rets_subElems heq hr)]
                  | rw [ih2 hb])
                dsimp only
                rw [heq] at ih1
                (first | exact ih1 hle hr | exact ih1 hle))))
        -- **And the same two arms *after* `simp_all` has already split them** (L230).
        -- `simp_all` reduces `FactorsElems` at the recursive call, so the case arrives
        -- with its `heq` in context and the `split` above has nothing to do — the
        -- alternative is the same three rewrites without it. `rename_i` names six because
        -- the two IHs are not the last inaccessible hypotheses here.
        | (rename_i ih2 ih1 _ _ _ _
           intro hle hr
           rw [ih2 (storeLe_subElems heq hle) (rets_subElems heq hr)]
           dsimp only
           rw [heq] at ih1
           (first | exact ih1 hle hr | exact ih1 hle))
        -- the join's own refusal: the guard is false, so the arm is `True`
        | (split <;>
             (first
               | done
               | simp
               | (rename_i heq; split at heq <;> simp_all)))
        -- **L230's third elems shape**: the case arrives with its recursive call
        -- *unreduced*, so the `split` is needed after all. Three alternatives for one
        -- traversal is the cost of `simp_all` reducing some cases and not others — and it
        -- is cheaper than teaching `simp_all` which.
        | (rename_i ih2 ih1
           split
           all_goals (first
             | simp
             -- **L237: the splat operand at a *variable*** — the one shape whose nominal
             -- counterpart needs a fact about `θ` rather than about the sub-derivation.
             -- The rule matched on `Ty.cls "Array"` and the IH answers `θ α`, so the
             -- recorded equality is spent here: `mem_addEq` at the store the recursive
             -- call ran in, carried to `stF` by the plain bridge and satisfied by `hsat`.
             -- Its own *inner* option, because the `have` is what fails on every other
             -- shape — and an alternative of the outer chain would have to succeed on all
             -- of the `split`'s goals at once.
             | (rename_i heq
                intro hle hr
                have hEq := by exact eq_of_addEq_subElems heq hle hsat
                have hb := by exact storeLe_subElemsEq heq hle
                have hr2 := by exact rets_subElems heq hr
                (first
                  | rw [ih2 hb hr2]
                  | rw [ih2 hb])
                rw [hEq]
                try dsimp only
                rw [heq] at ih1
                (first | exact ih1 hle hr | exact ih1 hle))
             | (rename_i heq
                intro hle hr
                -- L237: and the plain shape, whose bridge is the one that was here before.
                have hb := by exact storeLe_subElems heq hle
                (first
                  | rw [ih2 hb (rets_subElems heq hr)]
                  | rw [ih2 hb])
                try dsimp only
                rw [heq] at ih1
                (first | exact ih1 hle hr | exact ih1 hle)))))
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
  (st.rows.all fun r => r.2.entries.all fun e =>
    sigOf D (θ r.1) e.1 == some (e.2.params.map (ATy.subst θ), e.2.ret.subst θ)) &&
  -- L206: and the equalities, which is the half a `decide` can do in one step.
  (st.eqs.all fun e => θ e.1 == e.2.subst θ)

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
  unfold satStoreB at hb
  simp only [Bool.and_eq_true] at hb
  refine ⟨fun α n σ h => ?_, fun α a hm => ?_⟩
  · obtain ⟨R, hR, he⟩ := rowOf_mem h
    have h1 := (List.all_eq_true.mp hb.1) (α, R) hR
    have h2 := (List.all_eq_true.mp h1) (n, σ) he
    simpa using h2
  · -- L206: the equality half is a `List.all` over the same list the proposition
    -- quantifies over, so it is one `all_eq_true` and a `beq`.
    have := (List.all_eq_true.mp hb.2) (α, a) hm
    simpa using this

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

/-- **`joinRets` is a join: the body's answer and every recorded `return` are below it**
    (L229), which is `rets_of_all`'s replacement and supplies the *same* two premises
    `Factors` asks for — the second one verbatim, and the first one is new, because the
    body's own answer is now strictly below the type `inferBody` reports.

    The whole proof is `joinATy_subst` (the open join commutes with `θ`) composed with
    `joinTy_sub` (both sides of a nominal join are below it), once per element. -/
theorem joinRets_sub {θ : TyVar → Ty} : ∀ {rets : List ATy} {τ τj : ATy},
    joinRets rets τ = some τj →
    subTy (τ.subst θ) (τj.subst θ) = true ∧
      ∀ a ∈ rets, subTy (a.subst θ) (τj.subst θ) = true
  | [], τ, τj, h => by
      simp only [joinRets, Option.some.injEq] at h
      subst h
      exact ⟨subTy_refl _, by simp⟩
  | a :: rest, τ, τj, h => by
      simp only [joinRets] at h
      cases hr : joinRets rest τ with
      | none => rw [hr] at h; simp at h
      | some τ₁ =>
        rw [hr] at h
        obtain ⟨hτ, hall⟩ := joinRets_sub (θ := θ) hr
        obtain ⟨hl, hrr⟩ := joinTy_sub (joinATy_subst (θ := θ) h)
        refine ⟨subTy_trans hτ hrr, ?_⟩
        intro b hb
        rcases List.mem_cons.mp hb with rfl | hb'
        · exact hl
        · exact subTy_trans (hall b hb') hrr

/-- The body-level factoring theorem, at the store the body ends at.

    **L201 adds the return target to the conclusion**: the nominal context is now
    `ret := some (τ.subst θ)` — the body's own answer type. That is exactly the
    reading `inferBody`'s check enforces on the open side (`every collected return
    type equals the body's`), so the two halves say the same thing and the
    `return`-free case is unaffected: with no `return` in the body the nominal
    `infer` never reads `ctx.ret`. -/
theorem inferBody_sound {D : Decls} {c mname : String} {body : Expr} {τ : ATy} {Γ' : AEnv}
    {s' : OState} {θ : TyVar → Ty}
    (hb : inferBody D c mname body = .ok τ Γ' s')
    (hsat : SatStore D θ s'.st) (hself : θ 0 = .cls c) :
    -- **L229: the answer is the *join*, so the body's own type is only *below* it** — and
    -- that is the whole change to this statement. `infer` still answers the body's type;
    -- what `inferBody` reports is the type of the method, which is the join of its exits.
    ∃ τ0, infer D [] body false
        { cls := c, selfCls := some c, ret := some (τ.subst θ), meth := some mname,
          params := some [] }
        = some (τ0, substEnv θ Γ', D) ∧ subTy τ0 (τ.subst θ) = true := by
  have hf := inferOpen_factors D { cls := c, self := 0, meth := some mname, params := some [] } θ s'.st
    (τ.subst θ) hsat hself [] body none { st := {}, fresh := 1 }
  unfold inferBody at hb
  cases hop : inferOpen D [] body { cls := c, self := 0, meth := some mname, params := some [] }
      none { st := {}, fresh := 1 } with
  | ok τ₀ Γ₀ s₀ =>
    rw [hop] at hb
    dsimp only at hb
    split at hb
    · rename_i τj hall
      simp only [OResult.ok.injEq] at hb
      obtain ⟨rfl, rfl, rfl⟩ := hb
      rw [hop] at hf
      obtain ⟨hbelow, hrets⟩ := joinRets_sub (θ := θ) hall
      exact ⟨τ₀.subst θ, by simpa [substEnv] using hf (StoreLe.refl _) hrets, hbelow⟩
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
theorem inferBodyWith_sound {D : Decls} {c mname : String} {ps : List Param} {body : Expr}
    {Γb Γ' : AEnv} {τ : ATy} {s' : OState} {θ : TyVar → Ty}
    (hb : inferBodyWith D c mname ps body = some (Γb, .ok τ Γ' s'))
    (hsat : SatStore D θ s'.st) (hself : θ 0 = .cls c) :
    -- L229's widening, as in `inferBody_sound`: the reported type is the join of the
    -- method's exits, and the body's own answer is below it.
    ∃ τ0, infer D (substEnv θ Γb) body false
        { cls := c, selfCls := some c, ret := some (τ.subst θ), meth := some mname,
          params := (openParamTys ps).map (List.map (ATy.subst θ)) }
      = some (τ0, substEnv θ Γ', D) ∧ subTy τ0 (τ.subst θ) = true := by
  unfold inferBodyWith at hb
  dsimp only at hb
  cases hop : openParams D
      ({ cls := c, self := 0, meth := some mname, params := openParamTys ps } : OCtx)
      ps [] { st := {}, fresh := 1 } with
  | none => rw [hop] at hb; simp at hb
  | some pf =>
    obtain ⟨Γ₀, s₀⟩ := pf
    rw [hop] at hb
    simp only [Option.some.injEq, Prod.mk.injEq] at hb
    obtain ⟨hΓ, hrun⟩ := hb
    subst hΓ
    have hf := inferOpen_factors D
      { cls := c, self := 0, meth := some mname, params := openParamTys ps } θ s'.st
      (τ.subst θ) hsat hself Γ₀ body none s₀
    cases hr : inferOpen D Γ₀ body
        ({ cls := c, self := 0, meth := some mname, params := openParamTys ps } : OCtx)
        none s₀ with
    | ok τ₀ Γ₁ s₁ =>
      rw [hr] at hrun
      dsimp only at hrun
      split at hrun
      · rename_i τj hall
        simp only [OResult.ok.injEq] at hrun
        obtain ⟨rfl, rfl, rfl⟩ := hrun
        rw [hr] at hf
        obtain ⟨hbelow, hrets⟩ := joinRets_sub (θ := θ) hall
        exact ⟨τ₀.subst θ, hf (StoreLe.refl _) hrets, hbelow⟩
      · simp at hrun
    | missing _ _ _ => rw [hr] at hrun; simp at hrun
    | outOfFragment _ => rw [hr] at hrun; simp at hrun

/-- **The invariant's user-method clause, discharged by open-self inference.** -/
theorem userConforms_of_inferBody {D : Decls} {c mname : String} {md : MethodDef}
    {d : MethodDecl} {τ : ATy} {Γ' : AEnv} {s' : OState} {θ : TyVar → Ty}
    (hp : d.params = []) (hblk : d.blk = none) (hdf : defFree md.body = true)
    (hb : inferBody D c mname md.body = .ok τ Γ' s')
    (hsat : SatStore D θ s'.st) (hself : θ 0 = .cls c)
    (hret : τ.subst θ = d.ret) : UserConforms D c mname md d :=
  -- L201: `r = some d.ret` — the open front end now checks the body *against its own
  -- answer type*, so the row it discharges is one whose `return`s all agree with the
  -- declared return, and the clause's side condition is `hret` itself.
  ⟨hp, hblk, hdf, by
    obtain ⟨τ0, heq, hsub⟩ := inferBody_sound (θ := θ) hb hsat hself
    rw [hret] at heq hsub
    exact ⟨substEnv θ Γ', some d.ret, τ0, heq, hsub, fun _ h => by simpa using h.symm⟩⟩

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
    inferBody egRowD "String" "value" egRowBody = .ok (.var 2) [] { st := egRowStore, fresh := 3 } := by
  simp [joinRets, inferBody, egRowBody, egRowStore, inferOpen, isSelf, requireRow,
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
        { cls := "String", selfCls := some "String", ret := some .bool, meth := some "value",
          params := some [] }
      = some (.bool, [], egRowD) := by
  -- L229: `inferBody_sound` now hands over the body's own type *below* the reported
  -- one; here they coincide (the body has no `return`), and `subTy` at an atomic type is
  -- an equality (`subTy_atomic`) — so the witness is one `obtain` longer than it was.
  obtain ⟨τ0, heq, hsub⟩ := inferBody_sound egRow_open egRow_sat (by rfl)
  have : τ0 = .bool := by
    simpa using (subTy_atomic (τ := Ty.bool) (by simp) (by simp)).mp
      (by simpa [substEnv, egTheta] using hsub)
  rw [this] at heq
  simpa [substEnv, egTheta] using heq

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
    inferBodyWith baseDecls "String" "cmp" [.req "other"] egParamBody
      = some ([("other", .var 1)], .ok (.var 2) [("other", .var 1)]
          { st := egParamStore, fresh := 3 }) := by
  simp [joinRets, inferBodyWith, openParams, egParamBody, egParamStore, inferOpen, isSelf,
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
        { cls := "String", selfCls := some "String", ret := some .bool, meth := some "cmp",
          -- **L214**: the nominal context now carries the parameter types the open run
          -- opened them at, substituted — `[.int]` here, and that is the *whole* content
          -- of the channel `zsuper` reads. Note what it also shows: this context is one
          -- `infer` accepts and no *machine* context matches, because `StackCtx` pins an
          -- activation's `params` to `some []`. Which is the standing `accept (params
          -- open)` has had since L168, now visible in the type rather than in prose.
          params := some [.int] }
      = some (.bool, [("other", Ty.int)], baseDecls) := by
  -- L229, as in `egRow_nominal`: the body's own type comes back below the reported one,
  -- and at an atomic type `subTy` is an equality.
  obtain ⟨τ0, heq, hsub⟩ := inferBodyWith_sound egParam_open egParam_sat (by rfl)
  have : τ0 = .bool := by
    simpa using (subTy_atomic (τ := Ty.bool) (by simp) (by simp)).mp
      (by simpa [substEnv, egParamTheta] using hsub)
  rw [this] at heq
  simpa [substEnv, egParamTheta, openParamTys] using heq

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
