import RubyCore.Proof.Static.OpenSelf
import RubyCore.Types.Discharge

/-!
# L262 — `discharge_sound`: the one theorem the whole-program pass needs

`Types/Discharge.lean` **drops requirements**. That is the only thing about it that can
be unsound, and this file is the statement that it is not:

```
discharge_sound :  SatStore D θ (discharge st)  →  SatProvs D θ st  →  SatStore D θ st
```

*A substitution that satisfies the discharged store, at a program whose own provisions
hold, satisfies the store the pass started from.* So a solver may be handed
`discharge Σ` — the small, cancelled thing — and its answer still discharges every
requirement `inferOpen` recorded.

## Why this is the right theorem, where `inferOpen_factors` was the right one before

`inferOpen_factors` is about **one body**: open-self typing factors through nominal
typing at a fixed declaration table, which is what makes an open accept re-derivable as
an `infer` accept and therefore costs `check` no consecution case. It cannot be the
theorem for a *program*, because a program's `def`s are precisely the things that change
the table, and generalizing `Factors` to thread `D` would oblige the open `def` arm to
satisfy `infer`'s `def` rule — including `params.isEmpty`, which excludes 67 of the
slice's 112 method bodies (`homebrew/HANDOFF.md` §The measurement that reordered the
work).

So the whole-program pass does not factor, and it does not claim to. What it claims is
this file's theorem, and the division of labour is clean:

* `inferOpen_factors` — each *body*'s typing is a nominal typing (unchanged, untouched;
  `inferOpen` gains no arm, `Types/Program.lean` is a driver over it);
* `discharge_sound` — the *cancellation* between bodies preserves what was required.

## The second premise is real, and is not discharged here

`SatProvs D θ st` says every provision holds: `sigOf D (θ α) n` really is the signature
the `def` supplied. That is a fact about the **table**, not about `θ` — it is true when
the class in question really does define the method, which is what `Types/Program.lean`'s
`def` arm records and what `infer`'s own `def` rule (`Types/Core.lean`) obliges when it
adds a row. Stating it as a premise rather than proving it here is the honest split:
this file is about the cancellation, and pretending the provision were free would make
the theorem vacuous in exactly the direction that matters.

`SatProvs` is deliberately `SatStore`'s **first clause, at the other field** — same
predicate, opposite polarity. That is what makes the last step of the proof one `rw`.
-/

namespace RubyCore
namespace Proof
namespace Static

open RubyCore.Types

set_option maxRecDepth 100000

/-! ## 1. The two relations this file adds -/

/-- **The provisions hold.** `SatStore`'s row clause read at `provs`: whatever the
    program was found to *supply* at `α`, the table really does supply at `θ α`. -/
def SatProvs (D : Decls) (θ : TyVar → Ty) (st : Store) : Prop :=
  ∀ α n σ, (st.provOf α).get? n = some σ →
    sigOf D (θ α) n = some (σ.params.map (ATy.subst θ), σ.ret.subst θ)

/-- **`θ` meets a list of pinned equalities.** The currency `pinPair` produces and
    `SatStore`'s second clause consumes; a separate abbreviation because the traversals
    below hand around *sublists* of the store's `eqs` and the monotonicity step is then
    `List.mem_append`. -/
def SatEqs (θ : TyVar → Ty) (es : List (TyVar × ATy)) : Prop :=
  ∀ p ∈ es, θ p.1 = p.2.subst θ

theorem SatEqs.left {θ : TyVar → Ty} {a b : List (TyVar × ATy)}
    (h : SatEqs θ (a ++ b)) : SatEqs θ a := fun p hp => h p (List.mem_append_left _ hp)

theorem SatEqs.right {θ : TyVar → Ty} {a b : List (TyVar × ATy)}
    (h : SatEqs θ (a ++ b)) : SatEqs θ b := fun p hp => h p (List.mem_append_right _ hp)

/-- The lookup `Row.get?` is, off the bare entry list — the traversals in
    `Types/Discharge.lean` rebuild that list, so the lemmas have to talk about it. -/
def getIn (es : List (String × ASig)) (n : String) : Option ASig :=
  (es.find? (·.1 == n)).map (·.2)

theorem getIn_eq (R : Row) (n : String) : R.get? n = getIn R.entries n := rfl

/-! ## 2. Pinning is sound

Each of the three functions in `Types/Discharge.lean` §1, and the conclusion is always
the same shape: *under the equalities it emitted, the two types are the same type*. -/

/-- **`pinPair`'s content.** The `.var` cases are exactly why the store has an `eqs`
    field at all (L206): `θ α = b.subst θ` is what an `eqv` atom says, and
    `(ATy.var α).subst θ` **is** `θ α`, so the emitted equality *is* the conclusion. -/
theorem pinPair_sound {θ : TyVar → Ty} {a b : ATy} {es : List (TyVar × ATy)}
    (h : pinPair a b = some es) (hθ : SatEqs θ es) :
    a.subst θ = b.subst θ := by
  unfold pinPair at h
  split at h
  · -- syntactic equality: the strongest case and it needs no equality at all
    next heq => exact congrArg (ATy.subst θ) (by simpa using heq)
  · next =>
    match a, b, h with
    | .var α, b, h =>
      simp at h
      exact hθ (α, b) (by simp [← h])
    | .nom t, .var β, h =>
      simp at h
      exact (hθ (β, .nom t) (by simp [← h])).symm
    | .nilOf t, .var β, h =>
      simp at h
      exact (hθ (β, .nilOf t) (by simp [← h])).symm

/-- Pointwise, and the induction is on the pair of lists: the length-indexing that makes
    an arity disagreement a `none` is what makes the two `nil` cases the only base. -/
theorem pinPairs_sound {θ : TyVar → Ty} :
    ∀ {as bs : List ATy} {es : List (TyVar × ATy)}, pinPairs as bs = some es →
      SatEqs θ es → as.map (ATy.subst θ) = bs.map (ATy.subst θ)
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, h, _ => by simp [pinPairs] at h
  | _ :: _, [], _, h, _ => by simp [pinPairs] at h
  | a :: as, b :: bs, es, h, hθ => by
    unfold pinPairs at h
    split at h
    · next e he =>
      split at h
      · next es' hes =>
        simp at h
        subst h
        simp only [List.map_cons]
        rw [pinPair_sound he hθ.left, pinPairs_sound hes hθ.right]
      · next => simp at h
    · next => simp at h

/-- **The requirement and the provision are the same signature.** Both components, for
    `SatStore`'s reason: its row clause obliges `sigOf D (θ α) n` to be the *pair*. -/
theorem dischargeSig_sound {θ : TyVar → Ty} {σ σp : ASig} {es : List (TyVar × ATy)}
    (h : dischargeSig σ σp = some es) (hθ : SatEqs θ es) :
    σ.params.map (ATy.subst θ) = σp.params.map (ATy.subst θ) ∧
      σ.ret.subst θ = σp.ret.subst θ := by
  unfold dischargeSig at h
  split at h
  · next esp hp =>
    split at h
    · next e he =>
      simp at h
      subst h
      exact ⟨pinPairs_sound hp hθ.left, pinPair_sound he hθ.right⟩
    · next => simp at h
  · next => simp at h

/-! ## 3. One variable's entries

The disjunction is the whole shape of the argument: a requirement either **survives** —
and then the discharged store's own satisfaction covers it — or it was **cancelled**, and
then the provision plus the emitted equalities cover it. There is no third case, which is
what makes the main theorem two `rcases`. -/

/-- Order preservation is the content of the left disjunct: `find?` stops at the first
    entry of its name, entries before it have other names, and `dischargeEntries` never
    reorders — so a kept entry is still the first of its name. -/
theorem dischargeEntries_spec (provR : Row) {θ : TyVar → Ty} :
    ∀ (es : List (String × ASig)) (n : String) (σ : ASig),
      getIn es n = some σ → SatEqs θ (dischargeEntries provR es).1 →
      getIn (dischargeEntries provR es).2 n = some σ
      ∨ (∃ σp, provR.get? n = some σp ∧
          σ.params.map (ATy.subst θ) = σp.params.map (ATy.subst θ) ∧
          σ.ret.subst θ = σp.ret.subst θ)
  | [], _, _, hg, _ => by simp [getIn] at hg
  | (m, τ) :: rest, n, σ, hg, hsat => by
    by_cases hmn : m = n
    · -- the head **is** the entry `find?` answered with
      subst hmn
      simp [getIn] at hg
      subst hg
      simp only [dischargeEntries]
      split
      · next σp hp =>
        split
        · next e he =>
          -- cancelled: the provision and the equalities discharge it
          exact Or.inr ⟨σp, hp, dischargeSig_sound he (by
            simp only [dischargeEntries, hp, he] at hsat
            exact hsat.left)⟩
        · next => exact Or.inl (by simp [getIn])
      · next => exact Or.inl (by simp [getIn])
    · -- a different name: both sides skip the head, whether or not it was kept
      have hg' : getIn rest n = some σ := by
        simp [getIn, hmn] at hg ⊢; exact hg
      have hsat' : SatEqs θ (dischargeEntries provR rest).1 := by
        simp only [dischargeEntries] at hsat
        split at hsat
        · split at hsat
          · exact hsat.right
          · exact hsat
        · exact hsat
      have ih := dischargeEntries_spec provR rest n σ hg' hsat'
      rcases ih with hk | hd
      · refine Or.inl ?_
        simp only [dischargeEntries]
        split
        · split
          · exact hk
          · simpa [getIn, hmn] using hk
        · simpa [getIn, hmn] using hk
      · exact Or.inr hd

/-! ## 4. The store's rows

Two facts, and both are about the association list rather than about the store: the
lookup commutes with the rewrite, and the equalities one variable contributed are among
the equalities all of them did. `setRow` prepends rather than replaces, so `rows` may
carry a variable twice — which is exactly why these are stated at `rowIn` and proved by
induction on the list instead of assumed. -/

/-- The lookup at the head, when the head is the key. -/
theorem rowIn_cons_self (α : TyVar) (R : Row) (rest : List (TyVar × Row)) :
    Store.rowIn ((α, R) :: rest) α = R := by
  simp [Store.rowIn]

/-- And when it is not. Stated as a lemma rather than `simp`ed inline because the
    inductive steps below need the result *folded back* into a `rowIn`, which a
    `List.find?_cons` rewrite leaves unfolded. -/
theorem rowIn_cons_ne {β α : TyVar} (R : Row) (rest : List (TyVar × Row)) (h : β ≠ α) :
    Store.rowIn ((β, R) :: rest) α = Store.rowIn rest α := by
  simp [Store.rowIn, h]

/-- **The rewrite commutes with the lookup.** `dischargeRows` maps each pair to the same
    key, so the first entry at `α` is still first. -/
theorem dischargeRows_lookup (P : List (TyVar × Row)) :
    ∀ (l : List (TyVar × Row)) (α : TyVar),
      Store.rowIn (dischargeRows P l).2 α
        = { Store.rowIn l α with
            entries := (dischargeEntries (Store.rowIn P α)
                          (Store.rowIn l α).entries).2 }
  | [], α => by
    rw [show Store.rowIn ([] : List (TyVar × Row)) α = Row.empty from rfl]
    simp [dischargeRows, Store.rowIn, Row.empty, dischargeEntries]
  | (β, R) :: rest, α => by
    by_cases h : β = α
    · subst h
      simp only [dischargeRows]
      rw [rowIn_cons_self, rowIn_cons_self]
    · simp only [dischargeRows]
      rw [rowIn_cons_ne _ _ h, rowIn_cons_ne _ _ h]
      exact dischargeRows_lookup P rest α

/-- **And the equalities survive.** One variable's contribution is a sublist of the
    whole, which is all the main theorem needs of it. -/
theorem dischargeRows_eqs (P : List (TyVar × Row)) :
    ∀ (l : List (TyVar × Row)) (α : TyVar) (p : TyVar × ATy),
      p ∈ (dischargeEntries (Store.rowIn P α) (Store.rowIn l α).entries).1 →
      p ∈ (dischargeRows P l).1
  | [], α, p, hp => by
    rw [show Store.rowIn ([] : List (TyVar × Row)) α = Row.empty from rfl] at hp
    simp [Row.empty, dischargeEntries] at hp
  | (β, R) :: rest, α, p, hp => by
    by_cases h : β = α
    · subst h
      rw [rowIn_cons_self] at hp
      simp only [dischargeRows]
      exact List.mem_append_left _ hp
    · rw [rowIn_cons_ne _ _ h] at hp
      simp only [dischargeRows]
      exact List.mem_append_right _ (dischargeRows_eqs P rest α p hp)

/-! ## 5. The theorem -/

/-- **`discharge` preserves what was required.**

    Read the two premises as the whole-program pass's own workflow: `discharge` ran and a
    solver (untrusted, `assertion-language.md` §8.4) produced a `θ` that satisfies the
    *cancelled* store; the program's `def`s really do install what the pass recorded them
    as installing. Then `θ` satisfies the store `inferOpen` actually built — every
    requirement from every body, including the ones the cancellation removed. -/
theorem discharge_sound {D : Decls} {θ : TyVar → Ty} {st : Store}
    (h : SatStore D θ (discharge st)) (hp : SatProvs D θ st) : SatStore D θ st := by
  refine ⟨fun α n σ hgs => ?_, fun α a ha => ?_⟩
  · -- **The rows.** Either the requirement survived the cancellation, or the provision
    -- that cancelled it answers for it.
    have hsat : SatEqs θ
        (dischargeEntries (Store.rowIn st.provs α) (Store.rowIn st.rows α).entries).1 :=
      fun p hpm => h.2 p.1 p.2 (by
        simp only [discharge]
        exact List.mem_append_right _ (dischargeRows_eqs st.provs st.rows α p hpm))
    have hgs' : getIn (Store.rowIn st.rows α).entries n = some σ := by
      rw [← getIn_eq]; exact hgs
    rcases dischargeEntries_spec (Store.rowIn st.provs α) _ n σ hgs' hsat with hk | hd
    · -- survived: the discharged store's own satisfaction is the answer
      refine h.1 α n σ ?_
      show Row.get? (Store.rowIn (discharge st).rows α) n = some σ
      rw [show (discharge st).rows = (dischargeRows st.provs st.rows).2 from rfl,
        dischargeRows_lookup st.provs st.rows α, getIn_eq]
      exact hk
    · -- cancelled: `SatProvs` supplies the signature and the equalities align it
      obtain ⟨σp, hprov, hps, hret⟩ := hd
      have := hp α n σp hprov
      rw [this, hps, hret]
  · -- **The equalities.** `discharge` only ever appends, so the store's own are still
    -- there — this is `StoreLe`'s `eqs` clause, spent inline.
    exact h.2 α a (by simp only [discharge]; exact List.mem_append_left _ ha)

/-! ## 6. Two sanity corollaries

Neither is used downstream; both are here because a theorem with two premises can be
true and be about nothing, and these say which way each premise leans. -/

/-- With no provisions, every entry is kept — `Row.empty.get?` is `none` at every name. -/
theorem dischargeEntries_empty (es : List (String × ASig)) :
    (dischargeEntries Row.empty es).2 = es := by
  induction es with
  | nil => rfl
  | cons f fs ih =>
    obtain ⟨n, σ⟩ := f
    have hn : Row.get? Row.empty n = none := rfl
    simp only [dischargeEntries, hn]
    rw [ih]

theorem dischargeRows_nil_provs :
    ∀ l : List (TyVar × Row), (dischargeRows [] l).2 = l
  | [] => rfl
  | (α, R) :: rest => by
    simp only [dischargeRows]
    rw [show Store.rowIn ([] : List (TyVar × Row)) α = Row.empty from rfl,
      dischargeEntries_empty, dischargeRows_nil_provs rest]

/-- A store with **no provisions** is its own discharge, so §5 is trivially the identity
    there — which is the check that the cancellation, and not the statement, does the
    work. -/
theorem discharge_nil_provs (st : Store) (h : st.provs = []) :
    (discharge st).rows = st.rows := by
  simp only [discharge]
  rw [h, dischargeRows_nil_provs]

/-- And the other lean: `SatProvs` at the **empty** provisions is vacuous, so nothing in
    §5 is smuggled in through it. -/
theorem satProvs_nil {D : Decls} {θ : TyVar → Ty} {st : Store} (h : st.provs = []) :
    SatProvs D θ st := by
  intro α n σ hg
  have he : st.provOf α = Row.empty := by unfold Store.provOf; rw [h]; rfl
  rw [he] at hg
  simp [Row.get?, Row.empty] at hg

end Static
end Proof
end RubyCore
