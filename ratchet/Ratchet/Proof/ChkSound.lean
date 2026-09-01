import Ratchet.Validate

/-!
# `chk` only ever answers with a real derivation

The single theorem that makes `Ratchet/Validate.lean`'s `Bool` worth reading:

  `chk_sound : chk e = some τ → Judge e τ`

i.e. the executable checker never certifies anything the hand-authored judgment
(`Ratchet/Judge.lean`) does not derive. This is *not* the semantic soundness theorem —
that one (`validate p = true → ∀ r, Reachable p r → ¬ typeStuck r`) needs the
semantics in the statement and is still future work (`AGENTS.md` §What is deliberately
not built). What this gives is the reduction: trusting `validate` on rungs 1–13 now
requires trusting **only** the ~13 constructors of `Judge`/`PrimSig`, each of which is a
one-line, human-checkable claim about the real semantics, rather than trusting `chk`'s
control flow.

Axiom-clean: the `#print axioms` at the bottom is part of the file.
-/

namespace Ratchet

/-- `eqSafe?` never admits a receiver `EqSafe` does not. -/
theorem eqSafe?_sound {σ : Ty} (h : eqSafe? σ = true) : EqSafe σ := by
  cases σ
  all_goals
    first
      | exact .int
      | exact .float
      | exact .bool
      | exact .nilT
      | exact .sym
      | exact .cls
      | exact absurd h (by simp [eqSafe?])

/-- `primSig?` and `PrimSig` agree in the direction that matters: the executable table
never invents a signature the specification lacks. Proved by case exhaustion over the
table rows, in the order they are written in `Validate.lean`: the guarded `==` row
first, then the fixed rows, then the catch-all `none` (which contradicts `h`). -/
theorem primSig?_sound {σ : Ty} {m : String} {argTys : List Ty} {τ : Ty}
    (h : primSig? σ m argTys = some τ) : PrimSig σ m argTys τ := by
  unfold primSig? at h
  split at h
  · -- the guarded `==` row: the receiver had to pass `eqSafe?`
    split at h
    · injection h with h
      subst h
      exact .objEq (eqSafe?_sound (by assumption))
    · exact absurd h (by simp)
  all_goals
    first
      | (injection h with h
         subst h
         first
           | exact .intAdd
           | exact .intSub
           | exact .intMul
           | exact .intDiv
           | exact .strAdd
           | exact .intLt
           | exact .intLe
           | exact .intGt
           | exact .intGe
           | exact .intToS
           | exact .intZeroP
           | exact .strLength
           | exact .notBool)
      | simp at h

mutual

theorem chk_sound : ∀ {e : Expr} {τ : Ty}, chk e = some τ → Judge e τ := by
  intro e τ h
  unfold chk at h
  -- One `split` per arm of `chk`'s match, in the order they are written there: the
  -- seven literals, the primitive `send`, then the `none` catch-all.
  split at h
  · injection h with h; subst h; exact .intLit
  · injection h with h; subst h; exact .fltLit
  · injection h with h; subst h; exact .strLit
  · injection h with h; subst h; exact .symLit
  · injection h with h; subst h; exact .truLit
  · injection h with h; subst h; exact .flsLit
  · injection h with h; subst h; exact .nilLit
  · -- `send recv m args` with no block: the receiver, the arguments and the primitive
    -- table all agreed, so rebuild `.prim` from the two recursive calls. Any other
    -- route through this arm produced `none`, contradicting `h`.
    rename_i recv m args
    split at h
    · rename_i σ argTys hrecv hargs
      exact .prim (chk_sound hrecv) (chkAll_sound hargs) (primSig?_sound h)
    · exact absurd h (by simp)
  · exact absurd h (by simp)

theorem chkAll_sound :
    ∀ {es : List Expr} {τs : List Ty}, chkAll es = some τs → JudgeAll es τs := by
  intro es τs h
  unfold chkAll at h
  split at h
  · injection h with h; subst h; exact .nil
  · split at h
    · rename_i τ τs' hτ hτs
      injection h with h; subst h
      exact .cons (chk_sound hτ) (chkAll_sound hτs)
    · exact absurd h (by simp)

end

/-- The form the runner cares about: a `true` verdict means *some* type is derivable for
the whole program. -/
theorem validate_sound_syntactic {p : Expr} (h : validate p = true) :
    ∃ τ, Judge p τ := by
  unfold validate at h
  cases hc : chk p with
  | none => simp [hc] at h
  | some τ => exact ⟨τ, chk_sound hc⟩

#print axioms chk_sound
#print axioms validate_sound_syntactic

end Ratchet
