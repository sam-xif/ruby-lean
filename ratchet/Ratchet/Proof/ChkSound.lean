import Ratchet.Validate

/-!
# `chk` only ever answers with a real derivation

The single theorem that makes `Ratchet/Validate.lean`'s `Bool` worth reading:

  `chk_sound : chk fuel D Δ Γ e = some (τ, Γ') → Judge D Δ Γ e τ Γ'`

i.e. the executable checker never certifies anything the hand-authored judgment
(`Ratchet/Judge.lean`) does not derive. This is *not* the semantic soundness theorem —
that one (`validate p = true → ∀ r, Reachable p r → ¬ typeStuck r`) needs the
semantics in the statement and is still future work (`AGENTS.md` §What is deliberately
not built). What this gives is the reduction: trusting `validate` on the covered fragment now
requires trusting **only** the constructors of `Judge`/`PrimSig`, each of which is a
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
           | exact .notBool
           | exact .arrayIndex
           | exact .hashIndex)
      | simp at h

/-- `bareNameError?` never admits a name `BareNameError` does not. -/
theorem bareNameError?_sound {m : String} (h : bareNameError? m = true) :
    BareNameError m := by
  by_cases hm : m = "x"
  · subst hm; exact .x
  · exact absurd h (by simp [bareNameError?, hm])

mutual

theorem chk_sound : ∀ {fuel : Nat} {D : DefTable} {Δ : AsmTable} {Γ : Env} {e : Expr}
    {τ : Ty} {Γ' : Env},
    chk fuel D Δ Γ e = some (τ, Γ') → Judge D Δ Γ e τ Γ' := by
  intro fuel D Δ Γ e τ Γ' h
  unfold chk at h
  -- One `split` per arm of `chk`'s match, in the order they are written there: the
  -- out-of-fuel arm, the seven literals, `var`, `vasgn`, `seq`, the two `if'`s, `array`,
  -- `hash`, `vcall`, `def'`, the implicit-self call, the primitive `send`, then the `none`
  -- catch-all. Note that fuel never appears in a conclusion: it is spent by the recursive
  -- calls and is invisible to the judgment (see `Validate.lean` §Fuel).
  split at h
  · exact absurd h (by simp)
  · injection h with h; injection h with h h'; subst h; subst h'; exact .intLit
  · injection h with h; injection h with h h'; subst h; subst h'; exact .fltLit
  · injection h with h; injection h with h h'; subst h; subst h'; exact .strLit
  · injection h with h; injection h with h h'; subst h; subst h'; exact .symLit
  · injection h with h; injection h with h h'; subst h; subst h'; exact .truLit
  · injection h with h; injection h with h h'; subst h; subst h'; exact .flsLit
  · injection h with h; injection h with h h'; subst h; subst h'; exact .nilLit
  · -- `var lvar x`: the environment had a type for `x`.
    split at h
    · rename_i hget
      injection h with h
      injection h with h h'
      subst h; subst h'
      exact .var hget
    · exact absurd h (by simp)
  · -- `vasgn lvar x e`: the right-hand side typed, and the binding lands in the
    -- environment the right-hand side left behind.
    split at h
    · rename_i hrhs
      injection h with h
      injection h with h h'
      subst h; subst h'
      exact .vasgn (chk_sound hrhs)
    · exact absurd h (by simp)
  · exact .seq (chkSeq_sound h)
  · -- `if' c t (some e)`: condition, then-branch and else-branch all typed, and the
    -- result/environment are the joins the rule names.
    split at h
    · rename_i hc
      split at h
      · rename_i ht
        split at h
        · rename_i he
          injection h with h
          injection h with h h'
          subst h; subst h'
          exact .if' (chk_sound hc) (chk_sound ht) (chk_sound he)
        · exact absurd h (by simp)
      · exact absurd h (by simp)
    · exact absurd h (by simp)
  · -- `if' c t none`: the missing branch contributes `nil` and leaves `Γc`.
    split at h
    · rename_i hc
      split at h
      · rename_i ht
        injection h with h
        injection h with h h'
        subst h; subst h'
        exact .ifNoElse (chk_sound hc) (chk_sound ht)
      · exact absurd h (by simp)
    · exact absurd h (by simp)
  · -- `array es`: every element typed, and the literal's type is `arrayOf` of the join
    -- of what they synthesized.
    split at h
    · rename_i hes
      injection h with h
      injection h with h h'
      subst h; subst h'
      exact .arrayLit (chkAll_sound hes)
    · exact absurd h (by simp)
  · -- `hash pairs`: every key and value typed; their types do not appear in the result.
    split at h
    · rename_i hps
      injection h with h
      injection h with h h'
      subst h; subst h'
      exact .hashLit (chkPairs_sound hps)
    · exact absurd h (by simp)
  · -- `vcall m`: nothing may have defined the name, *and* it must be a known
    -- `BareNameError` row.
    split at h
    · exact absurd h (by simp)
    · rename_i hdef
      split at h
      · rename_i hbare
        injection h with h
        injection h with h h'
        subst h; subst h'
        exact .bareName (bareNameError?_sound hbare) hdef
      · exact absurd h (by simp)
  · -- `def' n ps body`: unconditional, and the body is not looked at (see `Judge.defStmt`).
    injection h with h; injection h with h h'; subst h; subst h'; exact .defStmt
  · -- `send none m args`: strictness, then the assumption table, then the def table.
    split at h
    · rename_i hargs
      split at h
      · -- a non-returning argument: the call never dispatches
        rename_i hnever
        injection h with h
        injection h with h h'
        subst h; subst h'
        exact .callNever (chkAll_sound hargs) (by simpa using hnever)
      · split at h
        · -- the instantiation is assumed
          rename_i _ hasm
          injection h with h
          injection h with h h'
          subst h; subst h'
          exact .callAsm (chkAll_sound hargs) hasm
        · split at h
          · rename_i _ _ hdef
            split at h
            · rename_i hpar
              -- Pass A's result `ρ₀` is bound here but its derivation is never used: the
              -- hint is untrusted by construction, and this is where that is visible in
              -- the proof rather than only in prose.
              split at h
              · split at h
                · -- Pass B: the candidate reproduced itself, so its derivation *is* the
                  -- premise `Judge.callDef` asks for.
                  rename_i _ _ _ _ hpassB
                  split at h
                  · rename_i heq
                    injection h with h
                    injection h with h h'
                    subst h; subst h'
                    exact .callDef (chkAll_sound hargs) hdef hpar
                      (by subst heq; exact chk_sound hpassB)
                  · exact absurd h (by simp)
                · exact absurd h (by simp)
              · exact absurd h (by simp)
            · exact absurd h (by simp)
          · exact absurd h (by simp)
    · exact absurd h (by simp)
  · -- `send (some recv) m args` with no block: strictness on the receiver, then on the
    -- arguments, then the primitive table.
    split at h
    · rename_i hrecv
      split at h
      · rename_i hargs
        split at h
        · -- receiver never returns
          rename_i hnever
          injection h with h
          injection h with h h'
          subst h; subst h'
          exact .primNever (chk_sound hrecv) (chkAll_sound hargs)
            (.inl hnever)
        · split at h
          · -- some argument never returns
            rename_i _ hnever
            injection h with h
            injection h with h h'
            subst h; subst h'
            exact .primNever (chk_sound hrecv) (chkAll_sound hargs)
              (.inr hnever)
          · split at h
            · rename_i _ _ hsig
              injection h with h
              injection h with h h'
              subst h; subst h'
              exact .prim (chk_sound hrecv) (chkAll_sound hargs) (primSig?_sound hsig)
            · exact absurd h (by simp)
      · exact absurd h (by simp)
    · exact absurd h (by simp)
  · exact absurd h (by simp)

theorem chkAll_sound : ∀ {fuel : Nat} {D : DefTable} {Δ : AsmTable} {Γ : Env}
    {es : List Expr} {τs : List Ty} {Γ' : Env},
    chkAll fuel D Δ Γ es = some (τs, Γ') → JudgeAll D Δ Γ es τs Γ' := by
  intro fuel D Δ Γ es τs Γ' h
  unfold chkAll at h
  split at h
  · exact absurd h (by simp)
  · injection h with h; injection h with h h'; subst h; subst h'; exact .nil
  · split at h
    · rename_i hhd
      split at h
      · rename_i htl
        injection h with h
        injection h with h h'
        subst h; subst h'
        exact .cons (chk_sound hhd) (chkAll_sound htl)
      · exact absurd h (by simp)
    · exact absurd h (by simp)

theorem chkPairs_sound : ∀ {fuel : Nat} {D : DefTable} {Δ : AsmTable} {Γ : Env}
    {ps : List (Expr × Expr)} {Γ' : Env},
    chkPairs fuel D Δ Γ ps = some Γ' → JudgePairs D Δ Γ ps Γ' := by
  intro fuel D Δ Γ ps Γ' h
  unfold chkPairs at h
  split at h
  · exact absurd h (by simp)
  · injection h with h; subst h; exact .nil
  · split at h
    · rename_i hk
      split at h
      · rename_i hv
        exact .cons (chk_sound hk) (chk_sound hv) (chkPairs_sound h)
      · exact absurd h (by simp)
    · exact absurd h (by simp)

theorem chkSeq_sound : ∀ {fuel : Nat} {D : DefTable} {Δ : AsmTable} {Γ : Env}
    {es : List Expr} {τ : Ty} {Γ' : Env},
    chkSeq fuel D Δ Γ es = some (τ, Γ') → JudgeSeq D Δ Γ es τ Γ' := by
  intro fuel D Δ Γ es τ Γ' h
  unfold chkSeq at h
  split at h
  · exact absurd h (by simp)
  · exact absurd h (by simp)
  · exact .last (chk_sound h)
  · split at h
    · rename_i hhd
      exact .cons (chk_sound hhd) (chkSeq_sound h)
    · exact absurd h (by simp)

end

/-- The form the runner cares about: a `true` verdict means *some* type is derivable for
the whole program, from the empty environment, with **nothing defined and nothing
assumed**. The empty `Δ` is what makes this an unconditional statement rather than one
relative to a table of assumptions — see `AsmTable`. -/
theorem validate_sound_syntactic {p : Expr} (h : validate p = true) :
    ∃ τ Γ', Judge [] [] [] p τ Γ' := by
  unfold validate at h
  cases hc : chk fuelDefault [] [] [] p with
  | none => simp [hc] at h
  | some r => exact ⟨r.1, r.2, chk_sound (by simpa using hc)⟩

#print axioms primSig?_sound
#print axioms chk_sound
#print axioms chkAll_sound
#print axioms chkPairs_sound
#print axioms chkSeq_sound
#print axioms validate_sound_syntactic

end Ratchet
