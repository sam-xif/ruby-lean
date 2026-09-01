import Ratchet.Validate

/-!
# `chk` only ever answers with a real derivation

The single theorem that makes `Ratchet/Validate.lean`'s `Bool` worth reading:

  `chk_sound : chk fuel κ Γ I e = some (τ, Γ', I') → Judge κ Γ I e τ Γ' I'`

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

theorem chk_sound : ∀ {fuel : Nat} {κ : Ctx} {Γ : Env} {I : Ty} {e : Expr}
    {τ : Ty} {Γ' : Env} {I' : Ty},
    chk fuel κ Γ I e = some (τ, Γ', I') → Judge κ Γ I e τ Γ' I' := by
  intro fuel κ Γ I e τ Γ' I' h
  unfold chk at h
  -- One `split` per arm of `chk`'s match, in the order they are written there: the
  -- out-of-fuel arm, the seven literals, the two `var` kinds, the two `vasgn` kinds,
  -- `seq`, the two `if'`s, `array`, `hash`, `vcall`, `self'`, `const`, `def'`, `class'`,
  -- the implicit-self call, the explicit-receiver send, then the `none` catch-all. Note
  -- that fuel never appears in a conclusion: it is spent by the recursive calls and is
  -- invisible to the judgment (see `Validate.lean` §Fuel).
  split at h
  · exact absurd h (by simp)
  · injection h with h; injection h with h h'; injection h' with h' h''
    subst h; subst h'; subst h''; exact .intLit
  · injection h with h; injection h with h h'; injection h' with h' h''
    subst h; subst h'; subst h''; exact .fltLit
  · injection h with h; injection h with h h'; injection h' with h' h''
    subst h; subst h'; subst h''; exact .strLit
  · injection h with h; injection h with h h'; injection h' with h' h''
    subst h; subst h'; subst h''; exact .symLit
  · injection h with h; injection h with h h'; injection h' with h' h''
    subst h; subst h'; subst h''; exact .truLit
  · injection h with h; injection h with h h'; injection h' with h' h''
    subst h; subst h'; subst h''; exact .flsLit
  · injection h with h; injection h with h h'; injection h' with h' h''
    subst h; subst h'; subst h''; exact .nilLit
  · -- `var lvar x`: the environment had a type for `x`.
    split at h
    · rename_i hget
      injection h with h
      injection h with h h'; injection h' with h' h''
      subst h; subst h'; subst h''
      exact .var hget
    · exact absurd h (by simp)
  · -- `var ivar x`: unconditional, defaulting to `nil` (see `Judge.ivarRead`).
    injection h with h
    injection h with h h'; injection h' with h' h''
    subst h; subst h'; subst h''; exact .ivarRead
  · -- `vasgn lvar x e`: the right-hand side typed, and the binding lands in the
    -- environment the right-hand side left behind.
    split at h
    · rename_i hrhs
      injection h with h
      injection h with h h'; injection h' with h' h''
      subst h; subst h'; subst h''
      exact .vasgn (chk_sound hrhs)
    · exact absurd h (by simp)
  · -- `vasgn ivar x e`: the same, but the effect lands on the spine.
    split at h
    · rename_i hrhs
      injection h with h
      injection h with h h'; injection h' with h' h''
      subst h; subst h'; subst h''
      exact .ivarAsgn (chk_sound hrhs)
    · exact absurd h (by simp)
  · exact .seq (chkSeq_sound h)
  · -- `if' c t (some e)`: condition, then-branch and else-branch all typed, the two
    -- branches agreed on the spine, and the result/locals are the joins the rule names.
    split at h
    · rename_i hc
      split at h
      · rename_i ht
        split at h
        · rename_i he
          split at h
          · rename_i hI
            injection h with h
            injection h with h h'; injection h' with h' h''
            subst h; subst h'; subst h''
            exact .if' (chk_sound hc) (chk_sound ht) (chk_sound he) hI
          · exact absurd h (by simp)
        · exact absurd h (by simp)
      · exact absurd h (by simp)
    · exact absurd h (by simp)
  · -- `if' c t none`: the missing branch contributes `nil` and touches nothing.
    split at h
    · rename_i hc
      split at h
      · rename_i ht
        split at h
        · rename_i hI
          injection h with h
          injection h with h h'; injection h' with h' h''
          subst h; subst h'; subst h''
          exact .ifNoElse (chk_sound hc) (chk_sound ht) hI
        · exact absurd h (by simp)
      · exact absurd h (by simp)
    · exact absurd h (by simp)
  · -- `array es`: every element typed, and the literal's type is `arrayOf` of the join
    -- of what they synthesized.
    split at h
    · rename_i hes
      injection h with h
      injection h with h h'; injection h' with h' h''
      subst h; subst h'; subst h''
      exact .arrayLit (chkAll_sound hes)
    · exact absurd h (by simp)
  · -- `hash pairs`: every key and value typed; their types do not appear in the result.
    split at h
    · rename_i hps
      injection h with h
      injection h with h h'; injection h' with h' h''
      subst h; subst h'; subst h''
      exact .hashLit (chkPairs_sound hps)
    · exact absurd h (by simp)
  · -- `vcall m`: implicit-self dispatch inside a method body, or the `BareNameError`
    -- table at top level. The two are disjoint by construction.
    split at h
    · -- `selfTy = some (.inst n Iself)`
      rename_i hself
      split at h
      · rename_i hmeth
        split at h
        · rename_i hpar
          split at h
          · rename_i hbody
            split at h
            · rename_i hI
              injection h with h
              injection h with h h'; injection h' with h' h''
              subst h; subst h'; subst h''
              exact .selfCall hself hmeth hpar (by subst hI; exact chk_sound hbody)
            · exact absurd h (by simp)
          · exact absurd h (by simp)
        · exact absurd h (by simp)
      · exact absurd h (by simp)
    · -- `selfTy = some (.clsOf n)`: the bare name goes to the singleton table.
      rename_i hself
      split at h
      · rename_i hsm
        split at h
        · rename_i hpar
          split at h
          · rename_i hbody
            split at h
            · rename_i hI
              injection h with h
              injection h with h h'; injection h' with h' h''
              subst h; subst h'; subst h''
              exact .selfSCall hself hsm hpar (by subst hI; exact chk_sound hbody)
            · exact absurd h (by simp)
          · exact absurd h (by simp)
        · exact absurd h (by simp)
      · exact absurd h (by simp)
    · exact absurd h (by simp)
    · -- `selfTy = none`
      rename_i hself
      split at h
      · exact absurd h (by simp)
      · rename_i hdef
        split at h
        · rename_i hbare
          injection h with h
          injection h with h h'; injection h' with h' h''
          subst h; subst h'; subst h''
          exact .bareName (bareNameError?_sound hbare) hdef hself
        · exact absurd h (by simp)
  · -- `self'`: only where the context supplies a type.
    split at h
    · rename_i hself
      injection h with h
      injection h with h h'; injection h' with h' h''
      subst h; subst h'; subst h''
      exact .selfExpr hself
    · exact absurd h (by simp)
  · -- `const n`: only a declared class.
    split at h
    · rename_i hcls
      injection h with h
      injection h with h h'; injection h' with h' h''
      subst h; subst h'; subst h''
      exact .constCls hcls
    · exact absurd h (by simp)
  · -- `def' n ps body`: unconditional, and the body is not looked at (see `Judge.defStmt`).
    injection h with h
    injection h with h h'; injection h' with h' h''
    subst h; subst h'; subst h''; exact .defStmt
  · -- `module' n body`: as `class'`, and the entry it produces differs only by the module
    -- flag that stops `M.new` (see `Cls.isModule`).
    split at h
    · rename_i hms
      injection h with h
      injection h with h h'; injection h' with h' h''
      subst h; subst h'; subst h''
      exact .moduleStmt hms
    · exact absurd h (by simp)
  · -- `class' n sup body`: only a body this checker can read into the class table.
    split at h
    · rename_i hms
      injection h with h
      injection h with h h'; injection h' with h' h''
      subst h; subst h'; subst h''
      exact .classStmt hms
    · exact absurd h (by simp)
  · -- `send none m [] (some (.block ps [] body))`: a `lambda`/`proc` literal.
    split at h
    · rename_i hname
      split at h
      · rename_i hself
        split at h
        · rename_i hidx
          injection h with h
          injection h with h h'; injection h' with h' h''
          subst h; subst h'; subst h''
          exact .lambdaLit (by
            rcases (by simpa using hname : _ = "lambda" ∨ _ = "proc") with h | h
            · exact .inl h
            · exact .inr h) hself hidx
        · exact absurd h (by simp)
      · exact absurd h (by simp)
    · exact absurd h (by simp)
  · -- `send none m args`: strictness, then the assumption table, then the def table.
    split at h
    · rename_i hargs
      split at h
      · -- a non-returning argument: the call never dispatches
        rename_i hnever
        injection h with h
        injection h with h h'; injection h' with h' h''
        subst h; subst h'; subst h''
        exact .callNever (chkAll_sound hargs) hnever
      · split at h
        · -- the instantiation is assumed
          rename_i _ hasm
          injection h with h
          injection h with h h'; injection h' with h' h''
          subst h; subst h'; subst h''
          exact .callAsm (chkAll_sound hargs) hasm
        · split at h
          · rename_i _ _ hdef
            split at h
            · rename_i hpar
              -- Pass A's result is bound here but its derivation is never used: the hint
              -- is untrusted by construction, and this is where that is visible in the
              -- proof rather than only in prose.
              split at h
              · split at h
                · -- Pass B: the candidate reproduced itself, so its derivation *is* the
                  -- premise `Judge.callDef` asks for.
                  rename_i _ _ _ _ hpassB
                  split at h
                  · rename_i heq
                    split at h
                    · rename_i hI
                      injection h with h
                      injection h with h h'; injection h' with h' h''
                      subst h; subst h'; subst h''
                      exact .callDef (chkAll_sound hargs) hdef hpar
                        (by subst heq; subst hI; exact chk_sound hpassB)
                    · exact absurd h (by simp)
                  · exact absurd h (by simp)
                · exact absurd h (by simp)
              · exact absurd h (by simp)
            · exact absurd h (by simp)
          · -- the name is not a top-level method: the last route is a bare `new` inside a
            -- singleton method, where `self` is a class object.
            split at h
            · rename_i hself
              split at h
              · rename_i hnew
                split at h
                · rename_i hinit
                  split at h
                  · rename_i hpar
                    split at h
                    · rename_i hbody
                      injection h with h
                      injection h with h h'; injection h' with h' h''
                      subst h; subst h'; subst h''
                      exact hnew ▸ .selfNew hself (chkAll_sound hargs) hinit hpar
                        (chk_sound hbody)
                    · exact absurd h (by simp)
                  · exact absurd h (by simp)
                · exact absurd h (by simp)
              · exact absurd h (by simp)
            · exact absurd h (by simp)
            · exact absurd h (by simp)
    · exact absurd h (by simp)
  · -- `send (some recv) m args` with no block: strictness on the receiver, then on the
    -- arguments, then tier 7's dispatch keyed on the receiver's type, then `PrimSig`.
    split at h
    · rename_i hrecv
      split at h
      · rename_i hargs
        split at h
        · -- receiver never returns
          rename_i hnever
          injection h with h
          injection h with h h'; injection h' with h' h''
          subst h; subst h'; subst h''
          exact .primNever (chk_sound hrecv) (chkAll_sound hargs) (.inl hnever)
        · split at h
          · -- some argument never returns
            rename_i _ hnever
            injection h with h
            injection h with h h'; injection h' with h' h''
            subst h; subst h'; subst h''
            exact .primNever (chk_sound hrecv) (chkAll_sound hargs) (.inr hnever)
          · split at h
            · -- the receiver is a class object: a singleton method first, then `new`
              split at h
              · rename_i hsm
                split at h
                · rename_i hpar
                  split at h
                  · rename_i hbody
                    split at h
                    · rename_i hI
                      injection h with h
                      injection h with h h'; injection h' with h' h''
                      subst h; subst h'; subst h''
                      exact .callSMethod (chk_sound hrecv) (chkAll_sound hargs) hsm hpar
                        (by subst hI; exact chk_sound hbody)
                    · exact absurd h (by simp)
                  · exact absurd h (by simp)
                · exact absurd h (by simp)
              · split at h
                · rename_i hnew
                  split at h
                  · rename_i hinit
                    split at h
                    · rename_i hpar
                      split at h
                      · rename_i hbody
                        injection h with h
                        injection h with h h'; injection h' with h' h''
                        subst h; subst h'; subst h''
                        exact hnew ▸ .newInst (chk_sound hrecv) (chkAll_sound hargs)
                          hinit hpar (chk_sound hbody)
                      · exact absurd h (by simp)
                    · exact absurd h (by simp)
                  · rename_i hinit
                    split at h
                    · rename_i hcls
                      split at h
                      · rename_i hzero
                        injection h with h
                        injection h with h h'; injection h' with h' h''
                        subst h; subst h'; subst h''
                        exact hnew ▸ .newInstNoInit (chk_sound hrecv)
                          (hzero ▸ chkAll_sound hargs) hcls hinit
                      · exact absurd h (by simp)
                    · exact absurd h (by simp)
                · exact absurd h (by simp)
            · -- the receiver is a callable: check its body here (`Judge.closCall`)
              split at h
              · rename_i hname
                split at h
                · rename_i hself
                  split at h
                  · rename_i hclos
                    split at h
                    · rename_i hpar
                      split at h
                      · rename_i hbody
                        split at h
                        · rename_i hI
                          injection h with h
                          injection h with h h'; injection h' with h' h''
                          subst h; subst h'; subst h''
                          exact .closCall (by
                            rcases (by simpa using hname : _ = "call" ∨ _ = "[]") with
                              h | h
                            · exact .inl h
                            · exact .inr h) hself (chk_sound hrecv)
                            (chkAll_sound hargs) hclos hpar
                            (by subst hI; exact chk_sound hbody)
                        · exact absurd h (by simp)
                      · exact absurd h (by simp)
                    · exact absurd h (by simp)
                  · exact absurd h (by simp)
                · exact absurd h (by simp)
              · exact absurd h (by simp)
            · -- the receiver is an instance: dispatch up the chain from its class
              split at h
              · rename_i hmeth
                split at h
                · rename_i hpar
                  split at h
                  · rename_i hbody
                    split at h
                    · rename_i hI
                      injection h with h
                      injection h with h h'; injection h' with h' h''
                      subst h; subst h'; subst h''
                      exact .callMethod (chk_sound hrecv) (chkAll_sound hargs)
                        hmeth hpar (by subst hI; exact chk_sound hbody)
                    · exact absurd h (by simp)
                  · exact absurd h (by simp)
                · exact absurd h (by simp)
              · exact absurd h (by simp)
            · -- anything else: the primitive table
              split at h
              · rename_i hsig
                injection h with h
                injection h with h h'; injection h' with h' h''
                subst h; subst h'; subst h''
                exact .prim (chk_sound hrecv) (chkAll_sound hargs) (primSig?_sound hsig)
              · exact absurd h (by simp)
      · exact absurd h (by simp)
    · exact absurd h (by simp)
  · -- `super' args none`: the arguments, then the walk from the *definition site*.
    split at h
    · rename_i hargs
      split at h
      · rename_i hfr
        split at h
        · rename_i hcls
          split at h
          · rename_i hsup
            split at h
            · rename_i hmeth
              split at h
              · rename_i hpar
                split at h
                · rename_i hbody
                  injection h with h
                  injection h with h h'; injection h' with h' h''
                  subst h; subst h'; subst h''
                  exact .superCall (chkAll_sound hargs) hfr hcls hsup hmeth hpar
                    (chk_sound hbody)
                · exact absurd h (by simp)
              · exact absurd h (by simp)
            · exact absurd h (by simp)
          · exact absurd h (by simp)
        · exact absurd h (by simp)
      · exact absurd h (by simp)
    · exact absurd h (by simp)
  · exact absurd h (by simp)

theorem chkAll_sound : ∀ {fuel : Nat} {κ : Ctx} {Γ : Env} {I : Ty}
    {es : List Expr} {τs : List Ty} {Γ' : Env} {I' : Ty},
    chkAll fuel κ Γ I es = some (τs, Γ', I') → JudgeAll κ Γ I es τs Γ' I' := by
  intro fuel κ Γ I es τs Γ' I' h
  unfold chkAll at h
  split at h
  · exact absurd h (by simp)
  · injection h with h; injection h with h h'; injection h' with h' h''
    subst h; subst h'; subst h''; exact .nil
  · split at h
    · rename_i hhd
      split at h
      · rename_i htl
        injection h with h
        injection h with h h'; injection h' with h' h''
        subst h; subst h'; subst h''
        exact .cons (chk_sound hhd) (chkAll_sound htl)
      · exact absurd h (by simp)
    · exact absurd h (by simp)

theorem chkPairs_sound : ∀ {fuel : Nat} {κ : Ctx} {Γ : Env} {I : Ty}
    {ps : List (Expr × Expr)} {Γ' : Env} {I' : Ty},
    chkPairs fuel κ Γ I ps = some (Γ', I') → JudgePairs κ Γ I ps Γ' I' := by
  intro fuel κ Γ I ps Γ' I' h
  unfold chkPairs at h
  split at h
  · exact absurd h (by simp)
  · injection h with h; injection h with h h'; subst h; subst h'; exact .nil
  · split at h
    · rename_i hk
      split at h
      · rename_i hv
        exact .cons (chk_sound hk) (chk_sound hv) (chkPairs_sound h)
      · exact absurd h (by simp)
    · exact absurd h (by simp)

theorem chkSeq_sound : ∀ {fuel : Nat} {κ : Ctx} {Γ : Env} {I : Ty}
    {es : List Expr} {τ : Ty} {Γ' : Env} {I' : Ty},
    chkSeq fuel κ Γ I es = some (τ, Γ', I') → JudgeSeq κ Γ I es τ Γ' I' := by
  intro fuel κ Γ I es τ Γ' I' h
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
assumed**, no `self`, and the program's own block table. The empty assumption table is what
makes this an unconditional statement rather than one relative to a table of assumptions — see
`AsmTable` and `ctx0`; `Ctx.withBlocks` is the one component that starts non-empty, and it is
derived from the program by `collectBlocks`. -/
theorem validate_sound_syntactic {p : Expr} (h : validate p = true) :
    ∃ τ Γ' I', Judge (ctx0.withBlocks p) [] .ivar0 p τ Γ' I' := by
  unfold validate at h
  cases hc : chk fuelDefault (ctx0.withBlocks p) [] .ivar0 p with
  | none => simp [hc] at h
  | some r => exact ⟨r.1, r.2.1, r.2.2, chk_sound (by simpa using hc)⟩

#print axioms primSig?_sound
#print axioms chk_sound
#print axioms chkAll_sound
#print axioms chkPairs_sound
#print axioms chkSeq_sound
#print axioms validate_sound_syntactic

end Ratchet
