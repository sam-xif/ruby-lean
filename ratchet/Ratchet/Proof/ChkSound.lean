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

-- File-level, and raised twice. Originally for `chkSeq_sound`'s guard-clause arm (see the note
-- at `chk_sound`); raised again when tiers 15 and 16 took `primSig?` from 18 rows to 33, since
-- `primSig?_sound` is one `split` over the whole table and its cost grows with it. Not a
-- soundness knob: a heartbeat limit can only turn a proof into an error.
set_option maxHeartbeats 4000000

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
      | exact .hashOf
      | exact absurd h (by simp [eqSafe?])

/-- `nilQSafe?` never admits a receiver `NilQSafe` does not. Recursive at `nilable`,
mirroring the relation's one recursive constructor. -/
theorem nilQSafe?_sound : ∀ {σ : Ty}, nilQSafe? σ = true → NilQSafe σ := by
  intro σ h
  induction σ with
  | nilable τ ih => exact .nilable (ih (by simpa [nilQSafe?] using h))
  | _ =>
    first
      | exact .int
      | exact .float
      | exact .bool
      | exact .nilT
      | exact .sym
      | exact .cls
      | exact .arrayOf
      | exact .hashOf
      | exact absurd h (by simp [nilQSafe?])

/-- `excCls?` never admits a name `ExcCls` does not (tier 16b). Row for row, exactly like
`builtinCls?_sound` -- and the list's *completeness* is a coverage condition rather than a
soundness one: a missing name makes a `raise` untypeable, never mistyped. -/
theorem excCls?_sound {n : String} (h : excCls? n = true) : ExcCls n := by
  unfold excCls? at h
  split at h
  · exact .standardError
  · exact .runtimeError
  · exact .argumentError
  · exact .typeError
  · exact .nameError
  · exact .noMethodError
  · exact .zeroDivisionError
  · exact .indexError
  · exact .keyError
  · exact .rangeError
  · exact .ioError
  · exact .frozenError
  · exact .notImplementedError
  · exact absurd h (by simp)

/-- The `String` half of the table agrees with `PrimSig` row for row (tier 16b). Same shape as
`primSig?_sound`'s tail, on the half that was split out of it. -/
theorem primSigStr?_sound {m : String} {argTys : List Ty} {τ : Ty}
    (h : primSigStr? m argTys = some τ) : PrimSig (.cls "String") m argTys τ := by
  unfold primSigStr? at h
  split at h
  all_goals
    first
      | (injection h with h
         subst h
         first
           | exact .strAdd
           | exact .strLength
           | exact .strEmptyP
           | exact .strStrip
           | exact .strDowncase
           | exact .strUpcase
           | exact .strTr
           | exact .strDeletePrefix
           | exact .strStartsWith
           | exact .strSplit
           | exact .strSub
           | exact .strGsub
           | exact .strMatchP
           | exact .strMatch)
      | simp at h

/-- The `Array` half of the table agrees with `PrimSig` row for row. Unguarded rows by
`all_goals`, the three element-guarded ones and `<<` by explicit bullets in `primSigArr?`'s
order. -/
theorem primSigArr?_sound {m : String} {argTys : List Ty} {τ ρ : Ty}
    (h : primSigArr? m argTys τ = some ρ) : PrimSig (.arrayOf τ) m argTys ρ := by
  unfold primSigArr? at h
  split at h
  · injection h with h; subst h; exact .arrayLength
  · injection h with h; subst h; exact .arrayIndex
  · injection h with h; subst h; exact .arrayEmptyP
  · injection h with h; subst h; exact .arrayFirst
  · injection h with h; subst h; exact .arrayLast
  · injection h with h; subst h; exact .arrayCompact
  · injection h with h; subst h; exact .arrayJoin
  · -- `<<`, whose guard is the *equality* that makes `arrayOf` invariant
    split at h
    · rename_i heq; subst heq; injection h with h; subst h; exact .arrayPush
    · exact absurd h (by simp)
  · -- `include?`, guarded on the **element** type
    split at h
    · rename_i hel; injection h with h; subst h
      exact .arrayInclude (nilQSafe?_sound hel)
    · exact absurd h (by simp)
  · -- `uniq`, same guard
    split at h
    · rename_i hel; injection h with h; subst h
      exact .arrayUniq (nilQSafe?_sound hel)
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- The `Hash` half of the table agrees with `PrimSig` row for row (tier 17b). Each row is
guarded, so this is a run of two-way splits rather than an `all_goals`. -/
theorem primSigHash?_sound {m : String} {argTys : List Ty} {k v τ : Ty}
    (h : primSigHash? m argTys k v = some τ) : PrimSig (.hashOf k v) m argTys τ := by
  unfold primSigHash? at h
  split at h
  · split at h
    · rename_i hg; injection h with h; subst h; exact .hashKeyP (nilQSafe?_sound hg)
    · exact absurd h (by simp)
  · split at h
    · rename_i hg; injection h with h; subst h; exact .hashFetch (nilQSafe?_sound hg)
    · exact absurd h (by simp)
  · split at h
    · rename_i hg; injection h with h; subst h; exact .hashFetchD (nilQSafe?_sound hg)
    · exact absurd h (by simp)
  · split at h
    · rename_i hg; injection h with h; subst h; exact .hashIndex (nilQSafe?_sound hg)
    · exact absurd h (by simp)
  · split at h
    · rename_i hg; injection h with h; subst h; exact .hashDig (nilQSafe?_sound hg)
    · exact absurd h (by simp)
  · split at h
    · rename_i hg
      injection h with h; subst h
      simp only [Bool.and_eq_true] at hg
      exact .hashDig2 (nilQSafe?_sound hg.1) (nilQSafe?_sound hg.2)
    · exact absurd h (by simp)
  · injection h with h; subst h; exact .hashLength
  · exact absurd h (by simp)

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
  · -- the guarded `nil?` row: the receiver had to pass `nilQSafe?`
    split at h
    · injection h with h
      subst h
      exact .nilQuery (nilQSafe?_sound (by assumption))
    · exact absurd h (by simp)
  · -- tier 16's guarded `===` row: `EqSafe`, exactly as `==`
    split at h
    · rename_i heq
      injection h with h
      subst h
      exact .caseEqPrim (eqSafe?_sound heq)
    · exact absurd h (by simp)
  · -- tier 13's guarded `freeze` row: the same guard, and the same predicate
    split at h
    · injection h with h
      subst h
      exact .freezeId (nilQSafe?_sound (by assumption))
    · exact absurd h (by simp)
  · -- tier 16b's guarded `message` row: the receiver's *name* has to be an exception class
    split at h
    · rename_i hexc
      injection h with h
      subst h
      exact .excMessage (excCls?_sound hexc)
    · exact absurd h (by simp)

  · -- tier 16b: everything else on a `String` receiver, delegated
    exact primSigStr?_sound h
  · -- tier 17b: everything on a `Hash` receiver, delegated
    exact primSigHash?_sound h
  · -- tiers 5/14b/17a: everything on an `Array` receiver, delegated
    exact primSigArr?_sound h
  all_goals
    first
      | (injection h with h
         subst h
         first
           | exact .intAdd
           | exact .intSub
           | exact .intMul
           | exact .intDiv
           | exact .intLt
           | exact .intLe
           | exact .intGt
           | exact .intGe
           | exact .intToS
           | exact .intZeroP
           | exact .intAsString
           | exact .symToS
           | exact .notBool
           | exact .intSpaceship)
      | simp at h

/-- `builtinCls?` never admits a name `BuiltinCls` does not. Row for row; `decide` on the
string equalities the match compiles to. -/
theorem builtinCls?_sound {n : String} (h : builtinCls? n = true) : BuiltinCls n := by
  unfold builtinCls? at h
  -- `split` gives one goal per name in the pattern alternation, with the name substituted
  -- into the goal, plus the catch-all (which contradicts `h`).
  split at h
  · exact .integer
  · exact .float
  · exact .string
  · exact .symbol
  · exact .nilClass
  · exact .trueClass
  · exact .falseClass
  · exact .array
  · exact .hash
  · exact absurd h (by simp)

/-- `comparable?` never admits a type `Comparable` does not. -/
theorem comparable?_sound {ρ : Ty} (h : comparable? ρ = true) : Comparable ρ := by
  unfold comparable? at h
  split at h
  · exact .int
  · exact .float
  · exact .str
  · exact absurd h (by simp)

/-- **The two halves of the iterator table only ever agree with `IterSig`.**

`iterParams?` and `iterResult?` are separate functions because `chk` needs the first before it
can compute the second's `ρ` argument (see `IterSig`), and this is the lemma that they are two
views of one relation rather than two independent tables that could drift. Proved by exhausting
`iterParams?`'s rows: each row fixes the method name and the argument list, at which point
`iterResult?` reduces. -/
theorem iterSig?_sound {m : String} {τ : Ty} {as βs : List Ty} {ρ res : Ty}
    (hp : iterParams? m τ as = some βs) (hr : iterResult? m τ as ρ = some res) :
    IterSig m τ as βs ρ res := by
  unfold iterParams? at hp
  split at hp
  · injection hp with hp; subst hp
    simp [iterResult?] at hr; subst hr; exact .each
  · injection hp with hp; subst hp
    simp [iterResult?] at hr; subst hr; exact .map
  · injection hp with hp; subst hp
    simp [iterResult?] at hr; subst hr; exact .select
  · -- `sort_by`: `simp` has already reduced the guarded row to its two conjuncts
    injection hp with hp; subst hp
    simp [iterResult?] at hr
    obtain ⟨hcmp, hres⟩ := hr
    subst hres
    exact .sortBy (comparable?_sound hcmp)
  · -- `inject`: **two rows** since tier 14b, and which one applies is decided by the
    -- receiver's element type rather than by anything in `iterParams?` -- hence the `cases`.
    -- `.never` is the provably-empty receiver (`IterSig.injectEmpty`), where `ρ` is
    -- unconstrained; everywhere else the first conjunct *is* the accumulator fixed point.
    injection hp with hp; subst hp
    cases τ with
    | never => simp [iterResult?] at hr; subst hr; exact .injectEmpty
    | _ =>
      simp [iterResult?] at hr
      obtain ⟨hfix, hres⟩ := hr
      subst hfix; subst hres
      exact .inject
  -- ### Tier 17's iterators, in `iterParams?`'s order
  · injection hp with hp; subst hp
    simp [iterResult?] at hr; subst hr; exact .anyP
  · injection hp with hp; subst hp
    simp [iterResult?] at hr; subst hr; exact .allP
  · injection hp with hp; subst hp
    simp [iterResult?] at hr; subst hr; exact .findFirst
  · injection hp with hp; subst hp
    simp [iterResult?] at hr; subst hr; exact .filterMap
  · -- `flat_map`: the block's return type has to *be* an array, which makes this the one row
    -- whose applicability is decided by `ρ` rather than by the receiver or the arguments.
    injection hp with hp; subst hp
    cases ρ with
    | arrayOf σ => simp [iterResult?] at hr; subst hr; exact .flatMap
    | _ => simp [iterResult?] at hr
  · injection hp with hp; subst hp
    simp [iterResult?] at hr; subst hr; exact .eachWithIndex
  · exact absurd hp (by simp)

/-- **`narrowCond?` only ever recognizes a condition `NarrowCond` does.**

Added at clink 26, and it closes a gap that had been open since clink 13: `NarrowCond` was
written as the *specification* of the recognizer — "evaluating this condition performs this test
on this variable, and evaluating it cannot invalidate the answer" — and nothing tied
`narrowCond?` to it. So the relation was decorative, and the one human-checkable statement of
why each refinement is licensed was not actually load-bearing. It is now.

Note what this theorem does **not** say: that the refinement *functions*
(`truthyTy`/`isATy`/…) are right about Ruby. That is a claim about the semantics, checked the
way every other such claim on this ladder is — by `CheckRungs.lean`'s controls, executed. What
it does say is that the checker never applies a refinement to a condition whose shape the
judgment has not licensed. -/
theorem narrowCond?_sound {c : Expr} {k : VarKind} {x : String} {nk : NarrowKind}
    {sides : NarrowSides} (h : narrowCond? c = some (k, x, nk, sides)) :
    NarrowCond c k x nk sides := by
  unfold narrowCond? at h
  split at h
  · -- the `&&` shape: the guard is a chain of `&&`s equating the four `VarKind`s and the three
    -- occurrences of the temporary, plus `noLocalAsgn` on the right conjunct.
    split at h
    · rename_i hg
      simp only [Bool.and_eq_true, beq_iff_eq] at hg
      obtain ⟨⟨⟨⟨⟨e1, e2⟩, e3⟩, e4⟩, e5⟩, hno⟩ := hg
      subst e1; subst e2; subst e3; subst e4; subst e5
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hk, hx, hnk, hs⟩ := h
      subst hk; subst hx; subst hnk; subst hs
      exact .andGuard hno
    · exact absurd h (by simp)
  all_goals
    first
      | (simp only [Option.some.injEq, Prod.mk.injEq] at h
         obtain ⟨hk, hx, hnk, hs⟩ := h
         subst hk; subst hx; subst hnk; subst hs
         first
           | exact .bareVar
           | exact .nilQuery
           | exact .isAQuery
           | exact .caseEqQuery)
      | simp at h

/-! ## `constLitTy?` is not a trusted table (tiers 13b and 14a)

`constLitTy?` reads a type off an expression's syntax, and it is used in two places where
nothing in the derivation discharges it: `Ctx.afterStmt` (a class body's constants) and
`paramEnv` (an optional parameter's default). The theorem below is what makes that legitimate
rather than a trusted row — it says an expression `constLitTy?` types **really has that type,
in any context whatsoever**, with no premise to supply:

  `constLitTy? e = some τ → Judge κ Γ I e τ Γ I`

Note the shape: `κ`, `Γ` and `I` are universally quantified and unchanged across the
conclusion. That is a strong statement and it is exactly why the function is restricted to
literals — nothing it accepts reads a variable, dispatches a method the program could
redefine, or leaves any state behind. It is also why `Judge.classStmt`'s `JudgeConsts` premise
is now redundant *as an obligation* (it is always satisfiable) while remaining useful as a
statement of intent: the premise says in the specification what this theorem proves.

The `NilQSafe` companion is needed for the `.freeze` row, whose `PrimSig.freezeId` carries
that guard. -/
theorem constLitTy?_nilQSafe : ∀ {e : Expr} {τ : Ty}, constLitTy? e = some τ → NilQSafe τ := by
  intro e τ h
  unfold constLitTy? at h
  split at h <;>
    first
      | (injection h with h; subst h
         first
           | exact .int | exact .float | exact .sym | exact .bool | exact .nilT
           | exact .cls | exact .arrayOf | exact .hashOf)
      | (split at h
         · injection h with h; subst h; first | exact .hashOf | exact .cls
         · exact absurd h (by simp))
      | (rename_i es; cases hes : constLitTys? es with
         | none => simp [hes] at h
         | some τs => simp [hes] at h; subst h; exact .arrayOf)
      | exact constLitTy?_nilQSafe h
      | exact absurd h (by simp)

mutual

theorem constLitTy?_sound : ∀ {e : Expr} {τ : Ty} {κ : Ctx} {Γ : Env} {I : Ty},
    constLitTy? e = some τ → Judge κ Γ I e τ Γ I := by
  intro e τ κ Γ I h
  unfold constLitTy? at h
  split at h
  · injection h with h; subst h; exact .intLit
  · injection h with h; subst h; exact .fltLit
  · injection h with h; subst h; exact .strLit
  · injection h with h; subst h; exact .symLit
  · injection h with h; subst h; exact .truLit
  · injection h with h; subst h; exact .flsLit
  · injection h with h; subst h; exact .nilLit
  · -- a hash literal: the pairs' *types* are the answer now (tier 17b), not just whether they
    -- exist -- `constLitPairTys?` folds them exactly as `JudgePairs` does.
    rename_i pairs
    split at h
    · rename_i kτ vτ hp
      injection h with h; subst h
      exact .hashLit (constLitPairTys?_sound hp)
    · exact absurd h (by simp)
  · -- an array literal: every element types, so `JudgeAll` does
    rename_i es
    cases hes : constLitTys? es with
    | none => simp [hes] at h
    | some τs =>
      simp [hes] at h; subst h
      exact .arrayLit (constLitTys?_sound hes)
  · -- `.freeze`: the identity, and its `NilQSafe` guard comes from the companion theorem
    rename_i r
    exact .prim (constLitTy?_sound h) .nil (.freezeId (constLitTy?_nilQSafe h))
  · exact absurd h (by simp)

theorem constLitTys?_sound : ∀ {es : List Expr} {τs : List Ty} {κ : Ctx} {Γ : Env} {I : Ty},
    constLitTys? es = some τs → JudgeAll κ Γ I es τs Γ I := by
  intro es τs κ Γ I h
  unfold constLitTys? at h
  split at h
  · injection h with h; subst h; exact .nil
  · rename_i e es'
    split at h
    · rename_i τ ρs he hes
      injection h with h; subst h
      exact .cons (constLitTy?_sound he) (constLitTys?_sound hes)
    · exact absurd h (by simp)

theorem constLitPairTys?_sound : ∀ {ps : List (Expr × Expr)} {kτ vτ : Ty} {κ : Ctx}
    {Γ : Env} {I : Ty},
    constLitPairTys? ps = some (kτ, vτ) → JudgePairs κ Γ I ps kτ vτ Γ I := by
  intro ps kτ vτ κ Γ I h
  unfold constLitPairTys? at h
  split at h
  · injection h with h
    injection h with h h'
    subst h; subst h'; exact .nil
  · rename_i k v ps'
    split at h
    · rename_i kt vt kr vr hk hv hrest
      injection h with h
      injection h with h h'
      subst h; subst h'
      exact .cons (constLitTy?_sound hk) (constLitTy?_sound hv)
        (constLitPairTys?_sound hrest)
    · exact absurd h (by simp)

end

/-- **`splitKw?` really does split the argument list where it says** (tier 14c).

`Judge.callDefKw` states the split as `args = pos ++ [.kwargs entries]` rather than as a call to
`splitKw?`, which is the readable form for a specification; this is the bridge. Note the shape
of the recursion: `splitKw?`'s first pattern (`[.kwargs es]`) *overlaps* its second (`e :: rest`),
so the `split` has to be taken in that order, and the second case's hypothesis is about the
tail. -/
theorem splitKw?_sound : ∀ {args pos : List Expr} {es : List KwEntry},
    splitKw? args = some (pos, es) → args = pos ++ [.kwargs es] := by
  intro args pos es h
  unfold splitKw? at h
  split at h
  · rename_i es'
    injection h with h
    injection h with h h'
    subst h; subst h'; rfl
  · rename_i hd tl hne
    cases hr : splitKw? tl with
    | none => simp [hr] at h
    | some r =>
      simp [hr] at h
      obtain ⟨hp, he⟩ := h
      subst hp; subst he
      simpa using splitKw?_sound hr
  · exact absurd h (by simp)

/-- `bareNameError?` never admits a name `BareNameError` does not. -/
theorem bareNameError?_sound {m : String} (h : bareNameError? m = true) :
    BareNameError m := by
  by_cases hm : m = "x"
  · subst hm; exact .x
  · exact absurd h (by simp [bareNameError?, hm])

-- Raised from the default 200000 when tier 12's guard clause was added. The cost is
-- elaboration time in `chkSeq_sound`'s new arm and nothing else: `chkSeq`'s guard pattern
-- (`.if' c (.ret (some r)) none :: _ :: _`) *overlaps* the generic `e :: e' :: es` arm, so
-- Lean's match compiler builds a splitter that case-analyses `Expr` several levels deep, and
-- `split at h` has to push `h` through it. Not a soundness knob -- a heartbeat limit can only
-- turn a proof into an error, never the reverse, and the file still checks in a few seconds.
set_option maxHeartbeats 1000000

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
  · -- tier 15: a regexp literal, opaque (`Judge.regexpLit`)
    injection h with h; injection h with h h'; injection h' with h' h''
    subst h; subst h'; subst h''; exact .regexpLit
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
    · rename_i tb hget
      injection h with h
      injection h with h h'; injection h' with h' h''
      subst h; subst h'; subst h''
      -- Tier 12: `chk` answers `stripAlias tb`, which is `varAlias`'s payload when the binding
      -- is an alias and `tb` itself otherwise. Case on the binding to pick the rule.
      cases tb with
      | sameAs y ρ => exact .varAlias hget
      | _ => exact .var hget rfl
    · exact absurd h (by simp)
  · -- `var ivar x`: unconditional, defaulting to `nil` (see `Judge.ivarRead`).
    injection h with h
    injection h with h h'; injection h' with h' h''
    subst h; subst h'; subst h''; exact .ivarRead
  · -- tier 12: `vasgn lvar t (var lvar x)` -- the alias route, when `t` is a desugarer
    -- temporary, and otherwise the ordinary binding written out (this arm shadows the general
    -- `vasgn` arm for that one syntactic shape, so it has to answer for both).
    split at h
    · rename_i tb hget
      split at h
      · rename_i hpre
        injection h with h
        injection h with h h'; injection h' with h' h''
        subst h; subst h'; subst h''
        exact .vasgnAlias hpre hget rfl
      · -- not a temporary: `Judge.vasgn` over `Judge.var`, whose `stripAlias` is exactly what
        -- this arm computes
        injection h with h
        injection h with h h'; injection h' with h' h''
        subst h; subst h'; subst h''
        -- Not a temporary, so this is the ordinary binding -- and its value is a *read* of
        -- `x`, which is `var`/`varAlias` exactly as in the `var` arm above.
        cases tb with
        | sameAs y ρ => exact .vasgn (.varAlias hget)
        | _ => exact .vasgn (.var hget rfl)
    · exact absurd h (by simp)
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
          injection h with h
          injection h with h h'; injection h' with h' h''
          subst h; subst h'; subst h''
          exact .if' (chk_sound hc) (chk_sound ht) (chk_sound he) rfl
        · exact absurd h (by simp)
      · exact absurd h (by simp)
    · exact absurd h (by simp)
  · -- `if' c t none`: the missing branch contributes `nil` and touches nothing.
    split at h
    · rename_i hc
      split at h
      · rename_i ht
        injection h with h
        injection h with h h'; injection h' with h' h''
        subst h; subst h'; subst h''
        exact .ifNoElse (chk_sound hc) (chk_sound ht) rfl
      · exact absurd h (by simp)
    · exact absurd h (by simp)
  · -- `begin' body rescues none none` (tier 16b): the body left every type where it found it,
    -- it contains no local assignment (so there is no intermediate state a handler could see at
    -- the wrong type), and every rescue clause typed.
    split at h
    · rename_i τb Γb Ib hbody
      split at h
      · rename_i hg
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hg
        obtain ⟨⟨hΓ, hI⟩, hna⟩ := hg
        split at h
        · rename_i τr hres
          injection h with h
          injection h with h h'; injection h' with h' h''
          subst h; subst h'; subst h''
          exact .begin' (chk_sound hbody) hΓ hI hna (chkRescues_sound hres)
        · exact absurd h (by simp)
      · exact absurd h (by simp)
    · exact absurd h (by simp)
  · -- `while' c body` (tier 16): both the condition and the body left every type where they
    -- found it, which is `Judge.while'`'s two premises and the whole rule.
    split at h
    · rename_i σc Γc Ic hc
      split at h
      · rename_i hfix
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hfix
        obtain ⟨hΓc, hIc⟩ := hfix
        split at h
        · rename_i σb Γb Ib hb
          split at h
          · rename_i hfixb
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hfixb
            obtain ⟨hΓb, hIb⟩ := hfixb
            injection h with h
            injection h with h h'; injection h' with h' h''
            subst h; subst h'; subst h''
            exact .while' (chk_sound hc) hΓc hIc (chk_sound hb) hΓb hIb
          · exact absurd h (by simp)
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
    · -- `selfTy = none`: the assumption table, then a defined method, then the
      -- `BareNameError` table.
      rename_i hself
      split at h
      · rename_i hasm
        injection h with h
        injection h with h h'; injection h' with h' h''
        subst h; subst h'; subst h''
        exact .vcallAsm hself hasm
      · split at h
        · rename_i _ hdef
          split at h
          · rename_i hpar
            split at h
            · split at h
              · rename_i _ _ _ _ hpassB
                split at h
                · rename_i heq
                  split at h
                  · rename_i hI
                    injection h with h
                    injection h with h h'; injection h' with h' h''
                    subst h; subst h'; subst h''
                    exact .vcallDef hself hdef hpar
                      (by subst heq; subst hI; exact chk_sound hpassB)
                  · exact absurd h (by simp)
                · exact absurd h (by simp)
              · exact absurd h (by simp)
            · exact absurd h (by simp)
          · exact absurd h (by simp)
        · rename_i _ hdef
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
  · -- `const n`: an assigned constant (tier 13), else a declared class, else a builtin class
    -- name. Each of the three carries the *other two's* negations as premises, so the three
    -- rules are disjoint and this nest supplies each hypothesis exactly where it is bound.
    split at h
    · rename_i hcv hconst
      injection h with h
      injection h with h h'; injection h' with h' h''
      subst h; subst h'; subst h''
      exact .constEnv hconst
    · rename_i hconst
      split at h
      · rename_i hcls
        injection h with h
        injection h with h h'; injection h' with h' h''
        subst h; subst h'; subst h''
        exact .constCls hcls hconst
      · rename_i hcls
        split at h
        · -- Tier 16b: the guard is a disjunction now -- a builtin class name, or a builtin
          -- *exception* class name, which `BuiltinCls` deliberately does not list.
          rename_i hb
          injection h with h
          injection h with h h'; injection h' with h' h''
          subst h; subst h'; subst h''
          rcases (by simpa using hb : builtinCls? _ = true ∨ excCls? _ = true) with hb' | hb'
          · exact .constBuiltin (builtinCls?_sound hb') hcls hconst
          · exact .constExc (excCls?_sound hb') hcls hconst
        · exact absurd h (by simp)
  · -- `cpath (some base) n` (tiers 13c and 13e): the base typed as *some* class-or-module
    -- object, and then either the absolute key was in the constant table (`constPath`) or a
    -- nested class was declared under the qualified name (`constPathCls`).
    split at h
    · rename_i owner Γ₁ I₁ hbase
      split at h
      · rename_i τ₀ hlook
        -- Tier 13d: `private_constant` -- one more `split`, and the `false` branch is the one
        -- that can succeed.
        split at h
        · exact absurd h (by simp)
        · rename_i hpriv
          injection h with h
          injection h with h h'; injection h' with h' h''
          subst h; subst h'; subst h''
          exact .constPath (chkOwner?_sound hbase) hlook (by simpa using hpriv)
      · rename_i hlook
        split at h
        · rename_i c hcls
          injection h with h
          injection h with h h'; injection h' with h' h''
          subst h; subst h'; subst h''
          exact .constPathCls (chkOwner?_sound hbase) hcls hlook
        · exact absurd h (by simp)
    · exact absurd h (by simp)
  · -- `cpathAsgn (some (const owner)) n e` (tier 13c): the same base premise, then the
    -- right-hand side. The binding is `chkSeq`'s, as it is for `casgn`.
    split at h
    · rename_i hbase
      exact .cpathAsgn (chk_sound hbase) (chk_sound h)
    · exact absurd h (by simp)
  · -- `casgn n e` (tier 13): the right-hand side typed, and nothing else happened — the
    -- binding is `chkSeq`'s, via `Ctx.afterStmt` (see `Judge.casgn`).
    split at h
    · rename_i res hrhs
      injection h with h
      injection h with h h'; injection h' with h' h''
      subst h; subst h'; subst h''
      exact .casgn (chk_sound hrhs)
    · exact absurd h (by simp)
  · -- `def' n ps body`: unconditional, and the body is not looked at (see `Judge.defStmt`).
    injection h with h
    injection h with h h'; injection h' with h' h''
    subst h; subst h'; subst h''; exact .defStmt
  · -- `module' n body`: as `class'`, and the entry it produces differs only by the module
    -- flag that stops `M.new` (see `Cls.isModule`).
    split at h
    · rename_i hms
      split at h
      · rename_i hmix
        injection h with h
        injection h with h h'; injection h' with h' h''
        subst h; subst h'; subst h''
        -- Tier 13: the guard is a conjunction now, and `simp` splits it into `allModules`
        -- and the `constGet?`-is-`none` premise `classStmt`/`moduleStmt` grew.
        -- Tier 13: three conjuncts now -- `allModules`, the `constGet?`-is-`none` premise,
        -- and the class body's constants (`chkConsts`).
        simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hmix
        exact .moduleStmt hms hmix.1.1.1 hmix.1.1.2 (chkConsts_sound hmix.1.2)
          (chkNested_sound hmix.2)
      · exact absurd h (by simp)
    · exact absurd h (by simp)
  · -- `class' n sup body`: only a body this checker can read into the class table, and (tier
    -- 10) only if everything it mixes in is a declared `module`.
    split at h
    · rename_i hms
      split at h
      · rename_i hmix
        injection h with h
        injection h with h h'; injection h' with h' h''
        subst h; subst h'; subst h''
        simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hmix
        exact .classStmt hms hmix.1.1.1 hmix.1.1.2 (chkConsts_sound hmix.1.2)
          (chkNested_sound hmix.2)
      · exact absurd h (by simp)
    · exact absurd h (by simp)
  · -- `send none m args (some (.block ps [] body))`: either a `lambda`/`proc` literal, or a
    -- call to a top-level method that passes the block.
    split at h
    · rename_i hself
      split at h
      · -- `lambda`/`proc`, with no positional arguments
        rename_i hname
        split at h
        · rename_i hidx
          injection h with h
          injection h with h h'; injection h' with h' h''
          subst h; subst h'; subst h''
          -- The guard is one `&&`: the name is `lambda`/`proc` *and* there are no
          -- positional arguments. `lambdaLit`'s conclusion needs the second as `args = []`.
          have hd := hname
          simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
            List.isEmpty_iff] at hd
          obtain ⟨hm, ha⟩ := hd
          subst ha
          exact .lambdaLit hm hidx
        · exact absurd h (by simp)
      · -- anything else: the block goes to a method
        split at h
        · rename_i hargs
          split at h
          · rename_i hidx
            split at h
            · rename_i hdef
              split at h
              · rename_i hpar
                split at h
                · rename_i hbody
                  split at h
                  · rename_i hI
                    injection h with h
                    injection h with h h'; injection h' with h' h''
                    subst h; subst h'; subst h''
                    exact .callDefBlk hself (chkAll_sound hargs) hidx hdef hpar
                      (by subst hI; exact chk_sound hbody)
                  · exact absurd h (by simp)
                · exact absurd h (by simp)
              · exact absurd h (by simp)
            · exact absurd h (by simp)
          · exact absurd h (by simp)
        · exact absurd h (by simp)
    · -- tier 11: implicit-self dispatch carrying a block (`Judge.selfCallBlk`)
      rename_i hself
      split at h
      · rename_i hargs
        split at h
        · rename_i hidx
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
                  exact .selfCallBlk hself (chkAll_sound hargs) hidx hmeth hpar
                    (by subst hI; exact chk_sound hbody)
                · exact absurd h (by simp)
              · exact absurd h (by simp)
            · exact absurd h (by simp)
          · exact absurd h (by simp)
        · exact absurd h (by simp)
      · exact absurd h (by simp)
    · exact absurd h (by simp)
  · -- `send none m args`: tier 14c's keyword route first (a trailing `kwargs` is not a value,
    -- so it has no other route), then strictness, the assumption table and the def table.
    split at h
    · -- the argument list ends in a `kwargs` node (`Judge.callDefKw`)
      rename_i pos entries hsplit
      split at h
      · rename_i posTys Γ₁ I₁ hpos
        split at h
        · rename_i kws Γk Ik hkw
          split at h
          · rename_i d hdef
            split at h
            · rename_i Γb hpar
              split at h
              · rename_i ρ Γb' Iout hbody
                split at h
                · rename_i hI
                  injection h with h
                  injection h with h h'; injection h' with h' h''
                  subst h; subst h'; subst h''
                  exact .callDefKw (splitKw?_sound hsplit) (chkAll_sound hpos)
                    (chkKw_sound hkw) hdef hpar (by subst hI; exact chk_sound hbody)
                · exact absurd h (by simp)
              · exact absurd h (by simp)
            · exact absurd h (by simp)
          · exact absurd h (by simp)
        · exact absurd h (by simp)
      · exact absurd h (by simp)
    · split at h
      · rename_i hargs
        split at h
        · -- a non-returning argument: the call never dispatches
          rename_i hnever
          injection h with h
          injection h with h h'; injection h' with h' h''
          subst h; subst h'; subst h''
          exact .callNever (chkAll_sound hargs) hnever
        · split at h
          · -- tier 16b: `raise C` / `raise C, "msg"`, which does not return (`Judge.raiseCls`)
            rename_i hm
            subst hm
            split at h
            · rename_i n'
              split at h
              · rename_i hexc
                injection h with h
                injection h with h h'; injection h' with h' h''
                subst h; subst h'; subst h''
                exact .raiseCls (chkAll_sound hargs) (.inl rfl) hexc
              · exact absurd h (by simp)
            · rename_i n'
              split at h
              · rename_i hexc
                injection h with h
                injection h with h h'; injection h' with h' h''
                subst h; subst h'; subst h''
                exact .raiseCls (chkAll_sound hargs) (.inr rfl) hexc
              · exact absurd h (by simp)
            · exact absurd h (by simp)
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
  · -- tier 9c: `send (some recv) m args (some (block …))` -- a builtin iterator with a block
    -- literal. Receiver must synthesize `arrayOf elem`; the block's body is typed here.
    split at h
    · rename_i hrecv
      split at h
      · rename_i hargs
        split at h
        · rename_i hpar
          split at h
          · rename_i hpe
            split at h
            · rename_i hbody
              split at h
              · rename_i hI
                split at h
                · rename_i hcap
                  split at h
                  · rename_i hres
                    injection h with h
                    injection h with h h'; injection h' with h' h''
                    subst h; subst h'; subst h''
                    exact .iterBlock (chk_sound hrecv) (chkAll_sound hargs)
                      (iterSig?_sound hpar hres) hpe
                      (by subst hI; exact chk_sound hbody) hcap
                  · exact absurd h (by simp)
                · exact absurd h (by simp)
              · exact absurd h (by simp)
            · exact absurd h (by simp)
          · exact absurd h (by simp)
        · exact absurd h (by simp)
      · exact absurd h (by simp)
    · -- tier 11: an instance method called with a block (`Judge.callMethodBlk`)
      rename_i hrecv
      split at h
      · split at h
        · rename_i hargs
          split at h
          · rename_i hidx
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
                    exact .callMethodBlk (chk_sound hrecv) (chkAll_sound hargs) hidx hmeth
                      hpar (by subst hI; exact chk_sound hbody)
                  · exact absurd h (by simp)
                · exact absurd h (by simp)
              · exact absurd h (by simp)
            · exact absurd h (by simp)
          · exact absurd h (by simp)
        · exact absurd h (by simp)
      · exact absurd h (by simp)
    · -- tier 11: a singleton method / module function called with a block
      -- (`Judge.callSMethodBlk`)
      rename_i hrecv
      split at h
      · split at h
        · rename_i hargs
          split at h
          · rename_i hidx
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
                    exact .callSMethodBlk (chk_sound hrecv) (chkAll_sound hargs) hidx hmeth
                      hpar (by subst hI; exact chk_sound hbody)
                  · exact absurd h (by simp)
                · exact absurd h (by simp)
              · exact absurd h (by simp)
            · exact absurd h (by simp)
          · exact absurd h (by simp)
        · exact absurd h (by simp)
      · exact absurd h (by simp)
    · exact absurd h (by simp)
  · -- tier 9c: `send (some recv) m args (some (blockpass (some pe)))` -- the two `&` forms.
    split at h
    · rename_i hrecv
      split at h
      · rename_i hargs
        split at h
        · rename_i hpar
          split at h
          · -- `&:sym`: `Symbol#to_proc`, so the block's return type is a `PrimSig` row's
            split at h
            · rename_i hsig
              split at h
              · rename_i hres
                injection h with h
                injection h with h h'; injection h' with h' h''
                subst h; subst h'; subst h''
                exact .iterSymPass (chk_sound hrecv) (chkAll_sound hargs)
                  (iterSig?_sound hpar hres) (primSig?_sound hsig)
              · exact absurd h (by simp)
            · exact absurd h (by simp)
          · -- `&expr`: the expression has to synthesize a `Ty.clos`
            split at h
            · rename_i hpe
              split at h
              · rename_i hclos
                split at h
                · rename_i hΓb
                  split at h
                  · rename_i hbody
                    split at h
                    · rename_i hI
                      split at h
                      · rename_i hcap
                        split at h
                        · rename_i hres
                          injection h with h
                          injection h with h h'; injection h' with h' h''
                          subst h; subst h'; subst h''
                          exact .iterClosPass (chk_sound hrecv) (chkAll_sound hargs)
                            (chk_sound hpe) (iterSig?_sound hpar hres) hclos hΓb
                            (by subst hI; exact chk_sound hbody) hcap
                        · exact absurd h (by simp)
                      · exact absurd h (by simp)
                    · exact absurd h (by simp)
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
            · -- tier 12: `Module#===`, checked before `is_a?` and before the dispatch
              rename_i hm
              subst hm
              split at h
              · -- `split` substituted `σ := .clsOf cn` and `argTys := [_]`
                split at h
                · rename_i hok
                  injection h with h
                  injection h with h h'; injection h' with h' h''
                  subst h; subst h'; subst h''
                  exact .caseEqQuery (chk_sound hrecv) (chkAll_sound hargs) hok
                · exact absurd h (by simp)
              · -- tier 16: the receiver is a *value*, so `===` is the `PrimSig` row
                split at h
                · rename_i τ' hprim
                  injection h with h
                  injection h with h h'; injection h' with h' h''
                  subst h; subst h'; subst h''
                  exact .prim (chk_sound hrecv) (chkAll_sound hargs) (primSig?_sound hprim)
                · exact absurd h (by simp)
            · split at h
              · -- tier 12: `is_a?`, checked before the receiver dispatch
                rename_i hm
                subst hm
                split at h
                · -- `split` substituted `argTys := [.clsOf _]`, so no equation is needed:
                  -- `hargs` already has the shape `JudgeAll`'s index wants.
                  split at h
                  · rename_i hok
                    injection h with h
                    injection h with h h'; injection h' with h' h''
                    subst h; subst h'; subst h''
                    exact .isAQuery (chk_sound hrecv) (chkAll_sound hargs) hok
                  · exact absurd h (by simp)
                · exact absurd h (by simp)
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
                  · rename_i hsmnone
                    -- Tier 13f: `Module#to_s` is matched here, after `smroGet?` missed -- and
                    -- that miss *is* `Judge.clsToS`'s guard, so `hsmnone` is the premise.
                    split at h
                    · rename_i hts
                      injection h with h
                      injection h with h h'; injection h' with h' h''
                      subst h; subst h'; subst h''
                      simp only [Bool.and_eq_true, decide_eq_true_eq] at hts
                      obtain ⟨hmts, hzero⟩ := hts
                      subst hmts
                      exact .clsToS (chk_sound hrecv) (hzero ▸ chkAll_sound hargs) hsmnone
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
                    · rename_i hclos
                      split at h
                      · rename_i hpar
                        split at h
                        · rename_i hbody
                          split at h
                          · rename_i hI
                            split at h
                            · rename_i hcap
                              injection h with h
                              injection h with h h'; injection h' with h' h''
                              subst h; subst h'; subst h''
                              exact .closCall (by
                                rcases (by simpa using hname : _ = "call" ∨ _ = "[]") with
                                  h | h
                                · exact .inl h
                                · exact .inr h) (chk_sound hrecv)
                                (chkAll_sound hargs) hclos hpar
                                (by subst hI; exact chk_sound hbody) hcap
                            · exact absurd h (by simp)
                          · exact absurd h (by simp)
                        · exact absurd h (by simp)
                      · exact absurd h (by simp)
                    · exact absurd h (by simp)
                  · exact absurd h (by simp)
                · -- the receiver is an instance: `Object#class` (tier 13f) first, then
                  -- dispatch up the chain from its class.
                  split at h
                  · rename_i hcl
                    injection h with h
                    injection h with h h'; injection h' with h' h''
                    subst h; subst h'; subst h''
                    simp only [Bool.and_eq_true, decide_eq_true_eq] at hcl
                    obtain ⟨hmcl, hzero⟩ := hcl
                    subst hmcl
                    exact .classOf (chk_sound hrecv) (hzero ▸ chkAll_sound hargs)
                  · split at h
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
                    · -- tier 10: dispatch missed, so `method_missing` (`Judge.callMissing`)
                      rename_i hmiss
                      split at h
                      · exact absurd h (by simp)
                      · rename_i hobj
                        split at h
                        · rename_i hmm
                          split at h
                          · rename_i hpar
                            split at h
                            · rename_i hbody
                              split at h
                              · rename_i hI
                                injection h with h
                                injection h with h h'; injection h' with h' h''
                                subst h; subst h'; subst h''
                                exact .callMissing (chk_sound hrecv) (chkAll_sound hargs) hmiss
                                  (fun hc => by
                                    cases hc with
                                    | mk hin => exact absurd hin (by simpa [objectMethod?] using hobj))
                                  hmm hpar (by subst hI; exact chk_sound hbody)
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
  · -- `yield' args`: the block the enclosing method was called with.
    split at h
    · rename_i hblk
      split at h
      · rename_i hargs
        split at h
        · rename_i hclos
          split at h
          · rename_i hpar
            split at h
            · rename_i hbody
              split at h
              · rename_i hI
                split at h
                · rename_i hcap
                  injection h with h
                  injection h with h h'; injection h' with h' h''
                  subst h; subst h'; subst h''
                  exact .yieldExpr hblk (chkAll_sound hargs) hclos hpar
                    (by subst hI; exact chk_sound hbody) hcap
                · exact absurd h (by simp)
              · exact absurd h (by simp)
            · exact absurd h (by simp)
          · exact absurd h (by simp)
        · exact absurd h (by simp)
      · exact absurd h (by simp)
    · exact absurd h (by simp)
    · exact absurd h (by simp)
  · -- tier 10: `zsuper` -- `super` with no argument list, for a parameterless method.
    split at h
    · rename_i hfr
      split at h
      · rename_i hcur
        split at h
        · rename_i hguard
          split at h
          · rename_i hmro
            split at h
            · rename_i hrest
              split at h
              · rename_i hmeth
                split at h
                · rename_i hpar
                  split at h
                  · rename_i hbody
                    injection h with h
                    injection h with h h'; injection h' with h' h''
                    subst h; subst h'; subst h''
                    -- One `&&`: the `Defn` found from the receiver's class is the running
                    -- method's (so its arity is the one being required empty), and that arity
                    -- is zero.
                    have hg := hguard
                    simp only [Bool.and_eq_true, decide_eq_true_eq, List.isEmpty_iff] at hg
                    obtain ⟨hdc, hnp⟩ := hg
                    exact .zsuperCall hfr (hdc ▸ hcur) hnp hmro hrest hmeth hpar
                      (chk_sound hbody)
                  · exact absurd h (by simp)
                · exact absurd h (by simp)
              · exact absurd h (by simp)
            · exact absurd h (by simp)
          · exact absurd h (by simp)
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

/-- `chkOwner?` reports a name only for an expression that really types as *that* class
object. One `split`, because the arm it is extracted from is the only thing in it. -/
theorem chkOwner?_sound : ∀ {fuel : Nat} {κ : Ctx} {Γ Γ₁ : Env} {I I₁ : Ty} {base : Expr}
    {owner : String},
    chkOwner? fuel κ Γ I base = some (owner, Γ₁, I₁) →
    Judge κ Γ I base (.clsOf owner) Γ₁ I₁ := by
  intro fuel κ Γ Γ₁ I I₁ base owner h
  unfold chkOwner? at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · rename_i o G J hchk
      injection h with h; injection h with h h'; injection h' with h' h''
      subst h; subst h'; subst h''
      exact chk_sound hchk
    · exact absurd h (by simp)

/-- **`chkRescues` never admits a rescue clause `JudgeRescues` does not** (tier 16b). Premise
for premise, and the two equations (`Γ' = Γh ++ Γ`, `I' = I`) come out of the guard rather than
being substituted, for `while'`'s reason. -/
theorem chkRescues_sound : ∀ {fuel : Nat} {κ : Ctx} {Γ : Env} {I : Ty}
    {rescues : List (List Expr × Option (TargetKind × String) × Expr)} {τ : Ty},
    chkRescues fuel κ Γ I rescues = some τ → JudgeRescues κ Γ I rescues τ := by
  intro fuel κ Γ I rescues τ h
  unfold chkRescues at h
  split at h
  · exact absurd h (by simp)
  · injection h with h; subst h; exact .nil
  · rename_i cls binding handler rest
    split at h
    · rename_i names hnames
      split at h
      · rename_i hall
        split at h
        · rename_i Γh hbind
          split at h
          · rename_i ρ Γ' I' hhandler
            split at h
            · rename_i hfix
              simp only [Bool.and_eq_true, decide_eq_true_eq] at hfix
              obtain ⟨hΓ', hI'⟩ := hfix
              split at h
              · rename_i τr hrest
                injection h with h; subst h
                exact .cons hnames hall hbind (chk_sound hhandler) hΓ' hI'
                  (chkRescues_sound hrest)
              · exact absurd h (by simp)
            · exact absurd h (by simp)
          · exact absurd h (by simp)
        · exact absurd h (by simp)
      · exact absurd h (by simp)
    · exact absurd h (by simp)

/-- **`chkKw` never admits keyword arguments `JudgeKw` does not** (tier 14c). Pair for pair,
with both states threading in the same order. -/
theorem chkKw_sound : ∀ {fuel : Nat} {κ : Ctx} {Γ Γ' : Env} {I I' : Ty}
    {es : List KwEntry} {kws : List (String × Ty)},
    chkKw fuel κ Γ I es = some (kws, Γ', I') → JudgeKw κ Γ I es kws Γ' I' := by
  intro fuel κ Γ Γ' I I' es kws h
  unfold chkKw at h
  split at h
  · exact absurd h (by simp)
  · injection h with h; injection h with h h'; injection h' with h' h''
    subst h; subst h'; subst h''; exact .nil
  · rename_i k v es'
    split at h
    · rename_i τ Γ₁ I₁ hv
      split at h
      · rename_i kws' Γ₂ I₂ hes
        injection h with h; injection h with h h'; injection h' with h' h''
        subst h; subst h'; subst h''
        exact .pair (chk_sound hv) (chkKw_sound hes)
      · exact absurd h (by simp)
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- **`chkNested` never admits a nested declaration `JudgeNested` does not** (tier 13e).
Premise for premise, and the recursion is the relation's: into the nested body's own nested
list, and along the rest of the list. -/
theorem chkNested_sound : ∀ {fuel : Nat} {κ : Ctx} {pfx : String} {nst : Nested},
    chkNested fuel κ pfx nst = true → JudgeNested κ pfx nst := by
  intro fuel κ pfx nst h
  unfold chkNested at h
  split at h
  · exact absurd h (by simp)
  · exact .nil
  · split at h
    · rename_i ms sms incs exts preps cs nst' hms
      simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at h
      exact .cons hms h.1.1.1.1 h.1.1.1.2 (chkConsts_sound h.1.1.2)
        (chkNested_sound h.1.2) (chkNested_sound h.2)
    · exact absurd h (by simp)

/-- **`chkConsts` never admits a class-body constant `JudgeConsts` does not** (tier 13).
Premise for premise: `constLitTy?` had to answer, and `chk` had to come back with exactly
that type and the empty outgoing environment and spine. The `if`'s condition *is* the triple
equality, so injecting it gives all three at once. -/
theorem chkConsts_sound : ∀ {fuel : Nat} {κ : Ctx} {cs : List (String × Expr)},
    chkConsts fuel κ cs = true → JudgeConsts κ cs := by
  intro fuel κ cs h
  unfold chkConsts at h
  split at h
  · exact .nil
  · rename_i n e cs'
    split at h
    · exact absurd h (by simp)
    · split at h
      · rename_i τ hlit
        split at h
        · rename_i hchk
          exact .cons hlit (chk_sound hchk) (chkConsts_sound h)
        · exact absurd h (by simp)
      · exact absurd h (by simp)

theorem chkPairs_sound : ∀ {fuel : Nat} {κ : Ctx} {Γ Γ' : Env} {I I' : Ty}
    {ps : List (Expr × Expr)} {kτ vτ : Ty},
    chkPairs fuel κ Γ I ps = some (kτ, vτ, Γ', I') → JudgePairs κ Γ I ps kτ vτ Γ' I' := by
  intro fuel κ Γ Γ' I I' ps kτ vτ h
  unfold chkPairs at h
  split at h
  · exact absurd h (by simp)
  · injection h with h; injection h with h h'; injection h' with h' h''
    injection h'' with h'' h'''
    subst h; subst h'; subst h''; subst h'''; exact .nil
  · split at h
    · rename_i σ Γ₁ I₁ hk
      split at h
      · rename_i ν Γ₂ I₂ hv
        split at h
        · rename_i kr vr Γ₃ I₃ hrest
          injection h with h; injection h with h h'; injection h' with h' h''
          injection h'' with h'' h'''
          subst h; subst h'; subst h''; subst h'''
          exact .cons (chk_sound hk) (chk_sound hv) (chkPairs_sound hrest)
        · exact absurd h (by simp)
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
  · -- tier 16's `next if …` guard (`JudgeSeq.nextGuard`), matched before both the return guard
    -- and the generic `cons` arm.
    split at h
    · rename_i hc
      split at h
      · rename_i hrest
        injection h with h
        injection h with h h'; injection h' with h' h''
        subst h; subst h'; subst h''
        exact JudgeSeq.nextGuard (chk_sound hc) (chkSeq_sound hrest)
      · exact absurd h (by simp)
    · exact absurd h (by simp)
  · -- tier 12's guard clause, matched before the generic `cons` arm
    split at h
    · rename_i hc
      split at h
      · rename_i hr
        split at h
        · rename_i hI
          split at h
          · rename_i hrest
            injection h with h
            injection h with h h'; injection h' with h' h''
            subst h; subst h'; subst h''
            exact JudgeSeq.guard (chk_sound hc) (chk_sound hr) hI (chkSeq_sound hrest)
          · exact absurd h (by simp)
        · exact absurd h (by simp)
      · exact absurd h (by simp)
    · exact absurd h (by simp)
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

#print axioms narrowCond?_sound
#print axioms nilQSafe?_sound
#print axioms builtinCls?_sound
#print axioms comparable?_sound
#print axioms iterSig?_sound
#print axioms primSigStr?_sound
#print axioms primSigArr?_sound
#print axioms primSigHash?_sound
#print axioms primSig?_sound
#print axioms chk_sound
#print axioms chkAll_sound
#print axioms constLitTy?_sound
#print axioms constLitTys?_sound
#print axioms constLitPairTys?_sound
#print axioms constLitTy?_nilQSafe
#print axioms excCls?_sound
#print axioms splitKw?_sound
#print axioms chkKw_sound
#print axioms chkRescues_sound
#print axioms chkOwner?_sound
#print axioms chkNested_sound
#print axioms chkConsts_sound
#print axioms chkPairs_sound
#print axioms chkSeq_sound
#print axioms validate_sound_syntactic

end Ratchet
