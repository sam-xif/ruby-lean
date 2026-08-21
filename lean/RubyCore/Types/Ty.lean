import RubyCore.Syntax

/-!
# The type language, and the local environment

Split out of `Types/Core.lean` for F1a (`PLAN.md` W5 asks for exactly this cut:
`Ty.lean`, `Sub.lean`, `Narrow.lean`, `Infer.lean`, `Check.lean`). The immediate
reason is that `Types/Decls.lean` needs `Ty` and `Core.lean` needs `Decls`, so
the two cannot both live in `Core.lean`. No definition changed.
-/

namespace RubyCore.Types

/-- The P0 type language. No subtyping: `Sub` is equality, so it is not yet a
    separate relation. Widening this is P1/P3.

    **What D10 changes about the *meaning* of an arm**, without changing an arm:
    a class type denotes its **declared method set** (`Types/Decls.lean`), and the
    ancestors walk is a cheap sufficient condition for it rather than the
    definition (`typing-a-mutable-method-table.md` §5). The four ground arms below
    are the degenerate case, since each denotes a class nothing can reopen inside
    the fragment. -/
inductive Ty where
  | int
  | bool
  | nilT
  /-- A Symbol. Present only because `def` *evaluates* to the method name
      (`Interp.lean:2624`), so a `def` in tail position needs a type. Nothing
      constructs or consumes one otherwise. -/
  | sym
  /-- **An instance of the class named `name`** (F1b/T2). The arm F1a said was
      missing — `typing-a-mutable-method-table.md` §8's correction to its own F1a
      row: the declaration table is keyed on a class *name* and until now no `Ty`
      carried one, so `declFor` could only ever be asked about the four ground
      classes.

      **Keyed on the name, not on an `ObjId`**, for the reason `Decls` is:
      `check` is a pure function of the program and object identities exist only
      in a heap (`Types/Decls.lean`). What ties the name back to the heap is
      `valueTy?`'s `.ref` arm, which is the first arm of that function to read
      its heap argument at all — the change L137 threaded the heap in for.

      **Nothing constructs one yet.** `infer` has no `new`, no `classDef` and no
      `casgn`, so no program gets a value of this type; the arm exists so that
      `entry_dispatch` has to survive an abstract non-immediate receiver, which
      is where the fragment's poverty was load-bearing (§F1b of `HANDOFF.md`).
      Giving it a producer needs `alloc`, hence the fuel-monotonicity lemma
      `ancestors_congr` wants, and that is the next commit rather than this one. -/
  | cls (name : String)
  /-- **The top type** (L183) — *some* value, of a type the checker does not pin.

      It exists for one reason, and the reason decides its whole shape: a
      declaration row whose parameter is *any object* cannot be written without it,
      and `Module#===` is exactly such a row —
      `slice-verdict.md` §4a prices it as the first of the four rungs to `const`,
      because `case x when String` with a *concrete* parameter types only when `x`
      is already known to be a `String`, which is the case the program is testing.

      **Nothing is ever *typed* `any`.** `valueTy?` has no arm for it, so no value
      carries it and no expression infers at it; it appears only as a **declared
      parameter**, and the imprecision lives in `subTy` at exactly that position.
      That is what keeps `CtlOk` — and all 39 `inv_value`/`inv_push`/`inv_eval`
      call sites — unchanged: the in-flight value keeps its exact type. Making
      `ValueTy` a *relation* so a value could have several types is the other
      design, it is what unions and nilable need, and it is deliberately **not**
      this one. -/
  | any
  /-- **The class object named `name`** (L184) — *the* class, not an instance of it.

      `.cls C` means an instance of `C`; this is the receiver `Token.from(x)` and
      `case v when String` send to. `slice-verdict.md` §4a prices it as rung 2 of
      four, and L180's measurement says where the cost is: **not** here and not in
      `valueTy?`, but in carrying `TyClass` — which must name *whatever `classOf`
      says*, because only 27 of the booted heap's 87 class objects have a
      materialized eigenclass and the split runs straight through the classes the
      slice uses (`String`/`Array`/`Regexp` have one, `Integer`/`Float`/`Hash` do
      not, and dispatch for those goes through `Class`).

      **Keyed on the class's own name**, as `.cls` is, and for the same reason:
      `infer` is a pure function of the program and cannot name an `ObjId`. The
      table key it reads is *not* `name` though — see `tyClassNames`, which prefixes
      it, because a row on `.clsOf "String"` (a singleton method) and a row on
      `.cls "String"` (an instance method) are different declarations. -/
  | clsOf (name : String)
  /-- **`τ` or `nil`** (L193), and the first arm that is *inhabited by values of
      more than one shape*. That is the whole difference from `.any`, whose
      docstring above says so: `any` is a declared *parameter* position and no
      value is ever typed at it, while a `nilable` is what an expression **infers
      at** — `if c then "s" end`, `x&.foo`, `return if c`. This slice cannot be
      typed without it: `T.nilable(String)` appears in a quarter of its `sig`s.

      **It is what made `ValueTy` a relation.** L183 wrote down the alternative and
      declined it ("making `ValueTy` a relation so a value could have several types
      is what unions and nilable need, and it is deliberately not this one"); this
      is that commit. `valueTy?` is unchanged — it still answers *the* exact type of
      a value — and `ValueTy h v τ` now reads *`v`'s exact type is below `τ`*, so a
      `String` reference satisfies both `.cls "String"` and `.nilable (.cls
      "String")`.

      Only `nil` and members of `τ` inhabit it: there is no general union, because
      nothing in the slice needs one and a general union needs a normal form to keep
      `Env` equality (which the `if`-merge and the loop-stability condition both
      decide) usable. -/
  | nilable (τ : Ty)
  /-- **A Float** (L202) — the fifth ground arm, and it is `.int`'s twin in every
      clause that mentions it.

      It costs what `.int` costs and nothing more, which is the whole reason it is
      the rung after `return`: a float is an *immediate* value (`Value.flt`), so
      `valueTy?` answers it without reading the heap, `TyClass` pins it to
      `Boot.floatId` outright rather than through `classPayload?`, and
      `tyClassNames` names one class. What it does **not** buy is any *send* — no
      row in `baseDecls` is declared on it — so a body containing `1.5` moves from
      *out of fragment* to *needing a declaration*, which is the same crossing
      L195–L197 made for constants and ivars.

      `--sets` is what picked it (L201): `{flt}` was a singleton blocker set for
      three slice bodies, the only cheap entry left on the marginal-value table. -/
  | float
deriving DecidableEq, Repr, Inhabited

/-- **Subtyping, and it is exactly one rule wide** (L183): everything is below
    `any`, and otherwise types are compared by equality as they always were.

    Used *only* where a declared parameter is compared against an argument's type —
    `infer`'s send rules, `KontOk.recvK`/`argsK`'s premises, and `ValuesTy`. Not on
    the value judgement, and not on the `if` join: a join needs a *least upper
    bound*, which is the unions rung and a different statement. -/
def subTy (σ τ : Ty) : Bool :=
  match τ with
  | .any => true
  | .nilable τ' => σ == .nilT || σ == .nilable τ' || subTy σ τ'
  | _ => σ == τ

/-- **The join** (L193) — a *least* upper bound is not what this computes and the
    difference matters. It answers only the two cases the fragment produces, an
    `if` whose branches agree and one where exactly one side is `nil`, and `none`
    otherwise. Answering `.any` for the rest would be an upper bound but a useless
    one: nothing can be done with an `any`-typed value, and — worse — `ValueTy h v
    .any` holds for *every* value, so `.any` in an inferred position would let the
    checker forget what it knows. `.any` stays a declared-parameter type. -/
def joinTy (σ τ : Ty) : Option Ty :=
  if σ == τ then some σ
  else if σ == .nilT then some (.nilable τ)
  else if τ == .nilT then some (.nilable σ)
  else none

/-- Pointwise, at the arity the signature declares. A length mismatch is `false`,
    which is what keeps the arity check that used to be list equality. -/
def subTys : List Ty → List Ty → Bool
  | [], [] => true
  | σ :: σs, τ :: τs => subTy σ τ && subTys σs τs
  | _, _ => false

/-- **At a concrete parameter, `subTy` *is* equality** — the lemma that makes the
    weakening inert: every row in `baseDecls` has concrete parameters, so their
    conformance obligations see the proposition they always saw. -/
theorem subTy_atomic {σ τ : Ty} (ha : τ ≠ .any) (hn : ∀ τ', τ ≠ .nilable τ') :
    subTy σ τ = true ↔ σ = τ := by
  cases τ <;> simp_all [subTy]

/-- The old name, kept for the call sites that instantiate it at a `baseDecls`
    parameter — every one of those is atomic, so the extra side condition is
    discharged by `simp`. -/
theorem subTy_concrete {σ τ : Ty} (hτ : τ ≠ .any) (hn : ∀ τ', τ ≠ .nilable τ') :
    subTy σ τ = true ↔ σ = τ := subTy_atomic hτ hn

@[simp] theorem subTy_refl (τ : Ty) : subTy τ τ = true := by
  cases τ <;> simp [subTy]

/-- **Transitivity**, which the unrelaxed `subTy` did not need and this one does:
    `ValueTy` composes a value's exact type with the declared one, and `CtlOk`'s
    eval clause composes again with the continuation's. -/
theorem subTy_trans : ∀ {a b c : Ty}, subTy a b = true → subTy b c = true →
    subTy a c = true
  | a, b, .any, _, _ => by simp [subTy]
  | a, b, .nilable c', hab, hbc => by
    simp only [subTy, Bool.or_eq_true, beq_iff_eq] at hbc ⊢
    rcases hbc with (rfl | rfl) | hbc'
    · exact Or.inl (Or.inl ((subTy_atomic (τ := Ty.nilT) (by simp) (by simp)).mp hab))
    · simpa only [subTy, Bool.or_eq_true, beq_iff_eq, or_assoc] using hab
    · exact Or.inr (subTy_trans hab hbc')
  | a, b, .int, hab, hbc => by
    simp only [subTy, beq_iff_eq] at hbc; subst hbc; exact hab
  | a, b, .bool, hab, hbc => by
    simp only [subTy, beq_iff_eq] at hbc; subst hbc; exact hab
  | a, b, .nilT, hab, hbc => by
    simp only [subTy, beq_iff_eq] at hbc; subst hbc; exact hab
  | a, b, .sym, hab, hbc => by
    simp only [subTy, beq_iff_eq] at hbc; subst hbc; exact hab
  | a, b, .cls n, hab, hbc => by
    simp only [subTy, beq_iff_eq] at hbc; subst hbc; exact hab
  | a, b, .clsOf n, hab, hbc => by
    simp only [subTy, beq_iff_eq] at hbc; subst hbc; exact hab
  | a, b, .float, hab, hbc => by
    simp only [subTy, beq_iff_eq] at hbc; subst hbc; exact hab

@[simp] theorem subTys_refl : ∀ (ps : List Ty), subTys ps ps = true
  | [] => rfl
  | _ :: ps => by simp [subTys, subTys_refl ps]

theorem subTys_nil_inv {ps : List Ty} (h : subTys [] ps = true) : ps = [] := by
  cases ps with
  | nil => rfl
  | cons _ _ => exact absurd h (by simp [subTys])

theorem subTys_cons_inv {σ : Ty} {σs ps : List Ty} (h : subTys (σ :: σs) ps = true) :
    ∃ τp psrest, ps = τp :: psrest ∧ subTy σ τp = true ∧ subTys σs psrest = true := by
  cases ps with
  | nil => exact absurd h (by simp [subTys])
  | cons τp psrest =>
    simp only [subTys, Bool.and_eq_true] at h
    exact ⟨τp, psrest, rfl, h.1, h.2⟩

/-- **`nilable` normalized at `nilT`** (L193b). `nilable nilT` and `nilT` denote the
    same set of values, and the *open* front end is why the difference has to be
    collapsed rather than tolerated: it joins against a type **variable**, so it
    cannot see whether the other side is `nil` and must emit `nilOf α`; the nominal
    join, at a substituted `α = nilT`, answers `nilT`. Without this the two would
    disagree at exactly one instantiation and `inferOpen_factors` would be false. -/
def mkNilable (τ : Ty) : Ty := if τ == .nilT then .nilT else .nilable τ

@[simp] theorem joinTy_nilT_left (τ : Ty) : joinTy .nilT τ = some (mkNilable τ) := by
  by_cases h : τ = Ty.nilT
  · subst h; simp [joinTy, mkNilable]
  · simp [joinTy, mkNilable, h, Ne.symm h]

@[simp] theorem joinTy_nilT_right (τ : Ty) : joinTy τ .nilT = some (mkNilable τ) := by
  by_cases h : τ = Ty.nilT
  · subst h; simp [joinTy, mkNilable]
  · simp [joinTy, mkNilable, h]

@[simp] theorem subTy_nilT_mkNilable (τ : Ty) : subTy .nilT (mkNilable τ) = true := by
  unfold mkNilable
  by_cases h : τ = Ty.nilT
  · subst h; simp
  · simp [h, subTy]

@[simp] theorem subTy_mkNilable (τ : Ty) : subTy τ (mkNilable τ) = true := by
  unfold mkNilable
  by_cases h : τ = Ty.nilT
  · subst h; simp
  · simp [h, subTy]

/-- Both sides of a join are below it. The join rule's whole soundness content, and
    the reason it is two lines: `joinTy` answers only the two shapes it can justify. -/
theorem joinTy_sub {σ τ τj : Ty} (h : joinTy σ τ = some τj) :
    subTy σ τj = true ∧ subTy τ τj = true := by
  unfold joinTy at h
  split at h
  · rename_i heq
    simp only [beq_iff_eq] at heq
    subst heq
    simp_all
  · split at h
    · rename_i hn
      simp only [beq_iff_eq] at hn
      simp only [Option.some.injEq] at h
      subst h; subst hn
      exact ⟨by simp [subTy], by simp [subTy]⟩
    · split at h
      · rename_i hn
        simp only [beq_iff_eq] at hn
        simp only [Option.some.injEq] at h
        subst h; subst hn
        exact ⟨by simp [subTy], by simp [subTy]⟩
      · exact absurd h (by simp)

/-- Local-variable typing environment. Order is canonical (`envSet` replaces in
    place) so that environment *equality* is a usable check — the `if`-merge and
    the loop-stability condition both need it. -/
abbrev Env := List (String × Ty)

def envGet? (Γ : Env) (x : String) : Option Ty :=
  (Γ.find? (·.1 == x)).map (·.2)

def envSet : Env → String → Ty → Env
  | [], x, τ => [(x, τ)]
  | (y, σ) :: Γ, x, τ => if y == x then (x, τ) :: Γ else (y, σ) :: envSet Γ x τ

/-! ## The static context of an activation

Two facts about the frame a rule is being checked in, bundled because they change
at exactly the same place — `KontOk.frameK`, where the environment changes too —
and because carrying them as separate parallel lists means two of every lemma.

* **`cls`** — the definee's class **name**: where a `def` here installs, and
  therefore the key of the row it declares (F1b.9/F1b.10). `infer` cannot name an
  `ObjId`, so the name is what a declaration hangs off.
* **`selfCls`** — `some c` when `self` in this activation is an *instance* of `c`,
  which is true in a **method** body and false in a class body, where `self` is
  the class object and has no type at all (`plainRecv` excludes classes). It is an
  `Option` rather than a `Bool` beside `cls` because the two names are not the
  same thing in general — a method inherited into a subclass has `cls` at the
  owner — even though today they coincide.

`top` stays a separate flag, read off `Γs.isEmpty` rather than stored, because it
is a property of the *stack* and not of a frame. -/
structure FrameCtx where
  cls : String
  selfCls : Option String := none
  /-- **The enclosing method's declared return type** (L198), or `none` in a class
      body and at toplevel — where a `return` has no target and the desugarer gates
      one anyway.

      It is the *declared* type rather than the body's inferred one, and that is what
      makes the rule local: `return e` can check `e` against `ret` without knowing
      what the rest of the body will answer. `UserConforms` is where the two are tied
      together — it already requires the body to infer at `d.ret`.

      Read `KontOk.frameK`'s premise next: the frame boundary is where this field has
      to *agree* with the type the caller's continuation expects, and that agreement
      is what lets `RetOk` be **derived** from `KontOk` instead of carried as a
      separate invariant conjunct. -/
  ret : Option Ty := none
deriving DecidableEq, Repr, Inhabited

end RubyCore.Types
