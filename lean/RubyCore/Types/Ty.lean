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
  /-- **An `Array` whose elements are all `elem`** (L238) — the first *parameterised*
      arm, and the gate for Wall 1 rather than a convenience.

      **Why it is not optional.** `tyClassNames .any = []`, so no send can use `.any`
      as a receiver; a block whose parameter is `.any` therefore type-checks only if
      its body never calls a method on the parameter, and every block in the slice
      does (`identifiers.select { |i| i.start_with?("CVE-") }`). The element type is
      already *in the program* — `sig { returns(T::Array[String]) }` — and it was the
      type language that dropped it.

      **Invariant, deliberately.** `subTy` compares it by equality (the catch-all
      arm), so `arrayOf String` and `arrayOf Object` are unrelated. Covariance would
      be unsound at *mutation* under aliasing: `ys = xs; ys << 1` cannot be allowed to
      widen `ys`'s element type while `xs` still claims `arrayOf String`, and no
      local-only narrowing can see the other alias. Every mutating row must therefore
      preserve the element type, which is what makes the claim survive for all aliases.

      **`valueTy?` never answers one**, for `.any`'s and `.clsOf`'s reason and one
      more: computing an array's element type recurses through the *heap*, and a Ruby
      array can contain itself (`a = []; a << a`). `ValueTy` gains a **relational**
      arm instead — recursion on the *type*, which is structural — so a cyclic array
      inhabits no `arrayOf` type at all, which is sound.

      **Nothing constructs one yet**: the decoder still maps `T::Array[X]` to
      `.cls "Array"` and no row mentions the arm, so this commit accepts nothing new.
      What it buys is the relation and its inversions, which the iterator rung needs
      before it can type a block body. -/
  | arrayOf (elem : Ty)
  /-- **A union** (L269, `judgment-layer.md` §1.4) — a value of `σ` or of `τ`.

      **Inert on the checker path, by design.** Nothing in `infer`/`chk` constructs
      one, `subTy` compares it by equality (the catch-all arm), `tyClassNames`
      answers `[]` (a union dispatches from nowhere until narrowed — `.nilable`'s
      reason), and `TyClass` is `False` at it. So `--assn` and every certificate
      verdict are byte-identical, and `subTy` stays structurally recursive on `τ`
      (norm 5: the checked path must kernel-reduce).

      **The union's meaning lives in the judgment layer** (`Judgment/Sub.lean`):
      the declarative subtype relation `SubJ` decomposes it on both sides, the
      join rules of `Judge` may choose it as the widened bound where the branches
      disagree, and `dropNil` re-narrows it in conditionals. `ValueTy` does not
      yet have a union disjunction arm — that is the J1 (machine-typing) bill,
      recorded in `Judgment/implementation-notes.md` J14.

      **Binary, and no normal form is imposed**: `union a (union b c)` and
      `union (union a b) c` are different `Ty`s related by `SubJ` both ways.
      `mkUnion` collapses only the degenerate cases (equal sides, a `nilT` side —
      the latter normalizes to `.nilable`, keeping the two spellings of "or nil"
      from proliferating). -/
  | union (σ τ : Ty)
  /-- **An arrow — the type of a value-level callable** (L270), spelled as a
      **params spine**: `(A, B) → R` is `arrowCons A (arrowCons B (arrow0 R))`,
      one `arrowCons` cell per parameter (uncurried, arity-exact as Ruby lambdas
      are), terminated by `arrow0 ret`.

      **Why a spine and not `params : List Ty`**: a list payload makes `Ty` a
      *nested* inductive, and both derive handlers and the kernel refuse it —
      `deriving DecidableEq` has no nested handler (measured at this build), and
      the repo already learned that nested-derived equality does not
      kernel-reduce (V15's `exprEq`-on-fuel exists for exactly that reason). The
      spine keeps `Ty` simple-recursive, so `==` stays structural and `chk`'s
      `decide`s keep reducing (norm 5). The cost: a malformed spine
      (`arrowCons A .int`) is representable — it is garbage no rule constructs
      or consumes, harmless the way a nonsense union is.

      **Inert on the checker path, by L269's playbook**: `subTy` compares both
      arms by the catch-all, nothing in `infer`/`chk` constructs one,
      `tyClassNames` answers `[]` (an arrow dispatches from no method table —
      its one consumer is the judgment layer's `call` rule), `TyClass` is
      `False`, and the JSON codec round-trips both arms.

      **The meaning lives in the judgment layer**: `SubJ.arrow0`/`SubJ.arrowCons`
      give the standard variance (contravariant per-cell params, covariant ret)
      cell by cell — arity mismatches refuse structurally, which is the
      `ArgumentError` family's condition. The `Judge` lambda rule introduces an
      arrow (body judged at the chosen parameter types) and `Judge.sendCall`
      eliminates it. **Methods are deliberately *not* arrows**: a method is not
      a value in Ruby, and `MethodDecl` already *is* the method-arrow
      (params/ret/blk) keyed in the table — reifying one into an arrow is
      `method(:f)`'s future rule, not a representation change
      (`Judgment/implementation-notes.md` J17). -/
  | arrow0 (ret : Ty)
  | arrowCons (param : Ty) (rest : Ty)
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
  -- **The nilable is absorbed** (L204), and this is not a widening of the *type*
  -- language — it is the fourth and last case that already has an answer in it.
  -- `nilable τ` and `τ` have a least upper bound, `nilable τ`, and it is the one
  -- `subTy` already admits both sides of (`subTy_refl` and `subTy_mkNilable`).
  --
  -- The measurement that asked for it: an `if/elsif` chain with no final `else`
  -- answers `nilable Symbol` on the inner arm and `Symbol` on the outer one, and the
  -- three cases above refuse *that* — so the slice's `CVSS.severity`, a plain
  -- four-way `elsif` over a score, was out of fragment for a join the fragment
  -- already had the type for.
  else if σ == .nilable τ then some σ
  else if τ == .nilable σ then some τ
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
  -- L238: `arrayOf` is compared by equality, so transitivity at it is `Eq.trans` —
  -- the same shape every other concrete arm has, spelled because the arm carries a
  -- payload and the catch-all pattern below does not reach it.
  | a, b, .arrayOf e, hab, hbc => by
    simp only [subTy, beq_iff_eq] at hbc
    subst hbc
    exact hab
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
  -- L269: `union` is compared by equality on this (checker-path) relation, so
  -- transitivity at it is `arrayOf`'s shape — `Eq.trans`, spelled because the arm
  -- carries payloads.
  | a, b, .union x y, hab, hbc => by
    simp only [subTy, beq_iff_eq] at hbc; subst hbc; exact hab
  -- L270: same shape at the two arrow-spine arms — equality on the checker-path
  -- relation.
  | a, b, .arrow0 r, hab, hbc => by
    simp only [subTy, beq_iff_eq] at hbc; subst hbc; exact hab
  | a, b, .arrowCons p r, hab, hbc => by
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

/-- **The absorption, packaged for `apply`** (L204). `joinATy_subst`'s two new cases
    need exactly this equation at a type the tactic cannot name (the match's binder is
    inaccessible), so stating it as a lemma is what lets unification supply it. Both
    branches of `mkNilable` are here: at `nilT` the join is `joinTy`'s *first* branch
    (the two sides are equal), otherwise it is the absorption arm. -/
@[simp] theorem joinTy_absorb (X : Ty) : joinTy (mkNilable X) X = some (mkNilable X) := by
  unfold mkNilable
  by_cases h : X = Ty.nilT
  · subst h; simp [joinTy]
  · simp [joinTy, h, Ne.symm h]

/-- `nilable` is not a fixed point of itself — needed by `joinTy_absorb'`, whose first
    branch has to be refuted at `X` against `nilable X`. One structural induction. -/
theorem ne_nilable_self : ∀ (X : Ty), ¬ (X = .nilable X)
  | .nilable Y => by simpa using ne_nilable_self Y
  | .int | .bool | .nilT | .sym | .cls _ | .any | .clsOf _ | .float
  | .arrayOf _ | .union _ _ | .arrow0 _ | .arrowCons _ _ => by simp

/-- And the once-nested form, which `joinTy_absorb'`'s *first* branch needs refuted.
    Same induction. -/
theorem ne_nilable_self2 : ∀ (X : Ty), ¬ (X = .nilable (.nilable X))
  | .nilable Y => by simpa using ne_nilable_self2 Y
  | .int | .bool | .nilT | .sym | .cls _ | .any | .clsOf _ | .float
  | .arrayOf _ | .union _ _ | .arrow0 _ | .arrowCons _ _ => by simp

@[simp] theorem joinTy_absorb' (X : Ty) : joinTy X (mkNilable X) = some (mkNilable X) := by
  unfold mkNilable
  by_cases h : X = Ty.nilT
  · subst h; simp [joinTy]
  · simp [joinTy, h, Ne.symm h, ne_nilable_self X, ne_nilable_self2 X]

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
      · -- L204's two absorption arms, and each is one clause of `subTy` on each side:
        -- `subTy (.nilable τ) (.nilable τ)` is `subTy`'s second disjunct and
        -- `subTy τ (.nilable τ)` its third.
        split at h
        · rename_i hg
          simp only [beq_iff_eq] at hg
          simp only [Option.some.injEq] at h
          subst h; subst hg
          exact ⟨by simp [subTy], by simp [subTy]⟩
        · split at h
          · rename_i hg
            simp only [beq_iff_eq] at hg
            simp only [Option.some.injEq] at h
            subst h; subst hg
            exact ⟨by simp [subTy], by simp [subTy]⟩
          · exact absurd h (by simp)

/-- Local-variable typing environment. Order is canonical (`envSet` replaces in
    place) so that environment *equality* is a usable check — the `if`-merge and
    the loop-stability condition both need it. -/
abbrev Env := List (String × Ty)

def envGet? (Γ : Env) (x : String) : Option Ty :=
  (Γ.find? (·.1 == x)).map (·.2)

/-- **One environment is weaker than another** (L218): every binding the first records,
    the second records at the same type. A *lower bound* relation, and that direction is
    the one `FrameConforms` needs — it reads `Γ` as "these locals are at least these
    types", so dropping bindings weakens the claim.

    `begin`/`rescue` is what wants it. The region's two exits leave different
    environments — the body may have assigned locals the handler never sees — so the
    type of the whole region can only be stated at an environment **both** paths
    guarantee, which is the entry one. -/
def SubEnv (Γ Γ' : Env) : Prop :=
  ∀ x τ, envGet? Γ x = some τ → envGet? Γ' x = some τ

/-- The decidable form the rule checks.

    **Each entry's *lookup* rather than its payload** (L236), and the difference is
    shadowing: an `Env` is an association list, so `[(x, Int), (x, String)]` is a legal
    value whose second entry is dead. Comparing payloads makes such an environment fail
    `subEnvB Γ Γ` — which is fine for a rule that checks two *different* environments,
    and fatal for `infer_env_mono`, whose conclusion instantiates the guard at an
    arbitrary wider environment. Comparing lookups is reflexive by construction and
    proves the same `SubEnv`. -/
def subEnvB (Γ Γ' : Env) : Bool :=
  Γ.all fun e => envGet? Γ' e.1 == envGet? Γ e.1

theorem subEnvB_sound {Γ Γ' : Env} (h : subEnvB Γ Γ' = true) : SubEnv Γ Γ' := by
  intro x τ hx
  have hx' := hx
  unfold envGet? at hx
  simp only [Option.map_eq_some_iff] at hx
  obtain ⟨e, he, hτ⟩ := hx
  have hp := List.find?_some he
  simp only [beq_iff_eq] at hp
  have := List.all_eq_true.mp h e (List.mem_of_find?_eq_some he)
  simp only [beq_iff_eq] at this
  rw [← hp] at hx' ⊢
  rw [this]; exact hx'

@[simp] theorem subEnvB_refl (Γ : Env) : subEnvB Γ Γ = true :=
  List.all_eq_true.mpr fun _ _ => by simp

/-- A member's key always resolves — the fact `subEnvB`'s lookup form needs to compose
    with `SubEnv`, which speaks about *successful* lookups only. -/
theorem envGet?_of_mem {Γ : Env} {e : String × Ty} (he : e ∈ Γ) :
    ∃ τ, envGet? Γ e.1 = some τ := by
  unfold envGet?
  cases hf : Γ.find? (fun p => p.1 == e.1) with
  | none => exact absurd (List.find?_eq_none.mp hf e he) (by simp)
  | some p => exact ⟨p.2, by simp [hf]⟩

/-- `subEnvB` composes with `SubEnv` on the right. This is the `next` rule's own
    transitivity (L227), restated for the lookup form (L236). -/
theorem subEnvB_trans_sub {Γl Γ Γ₂ : Env} (h : subEnvB Γl Γ = true) (hs : SubEnv Γ Γ₂) :
    subEnvB Γl Γ₂ = true := by
  refine List.all_eq_true.mpr fun e he => ?_
  have h1 := List.all_eq_true.mp h e he
  obtain ⟨τ, hτ⟩ := envGet?_of_mem he
  simp only [beq_iff_eq] at h1 ⊢
  rw [hτ] at h1 ⊢
  exact hs e.1 τ h1

theorem SubEnv.refl (Γ : Env) : SubEnv Γ Γ := fun _ _ h => h

theorem SubEnv.trans {Γ Γ' Γ'' : Env} (h : SubEnv Γ Γ') (h' : SubEnv Γ' Γ'') :
    SubEnv Γ Γ'' := fun x τ hx => h' x τ (h x τ hx)

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
  /-- **The running method's name** (L207), or `none` in a class body and at toplevel.

      `super` is the only rule that needs it, and it needs it for the reason `doSuper`
      does (`Interp/Send.lean:260`): the target is *this method's name*, looked up on
      the chain **after** the definee. `ret`'s channel, one field over, and established
      at the same push — `userFrame` sets `meth := md.superName.getD mname`, which is
      the aliasing-correct name and therefore the one to carry. -/
  meth : Option String := none
  /-- **The running method's declared parameter types** (L214), in order, or `[]` in a
      class body and at toplevel — and `[]` in every activation the invariant can
      currently describe, because `ResolvesUser` requires `md.params = []`.

      `zsuper` is the only rule that needs it, and it needs it because bare `super`
      forwards the enclosing method's *parameter values* (`zsuperArgs` reads them out of
      the frame's locals), so its argument **types** are the parameters' declared types.
      Neither `meth` nor `Γ` can supply them: `Γ` has the locals but nothing says which
      of them are parameters.

      **`Option`, and it mirrors `zsuperArgs`' own `Option`**: that function answers `none`
      when the parameter shape is not reconstructible (a `define_method` body, or
      destructuring parameters whose synthetic slots are dropped after binding), and this
      field answers `none` for exactly the shapes a `zsuper` therefore cannot forward. The
      rule refuses `none` rather than guessing.

      `StackCtx`'s `meth` clause pins it to `some []` in every activation the invariant
      can describe, because `ResolvesUser` requires `md.params = []`. -/
  params : Option (List Ty) := none
  /-- **Are we lexically inside a `while` in this activation?** (L222)

      `next`/`break`/`redo` need it for the reason `return` needed `ret`: the jump has a
      *target*, and the rule is only sound where the target exists. `unwind` sends a `.nxtJ`
      to the innermost `whileCondK`/`whileBodyK`; crossing a **method** boundary answers
      `.unsupported`, which `StepOk` refuses.

      Unlike the other four fields it varies *within* an activation: `infer`'s `.while'` arm
      sets it, `KontOk`'s loop constructors clear it on the way down, and `KontOk.frameK`
      requires it clear on the callee. Free on the nominal side because `Mono.lean` already
      has `ctx` as an induction target; the open side carries the same channel as an explicit
      **parameter** of `inferOpen`, for the reason recorded there.

      **It carries the loop's *environment*, not just a flag** (L224), and that is the one
      way `next` costs more than `return` did. A `return` pops the frame, so `RetOk` owes
      nothing about the environment; a `next` restarts the loop **in the same frame**, and
      the condition is typed at the loop's entry environment while the `next` may fire
      part-way through the body at a richer one. So the rule owes `SubEnv Γloop Γcur`, which
      it can only check if it knows `Γloop` — hence `Option Env` and not `Bool`. -/
  inLoop : Option Env := none
  /-- **Is this activation a block?** (L249) — the sixth channel, and the one the
      *frame* side of Wall 1 turned out to need after all.

      L243 added it, pinned it `false`, and withdrew it in the same commit on the
      grounds that a field no rule sets is a `DecidableEq` cost and an implication with
      one instance. That was right about `FrameConforms`, whose obligation at an
      enclosing local is `ValueTy _ _ .any` and needs nothing about the captured frame
      (L247), and **wrong about `StackCtx`**, which is positional over the same stack and
      whose second clause compares a *heap-derived name* — `className h defmod`, read off
      the frame the closure captured — against the name this context carries. Only the
      pairing connects them, and `KontOk` cannot express a pairing (L249).

      So the clause is guarded on this flag instead: a block activation owes no name, and
      nothing reads one there — the clause's consumers are the `def` row's key and the
      `class'` rule, and a block body may contain neither.

      **`false` in every activation the invariant can currently describe**, and no rule
      sets it; the block-send rule is what will. `infer`'s `def` arm carries the matching
      guard, which refuses nothing today and is what `--check`'s byte-identical diff
      records. -/
  inBlock : Bool := false
deriving DecidableEq, Repr, Inhabited

end RubyCore.Types
