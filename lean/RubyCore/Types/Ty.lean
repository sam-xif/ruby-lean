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
deriving DecidableEq, Repr, Inhabited

/-- **Subtyping, and it is exactly one rule wide** (L183): everything is below
    `any`, and otherwise types are compared by equality as they always were.

    Used *only* where a declared parameter is compared against an argument's type —
    `infer`'s send rules, `KontOk.recvK`/`argsK`'s premises, and `ValuesTy`. Not on
    the value judgement, and not on the `if` join: a join needs a *least upper
    bound*, which is the unions rung and a different statement. -/
def subTy (σ τ : Ty) : Bool := τ == .any || σ == τ

/-- Pointwise, at the arity the signature declares. A length mismatch is `false`,
    which is what keeps the arity check that used to be list equality. -/
def subTys : List Ty → List Ty → Bool
  | [], [] => true
  | σ :: σs, τ :: τs => subTy σ τ && subTys σs τs
  | _, _ => false

@[simp] theorem subTy_refl (τ : Ty) : subTy τ τ = true := by simp [subTy]

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

/-- **At a concrete parameter, `subTy` *is* equality** — the lemma that makes the
    weakening inert: every row in `baseDecls` has concrete parameters, so their
    conformance obligations see the proposition they always saw. -/
theorem subTy_concrete {σ τ : Ty} (hτ : τ ≠ .any) : subTy σ τ = true ↔ σ = τ := by
  unfold subTy
  cases τ <;> simp_all

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
deriving DecidableEq, Repr, Inhabited

end RubyCore.Types
