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
deriving DecidableEq, Repr, Inhabited

/-- Local-variable typing environment. Order is canonical (`envSet` replaces in
    place) so that environment *equality* is a usable check — the `if`-merge and
    the loop-stability condition both need it. -/
abbrev Env := List (String × Ty)

def envGet? (Γ : Env) (x : String) : Option Ty :=
  (Γ.find? (·.1 == x)).map (·.2)

def envSet : Env → String → Ty → Env
  | [], x, τ => [(x, τ)]
  | (y, σ) :: Γ, x, τ => if y == x then (x, τ) :: Γ else (y, σ) :: envSet Γ x τ

end RubyCore.Types
