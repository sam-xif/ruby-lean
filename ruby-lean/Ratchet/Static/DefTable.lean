import Ratchet.Static.Predicates

/-!
# `Ratchet/Static/DefTable.lean`

`Defn`/`DefTable` — a top-level `def` as the checker remembers it. Split out from the
lookup functions below because the *shape* of the table is what `Ctx` and
`Denote/Sem/Core/State.lean`'s conformance statements mention; the lookups are
`Ratchet/Static/Lookup.lean`.
-/

namespace Ratchet

/-! ## Tier 6's two tables

A top-level `def` puts a *method* into the world, and nothing in `Env` can hold one: a
method has parameters and a body, not a type. So tier 6 adds two tables beside `Env`, and
they are as different from each other as they are from `Env`.

`DefTable` is **syntax the checker has seen**; `AsmTable` is **a claim the checker is in
the middle of discharging**. Neither is trusted, but for opposite reasons: the first
because it is read straight off the program, the second because the only rule that adds to
it also proves it. -/

/-- One top-level method definition, as the checker sees it: a name, a parameter list and
a body — no types anywhere, because none are written in Ruby. -/
structure Defn where
  name : String
  params : List Param
  body : Expr

/-- The methods **already defined at this point in evaluation order**.

The "already" is a soundness requirement, not bookkeeping. Collecting every `def` in the
program up front would certify `foo(); def foo; end`, which raises `NoMethodError` — the
headline member of the family this ladder calls type-stuck. So `D` is threaded through
`JudgeSeq` (see `extendDefs`) exactly the way `Env` is threaded through everything, and a
call can only see a `def` that a *preceding* statement performed.

Note what that costs and does not cost: a `def` inside an `if` branch never reaches the
table (`extendDefs` looks only at a statement head), so a program that calls such a method
is simply not typed. Conservative, and no rung asks for it. What it does *not* cost is
forward reference **inside a body**: `def twice(x) = inc(inc(x))` type-checks against
whatever `D` holds at the *call site* of `twice`, which is after every top-level `def` has
run — so source order between two `def`s is irrelevant (rung `fun-calling-another-fun`),
while source order between a `def` and a call is not. -/
abbrev DefTable := List Defn

end Ratchet
