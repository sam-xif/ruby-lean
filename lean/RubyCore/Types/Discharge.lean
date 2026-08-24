import RubyCore.Types.Assn

/-!
# L262 — discharge: where the program's own `def`s meet its own requirements

`inferOpen` records a *requirement* every time a body calls a method on a receiver
whose type is still a variable — `α ~ value : () → β` for the `vcall` in
`def hash; value.hash; end`. Nothing has ever discharged one, because nothing has
ever recorded the other half: `α_C ▷ value : () → Integer`, the row that `class C`'s
*own* `def value; 1; end` supplies.

The whole-program pass (`Types/Program.lean`) records both, at one variable per class,
in one store. This file is the cancellation:

```
Σ = { α ~ value : () → β }  ∪  { α ▷ value : () → Integer }
discharge Σ  =  { β = Integer }
```

and the point is the *shape* of the answer. A program whose classes supply everything
their own bodies ask for closes to `emp` — an unconditional whole-program accept —
while `class Foo < Formula; def install; system "make"; end; end` closes to
`Foo ⊒ ⟨ system : (String) → … ⟩`, which is the honest statement that `Formula` (which
no table describes) must declare it.

## The direction it is allowed to be wrong in

`discharge` **drops requirements**, so its whole soundness content is that a dropped
one was really met. That is `Proof/Static/Discharge.lean`:

```
SatStore D θ (discharge st)  →  SatProvs D θ st  →  SatStore D θ st
```

*A substitution satisfying the discharged store, at a program whose provisions hold,
satisfies the original.* The second premise is not free and this file does not pretend
it is: a provision holds iff the class really does define the method at that signature,
which is a fact about the heap, not about `θ`. `Types/Program.lean` is what has to
supply it — the provision it records comes from the `def` that installs the method.

Everything here is therefore built to be **conservative in one direction**: when the
constraint that would justify a cancellation cannot be *stated*, the requirement is
kept. A kept requirement is a weaker output, never a wrong one.

## Three places it refuses to cancel, each for a stated reason

* **A pair of types neither of which is a variable.** `pinPair` can equate `α` with
  anything, either way round, because `θ α = τ.subst θ` is exactly an `eqv` atom. Two
  *nominal* types that differ are not equatable by any `θ`, and pinning them would be
  a claim the assertion language cannot make; refusing keeps the requirement.
* **An arity disagreement.** `pinPairs` is length-indexed and answers `none` on a
  mismatch. A `def` with optional or keyword parameters accepts a *range* of arities
  and `ASig` records one, so `Types/Program.lean` records no provision for such a
  `def` at all — which means this case fires only on a genuine caller/callee
  disagreement.
* **Two `def`s of one name at different signatures.** That is `addProv`'s ★★, upstream
  of here: no provision is recorded, so there is nothing to cancel against.
-/

namespace RubyCore.Types

/-! ## 1. Pinning one pair of types -/

/-- **The constraint that makes `a` and `b` interchangeable under `θ`**, or `none` when
    there is none to state.

    Three cases and they are `Store.joinOpen`'s, minus the join: syntactic equality needs
    nothing; a variable on either side is pinned to the other; anything else is refused.
    The output is the *list of equalities to record* rather than a store, so that the
    traversals below can be folded without threading rows they do not touch — which is
    what makes the eqs-monotonicity step of the soundness proof `List.mem_append`. -/
def pinPair (a b : ATy) : Option (List (TyVar × ATy)) :=
  if a == b then some []
  else
    match a, b with
    | .var α, _ => some [(α, b)]
    | _, .var β => some [(β, a)]
    | _, _ => none

/-- Pointwise, over two argument lists. Length-indexed: a mismatch is `none`, which is
    the arity disagreement the header's second bullet is about. -/
def pinPairs : List ATy → List ATy → Option (List (TyVar × ATy))
  | [], [] => some []
  | a :: as, b :: bs =>
    match pinPair a b with
    | some e =>
      match pinPairs as bs with
      | some es => some (e ++ es)
      | none => none
    | none => none
  | _, _ => none

/-- **The requirement, against the provision.** `σ` is what a call site asked for and
    `σp` what the `def` supplies; the answer is the equalities under which the two are
    the same signature.

    Parameters *and* return, because `SatStore`'s row clause obliges the whole
    signature: `sigOf D (θ α) n = some (σ.params.map (·.subst θ), σ.ret.subst θ)`, and
    the provision gives that equation at `σp`. So both components have to be pinned or
    neither. -/
def dischargeSig (σ σp : ASig) : Option (List (TyVar × ATy)) :=
  match pinPairs σ.params σp.params with
  | some es =>
    match pinPair σ.ret σp.ret with
    | some e => some (es ++ e)
    | none => none
  | none => none

/-! ## 2. One variable's row, then the store -/

/-- Walk one variable's requirement entries against its provisions. Returns the
    equalities the cancellations owe and the entries that **survive**.

    Order is preserved in the kept list, which is the fact the soundness proof needs at
    the entries `discharge` does *not* drop: `Row.get?` is a `find?`, so a kept entry is
    still the first of its name exactly when it was before. -/
def dischargeEntries (provR : Row) :
    List (String × ASig) → List (TyVar × ATy) × List (String × ASig)
  | [] => ([], [])
  | (n, σ) :: rest =>
    -- **`let r := …` and then `r.1`/`r.2`, not `let (es, keep) := …`** — a destructuring
    -- `let` elaborates to a `match`, and every lemma in
    -- `Proof/Static/Discharge.lean` would have to push a motive through it. The
    -- projections reduce.
    let r := dischargeEntries provR rest
    match provR.get? n with
    | some σp =>
      match dischargeSig σ σp with
      | some e => (e ++ r.1, r.2)
      | none => (r.1, (n, σ) :: r.2)
    | none => (r.1, (n, σ) :: r.2)

/-- Every variable's, over the `rows` association list.

    **Keys are preserved and duplicates are kept.** `setRow` prepends rather than
    replaces, so `rows` may carry `α` twice and `rowIn` reads the first; mapping each
    pair to the same key keeps that first entry first, which is what lets the proof
    reduce a lookup in the output to `dischargeEntries` of the lookup in the input. -/
def dischargeRows (P : List (TyVar × Row)) :
    List (TyVar × Row) → List (TyVar × ATy) × List (TyVar × Row)
  | [] => ([], [])
  | (α, R) :: rest =>
    let d := dischargeEntries (Store.rowIn P α) R.entries
    let r := dischargeRows P rest
    (d.1 ++ r.1, (α, { R with entries := d.2 }) :: r.2)

/-- **The pass.** Requirements the program's own `def`s answer are replaced by the
    equalities that answering them owes.

    `provs` is carried through untouched: it is what the *program* supplies, a fact about
    the program and not a residue of this computation, and `Types/Program.lean` reads it
    again to print the per-class ledger. -/
def discharge (st : Store) : Store :=
  { st with rows := (dischargeRows st.provs st.rows).2,
            eqs := st.eqs ++ (dischargeRows st.provs st.rows).1 }

/-! ## 3. Examples — the three shapes the header names

Kept in the build rather than in a test file, for the reason every `example` in
`Types/OpenSelf.lean` is: a capability asserted by a number in a report is a capability
that can rot silently. **`decide`, not `native_decide`** — `PLAN.md` §4 norm 5 bans the
latter above a per-program leaf, and the kernel reduces these: a four-field record, a
`find?` over two entries, and `String.decEq`. -/

/-- `def get; value; end` beside `def value; 1; end`, both on the same class variable:
    the requirement cancels and what is left is the equality it owed. -/
example :
    discharge { rows := [(0, { entries := [("value", { params := [], ret := .var 1 })] })],
                provs := [(0, { entries := [("value", { params := [], ret := .nom .int })] })] }
      = { rows := [(0, { entries := [] })],
          eqs := [(1, .nom .int)],
          provs := [(0, { entries := [("value", { params := [], ret := .nom .int })] })] } := by
  decide

/-- **Nothing supplies it**, which is the `Formula` case: the requirement survives
    verbatim, and `closeAt` will turn it into `Foo ⊒ ⟨ … ⟩`. -/
example :
    discharge { rows := [(0, { entries := [("system", { params := [.nom (.cls "String")],
                                                        ret := .var 1 })] })] }
      = { rows := [(0, { entries := [("system", { params := [.nom (.cls "String")],
                                                  ret := .var 1 })] })] } := by
  decide

/-- **An arity disagreement is not cancelled.** The provision is `() → Integer` and the
    call passed one argument, so `pinPairs` refuses and the requirement stands — the
    output says the class must declare `value` at the arity the *caller* used, which is
    the honest reading of a program that will `ArgumentError`. -/
example :
    discharge { rows := [(0, { entries := [("value", { params := [.nom .int],
                                                       ret := .var 1 })] })],
                provs := [(0, { entries := [("value", { params := [], ret := .nom .int })] })] }
      = { rows := [(0, { entries := [("value", { params := [.nom .int], ret := .var 1 })] })],
          provs := [(0, { entries := [("value", { params := [], ret := .nom .int })] })] } := by
  decide

end RubyCore.Types
