import Ratchet.Static.ExprEq

/-!
# `Ratchet/Static/Closures.lean`

Tier 9's **block table**: `Clos`/`ClosTable` and `collectBlocks`. What `Ty.clos`'s index
refers to, which is why a callable's type is a reference rather than an arrow.
-/

namespace Ratchet

/-! ## Tier 9's block table

`Ty.clos` says why a callable's type is a *reference* rather than an arrow. This is what it
refers to. -/

/-- One block literal the program contains. `locals` (a `|x; y|` block-local list) is not
recorded because no rule admits a block that has any — see `Judge.lambdaLit`. -/
structure Clos where
  params : List Param
  body : Expr

abbrev ClosTable := List Clos

/-- The index of a block literal in the table, matched **by syntax**.

Syntax equality is `exprEq`, not `==`: the derived instance does not kernel-reduce (see
above). Syntactically identical blocks therefore share an index, and that is fine rather than
tolerated: an entry is only `(params, body)`, so two blocks that agree on both are
interchangeable *here*. What distinguishes two instances of the same block literal is the
environment each captured, and that lives in `Ty.clos`'s second argument, not in this
table. -/
def closIdxAux (k : Nat) : ClosTable → List Param → Expr → Option Nat
  | [], _, _ => none
  | c :: cs, ps, b =>
    if paramEqAll c.params ps && exprEq c.body b then some k
    else closIdxAux (k + 1) cs ps b

def closIdx? (K : ClosTable) (ps : List Param) (b : Expr) : Option Nat :=
  closIdxAux 0 K ps b

/-- The closure a call rule may type against. Same guard as `defGet?` and for the same reason
(`found-issues.md` §F3): `closCall`, `iterClosPass` and `yieldExpr` all type `c.body` and then
conclude at the caller's `κ`, so a block body containing a `def` would carry a stale table out
of the call. A block whose body declares still gets a `Ty.clos` from `lambdaLit` — the type says
nothing about the tables — it just cannot be *called* by this checker. -/
def closGet? (K : ClosTable) (k : Nat) : Option Clos :=
  match K[k]? with
  | some c => if declFree c.body then some c else none
  | none => none

mutual

/-- Every block literal in the program, collected **before checking starts** so that
`Ctx.closures` is a constant and `Ty.clos`'s index means the same thing everywhere.

This is why tier 9 needed no fourth piece of threaded state: the alternative — allocating an
index when a lambda expression is reached — makes the table grow mid-expression, and then a
`Ty.clos k` would only be meaningful relative to a table that is still changing.

Coverage is the constructors that can contain a block in this corpus. **Anything unlisted
simply does not get its blocks registered**, so a lambda written there has no index, no rule
applies, and the program is not typed — conservative, and the failure is a rejection rather
than a wrong index. -/
def collectBlocks : Expr → ClosTable
  | .block ps _ body => ⟨ps, body⟩ :: collectBlocks body
  | .send recv _ args blk =>
    (match recv with | some r => collectBlocks r | none => []) ++
    collectBlocksAll args ++
    (match blk with | some b => collectBlocks b | none => [])
  | .seq es => collectBlocksAll es
  | .vasgn _ _ e => collectBlocks e
  | .def' _ _ body => collectBlocks body
  | .defs _ _ _ body => collectBlocks body
  | .class' _ _ body => collectBlocks body
  | .module' _ body => collectBlocks body
  | .array es => collectBlocksAll es
  | .hash ps => collectBlocksPairs ps
  | .if' c t e =>
    collectBlocks c ++ collectBlocks t ++
    (match e with | some x => collectBlocks x | none => [])
  | .yield' args => collectBlocksAll args
  | .blockpass (some e) => collectBlocks e
  | .super' args blk =>
    collectBlocksAll args ++ (match blk with | some b => collectBlocks b | none => [])
  | .ret (some e) => collectBlocks e
  | _ => []

def collectBlocksAll : List Expr → ClosTable
  | [] => []
  | e :: es => collectBlocks e ++ collectBlocksAll es

def collectBlocksPairs : List (Expr × Expr) → ClosTable
  | [] => []
  | (k, v) :: ps => collectBlocks k ++ collectBlocks v ++ collectBlocksPairs ps

end

end Ratchet
