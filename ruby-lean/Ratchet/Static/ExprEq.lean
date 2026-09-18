import Ratchet.Static.Nested

/-!
# `Ratchet/Static/ExprEq.lean`

A structural `Expr` comparator that **kernel-reduces**, which the derived `BEq` does not:
`Expr` is a nested inductive, so its derived instance is compiled by well-founded recursion.
One concern, one file.
-/

namespace Ratchet

/-! ## A structural `Expr` comparator that kernel-reduces

Tier 9 matches a block literal against the whole-program block table **by syntax**
(`closIdx?`), and `Expr`'s derived `BEq` cannot do that job: `Expr` is a *nested* inductive
(`List Expr`, `List (Expr × Expr)`), so the derived instance is compiled by well-founded
recursion and does not reduce in the kernel — which `Ratchet/Rungs.lean`'s per-rung `rfl`
checks and every `closIdx? … = some idx` premise depend on. This is the same fact that made
`Ty`'s arrow and ivar spines spines rather than list payloads; here it shows up on the other
side of the boundary, on syntax this package does not own.

So: hand-written, structurally recursive, with explicit list companions — exactly the shape
`collectBlocks` uses, which does reduce.

**The catch-all is `false`, and that is safe in both directions.** A constructor pair this
function does not cover compares unequal, so two syntactically *identical* blocks built from
uncovered syntax get no shared index — `closIdx?` misses, no rule applies, and the program is
not typed. Conservative. What is *not* possible is a spurious `true`: every covered case
compares every field. Coverage below is the constructors that appear in a block's parameters
or body anywhere in the corpus; the rest are honest omissions rather than a claim. -/

/-- Parameter comparison, **outside** the recursive group on purpose: `Param.opt` carries a
default `Expr`, and pulling `Expr` into this function's recursion would put it back in the
bundle. So an optional parameter compares `false` — conservatively, since a block with one
then has no index and is not typed, and no rung has one. -/
def paramEq : Param → Param → Bool
  | .req a, .req b => a == b
  | .rest a, .rest b => a == b
  | .kwrest a, .kwrest b => a == b
  | .block a, .block b => a == b
  | .fwd, .fwd => true
  | _, _ => false

def paramEqAll : List Param → List Param → Bool
  | [], [] => true
  | a :: as, b :: bs => paramEq a b && paramEqAll as bs
  | _, _ => false

mutual

def exprEq : Expr → Expr → Bool
  | .int a, .int b => a == b
  | .flt a, .flt b => a == b
  | .str a, .str b => a == b
  | .sym a, .sym b => a == b
  | .tru, .tru => true
  | .fls, .fls => true
  | .nil, .nil => true
  | .self', .self' => true
  | .var k a, .var k' b => k == k' && a == b
  | .vasgn k a e, .vasgn k' b e' => k == k' && a == b && exprEq e e'
  | .const a, .const b => a == b
  | .vcall a, .vcall b => a == b
  -- The `Option Expr` fields are matched inline rather than through a helper: an
  -- `Option Expr → Option Expr → Bool` companion is not part of the nested-inductive
  -- bundle Lean builds structural recursion from, and adding one is what pushes this whole
  -- group onto well-founded recursion — at which point it stops reducing in the kernel and
  -- every `rfl` that depends on it fails. Discovered the hard way; see
  -- `../notes/ratchet/implementation-notes.md` clink 9.
  | .send none m as none, .send none m' as' none =>
    m == m' && exprEqAll as as'
  | .send (some r) m as none, .send (some r') m' as' none =>
    exprEq r r' && m == m' && exprEqAll as as'
  | .send none m as (some b), .send none m' as' (some b') =>
    m == m' && exprEqAll as as' && exprEq b b'
  | .send (some r) m as (some b), .send (some r') m' as' (some b') =>
    exprEq r r' && m == m' && exprEqAll as as' && exprEq b b'
  | .block ps ls b, .block ps' ls' b' =>
    paramEqAll ps ps' && ls == ls' && exprEq b b'
  | .yield' as, .yield' as' => exprEqAll as as'
  | .blockpass none, .blockpass none => true
  | .blockpass (some e), .blockpass (some e') => exprEq e e'
  | .if' c t none, .if' c' t' none => exprEq c c' && exprEq t t'
  | .if' c t (some e), .if' c' t' (some e') =>
    exprEq c c' && exprEq t t' && exprEq e e'
  | .def' n ps b, .def' n' ps' b' => n == n' && paramEqAll ps ps' && exprEq b b'
  | .defs r n ps b, .defs r' n' ps' b' =>
    exprEq r r' && n == n' && paramEqAll ps ps' && exprEq b b'
  | .array es, .array es' => exprEqAll es es'
  | .hash ps, .hash ps' => exprEqPairs ps ps'
  | .ret none, .ret none => true
  | .ret (some e), .ret (some e') => exprEq e e'
  | .class' n none b, .class' n' none b' => n == n' && exprEq b b'
  | .class' n (some s) b, .class' n' (some s') b' =>
    n == n' && exprEq s s' && exprEq b b'
  | .module' n b, .module' n' b' => n == n' && exprEq b b'
  | .super' as none, .super' as' none => exprEqAll as as'
  | .super' as (some b), .super' as' (some b') => exprEqAll as as' && exprEq b b'
  | .seq es, .seq es' => exprEqAll es es'
  | _, _ => false

def exprEqAll : List Expr → List Expr → Bool
  | [], [] => true
  | a :: as, b :: bs => exprEq a b && exprEqAll as bs
  | _, _ => false

def exprEqPairs : List (Expr × Expr) → List (Expr × Expr) → Bool
  | [], [] => true
  | (k, v) :: ps, (k', v') :: ps' =>
    exprEq k k' && exprEq v v' && exprEqPairs ps ps'
  | _, _ => false

end

end Ratchet
