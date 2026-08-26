import RubyCore.Types.Assn

/-!
# `exprEq` — structural equality on syntax, on fuel (V16)

One concern, one file (§7 norm 3), and the concern is narrow: **a claim is keyed on
the subterm it is about** (V15), so `Cert.claimAt` needs to compare two `Expr`s, and
it needs to do so *in the kernel* because the whole point of `chk` is that `validate`
is one `decide` (V9).

`deriving BEq for Expr` does not do that. Measured:

```lean
example : ((.int 1 : Expr) == (.int 1)) = true := by decide   -- FAILS
```

`Expr` is a **nested** inductive (`List Expr`, `List Param`, `List (Expr × Expr)`,
the `rescues` triple), so the derived `BEq` compiles to well-founded recursion and
kernel reduction gets stuck on it — the same trap that caught `infer`, `findDef`,
`bindParams` and `defFree` in turn. The fix is the same one: recurse on a `Nat`.

The derived instance is kept (`RubyCore/Syntax.lean`) because it is the right thing
for `#guard`s, tests and anything running compiled; nothing on the checked path uses
it. **Fuel exhaustion answers `false`**, i.e. *not equal*, so a claim on a subterm
deeper than the fuel is simply not found — which refuses, the safe direction every
other fuel bound in this initiative fails in.
-/

namespace RubyCore.Cert

open RubyCore.Types

/-! ## 1. The two generic combinators

Taking the element comparison as a parameter, so each recurses on its own list and
never has to decrease together with the fuel. -/

def listEq {α : Type} (f : α → α → Bool) : List α → List α → Bool
  | [], [] => true
  | a :: as, b :: bs => f a b && listEq f as bs
  | _, _ => false

def optEq {α : Type} (f : α → α → Bool) : Option α → Option α → Bool
  | none, none => true
  | some a, some b => f a b
  | _, _ => false

/-! ## 2. Parameters and keyword-argument entries

`Param` is itself nested (`.destr` carries a `List Param`), so it gets its own fuel;
`KwEntry` is not, so it takes the expression comparison and nothing else. -/

def paramEq (f : Expr → Expr → Bool) : Nat → Param → Param → Bool
  | 0, _, _ => false
  | m + 1, a, b =>
    match a, b with
    | .req x, .req y => x == y
    | .opt x dx, .opt y dy => x == y && f dx dy
    | .rest x, .rest y => x == y
    | .key x dx, .key y dy => x == y && optEq f dx dy
    | .kwrest x, .kwrest y => x == y
    | .block x, .block y => x == y
    | .fwd, .fwd => true
    | .destr xs, .destr ys => listEq (fun p q => paramEq f m p q) xs ys
    | _, _ => false

def kwEntryEq (f : Expr → Expr → Bool) : KwEntry → KwEntry → Bool
  | .pair k v, .pair k' v' => k == k' && f v v'
  | .dyn k v, .dyn k' v' => f k k' && f v v'
  | .splat a, .splat b => f a b
  | _, _ => false

/-! ## 3. `exprEq`

An arm per pair of *matching* heads, and a single catch-all for the rest — which is
the one place in this initiative a catch-all is right, because the catch-all here
says *different heads are different terms* rather than *this head is unsupported*. -/

def exprEq : Nat → Expr → Expr → Bool
  | 0, _, _ => false
  | n + 1, a, b =>
    let ee := exprEq n
    let el := listEq ee
    let eo := optEq ee
    match a, b with
    | .int x, .int y => x == y
    -- `Float` has `BEq` and no `DecidableEq`, which is the whole reason `Cert`
    -- derives `BEq` rather than `DecidableEq`. Two `NaN` literals compare unequal;
    -- a claim on one is not found, which refuses.
    | .flt x, .flt y => x == y
    | .str x, .str y => x == y
    | .sym x, .sym y => x == y
    | .tru, .tru => true
    | .fls, .fls => true
    | .nil, .nil => true
    | .self', .self' => true
    | .var k x, .var k' x' => k == k' && x == x'
    | .vasgn k x r, .vasgn k' x' r' => k == k' && x == x' && ee r r'
    | .const x, .const y => x == y
    | .casgn x r, .casgn y r' => x == y && ee r r'
    | .cpath bx x, .cpath by' y => eo bx by' && x == y
    | .cpathAsgn bx x r, .cpathAsgn by' y r' => eo bx by' && x == y && ee r r'
    | .send r m as bl, .send r' m' as' bl' =>
      eo r r' && m == m' && el as as' && eo bl bl'
    | .vcall m, .vcall m' => m == m'
    | .kwargs es, .kwargs es' => listEq (kwEntryEq ee) es es'
    | .fwd, .fwd => true
    | .block ps ls bd, .block ps' ls' bd' =>
      listEq (fun p q => paramEq ee n p q) ps ps' && ls == ls' && ee bd bd'
    | .yield' as, .yield' as' => el as as'
    | .blockpass x, .blockpass y => eo x y
    | .if' c t e, .if' c' t' e' => ee c c' && ee t t' && eo e e'
    | .while' c bd, .while' c' bd' => ee c c' && ee bd bd'
    | .dowhile bd c, .dowhile bd' c' => ee bd bd' && ee c c'
    | .for' ts co bd, .for' ts' co' bd' => ts == ts' && ee co co' && ee bd bd'
    | .def' nm ps bd, .def' nm' ps' bd' =>
      nm == nm' && listEq (fun p q => paramEq ee n p q) ps ps' && ee bd bd'
    | .array es, .array es' => el es es'
    | .hash ps, .hash ps' => listEq (fun p q => ee p.1 q.1 && ee p.2 q.2) ps ps'
    | .splat x, .splat y => eo x y
    | .ret x, .ret y => eo x y
    | .brk x, .brk y => eo x y
    | .nxt x, .nxt y => eo x y
    | .retry', .retry' => true
    | .redo', .redo' => true
    | .class' nm su bd, .class' nm' su' bd' => nm == nm' && eo su su' && ee bd bd'
    | .module' nm bd, .module' nm' bd' => nm == nm' && ee bd bd'
    | .scopedClass ba nm bd, .scopedClass ba' nm' bd' =>
      eo ba ba' && nm == nm' && ee bd bd'
    | .scopedModule ba nm bd, .scopedModule ba' nm' bd' =>
      eo ba ba' && nm == nm' && ee bd bd'
    | .sclass ob bd, .sclass ob' bd' => ee ob ob' && ee bd bd'
    | .defs r nm ps bd, .defs r' nm' ps' bd' =>
      ee r r' && nm == nm' && listEq (fun p q => paramEq ee n p q) ps ps' && ee bd bd'
    | .begin' bd rs el' en, .begin' bd' rs' el'' en' =>
      ee bd bd' &&
        listEq (fun x y => el x.1 y.1 && x.2.1 == y.2.1 && ee x.2.2 y.2.2) rs rs' &&
        eo el' el'' && eo en en'
    | .super' as bl, .super' as' bl' => el as as' && eo bl bl'
    | .zsuper bl, .zsuper bl' => eo bl bl'
    | .undef ns, .undef ns' => ns == ns'
    | .alias' nw od, .alias' nw' od' => nw == nw' && od == od'
    | .defined x, .defined y => ee x y
    | .seq es, .seq es' => el es es'
    | _, _ => false

/-! ## 4. Checked facts

The measurement this file exists for, as a test rather than a comment. -/

example : exprEq 8 (.int 1) (.int 1) = true := by decide
example : exprEq 8 (.int 1) (.int 2) = false := by decide
example : exprEq 8 (.seq [.int 1, .str "a"]) (.seq [.int 1, .str "a"]) = true := by decide
example : exprEq 8 (.seq [.int 1]) (.array [.int 1]) = false := by decide

/-- A nested term, to exercise the fuel: `if true then 1 else :s end`. -/
example : exprEq 8 (.if' .tru (.int 1) (some (.sym "s")))
    (.if' .tru (.int 1) (some (.sym "s"))) = true := by decide

/-- **Too little fuel is inequality, not equality** — the safe direction. -/
example : exprEq 1 (.seq [.int 1]) (.seq [.int 1]) = false := by decide

/-- Parameters, including the nested `destr` arm that is why `paramEq` has its own
    fuel. -/
example :
    exprEq 8 (.def' "f" [.destr [.req "a", .req "b"]] (.int 1))
      (.def' "f" [.destr [.req "a", .req "b"]] (.int 1)) = true := by decide

end RubyCore.Cert
