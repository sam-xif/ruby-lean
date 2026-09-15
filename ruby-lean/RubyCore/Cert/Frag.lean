import RubyCore.Cert.Check

/-!
# `inferFrag` — the coverage frontier, as a decidable predicate

Split out of `Cert/Check.lean` under §7 norm 3. It is a different concern from the
checker: `chk` says *does this program check*, and this says *is an accept
transferable to the invariant*. `docs/semantics/certificate-language.md` §10.3 is why
that is a `Bool` in the output rather than a caveat in a docstring.
-/

namespace RubyCore.Cert

open RubyCore.Types

/-! ## 5. `inferFrag` — the frontier, as a decidable predicate

**The sound tier's syntactic side**, and the honest half of this whole rewrite.
`chk` has an arm for every head; `Inv` does not. `CtlOk`'s eval clause is
`infer F Γ e … = some …`, so an accept can only be turned into *no reachable
`typeStuck`* where `infer` would have accepted too — and `inferFrag` marks exactly
that sub-grammar, so that the two tiers are told apart by a `Bool` a reader can run
rather than by a convention.

`chk_infer` (`Proof/Cert/Check.lean`) is the theorem this predicate is the
hypothesis of:

```lean
chk c n D Γ e top ctx = some r → inferFrag n e = true → c.claims = [] →
  infer D Γ e top ctx = some r
```

so a head is admitted here **only** when `chk`'s arm and `infer`'s arm are the same
function. Three kinds of head are therefore excluded, and the third is the
interesting one:

1. **`chk` accepts and `infer` has no arm** — `hash`, `defined`, `for'`, `dowhile`,
   `begin'`, `module'`, `defs`, `sclass`, the scoped class/module forms, `casgn`,
   `alias'`, `brk`, `redo'`, `kwargs`, `fwd`, a standalone `splat`, `nxt` with a
   value, a `vasgn` to a class variable, a block-pass send, and a positive-arity
   implicit-self block send. Every one of these is a **preservation case** in
   `Proof/Static/Preservation.lean` away from being admissible, and that is the
   list of work items §10 of the design document records.
2. **`chk` accepts on a claim where `infer` refuses** — excluded by the
   `c.claims = []` hypothesis rather than by this predicate, so no arm here has to
   mention paths.
3. **`chk` *refuses* on a head `infer` also refuses** — these are *admitted*, and
   the reason is that the implication is vacuous: `retry'`, `undef`, `yield'`, a
   bare `block`/`blockpass` node, a class-variable *read*. Admitting them costs
   nothing and keeps the predicate's shape the grammar's rather than a hand-picked
   list, which is what makes it auditable against `infer` arm by arm.

Fuel-bounded like everything else, and refusing when it runs out. -/

/-- The list arm, with the recursive call as a parameter. -/
def fragAll (g : Expr → Bool) : List Expr → Bool
  | [] => true
  | e :: rest => g e && fragAll g rest

/-- Array/argument elements, where a `.splat` is consumed *in place* by `chkElems`
    and `inferElems` alike — so its operand is what has to be in the fragment, and
    the `.splat` node itself is never handed to either checker. -/
def fragElems (g : Expr → Bool) : List Expr → Bool
  | [] => true
  | .splat (some o) :: rest => g o && fragElems g rest
  | e :: rest => g e && fragElems g rest

/-- Is `e` in the sub-grammar on which `chk` and `infer` are the same function? -/
def inferFrag : Nat → Expr → Bool
  | 0, _ => false
  | n + 1, e =>
    match e with
    -- Literals and the immediate reads.
    | .int _ | .flt _ | .str _ | .sym _ | .tru | .fls | .nil | .self' => true
    | .var .lvar _ | .var .ivar _ | .var .gvar _ => true
    -- Admitted vacuously: `chk` refuses a class-variable read with no claim, and
    -- `infer` has no arm for one either.
    | .var .cvar _ => true
    | .vasgn .lvar _ rhs | .vasgn .ivar _ rhs | .vasgn .gvar _ rhs => inferFrag n rhs
    | .const _ => true
    | .cpath none _ => true
    | .cpath (some b) _ => inferFrag n b
    | .vcall _ => true
    -- The send. The block-less shapes are all four of `infer`'s; with a literal
    -- block, a receiver is required unless the argument list is empty (which is the
    -- `lambda` arm, and the one shape where both refuse).
    | .send recvO _ args blkO =>
      (match recvO with | some r => inferFrag n r | none => true) &&
      -- `fragAll` and **not** `fragElems`: an *argument* list hands each element to
      -- `chk`/`infer` directly, so a `.splat` argument is a head `chk` accepts and
      -- `infer` refuses. Only an *array* literal consumes a splat in place. The first
      -- draft had `fragElems` in both positions and it was wrong in this one.
      fragAll (inferFrag n) args &&
      (match blkO with
       | none => true
       -- **A receiver is required**, and `lambda` is why it is not
       -- `recvO.isSome || args.isEmpty`. `infer`'s implicit-self block arm answers
       -- `some (.any, Γ, D)` for `lambda { … }` *without consulting `ctx.selfCls`*,
       -- while `chk` computes the receiver first and so refuses in a class body.
       -- The two therefore disagree at exactly one shape, and admitting it here
       -- would make `chk_infer` false. `lambda` stays in the coverage tier; the
       -- alternative — special-casing it ahead of the receiver in `chk` — buys one
       -- expression and costs the send arm its single shape.
       | some (.block _ _ body) => recvO.isSome && inferFrag n body
       | some _ => false)
    | .super' args blkO =>
      fragAll (inferFrag n) args && (match blkO with | none => true | some _ => false)
    | .zsuper blkO => match blkO with | none => true | some _ => false
    | .array es => fragElems (inferFrag n) es
    | .seq es => fragAll (inferFrag n) es
    | .if' cnd t els =>
      inferFrag n cnd && inferFrag n t &&
        (match els with | some el => inferFrag n el | none => true)
    | .while' cnd body => inferFrag n cnd && inferFrag n body
    | .ret eo => match eo with | some e' => inferFrag n e' | none => true
    | .nxt none => true
    -- **`defFreeF` is a *fragment* condition and not just a rule condition**, which
    -- the first draft got wrong. `infer`'s promotion guard reads `defFree body` and
    -- `chk`'s reads `defFreeF n body`, and those two are related by *implication*
    -- only (V13): at low fuel `defFreeF` is `false` where `defFree` is `true`. So
    -- without this conjunct the two checkers can take *different branches* of the
    -- promotion — one threading a row and one not — and `chk_infer` is false, in the
    -- `else` branch where nothing looks wrong. Demanding it here makes the guard's
    -- `defFree` component `true` on both sides, so the branches agree.
    --
    -- The population it costs is a `def` whose body contains a nested `def` or
    -- `class`. `infer` accepts one only when it does not promote, so the loss is the
    -- non-promoting corner of an already narrow arm; recorded rather than measured
    -- because the slice has no instance.
    | .def' _ ps body => ps.isEmpty && defFreeF n body && inferFrag n body
    | .class' _ none body => inferFrag n body
    -- Admitted vacuously: both checkers refuse.
    | .retry' | .undef _ => true
    | .block _ _ _ | .blockpass _ => true
    | .yield' _ => true
    -- Everything else is a head `chk` can accept and `Inv` cannot yet carry.
    | _ => false

end RubyCore.Cert
