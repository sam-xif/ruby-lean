import Ratchet.Static.DefTable

/-!
# `Ratchet/Static/Purity.lean`

The **syntactic freedom predicates** — `declFree`, `nxtFree`, `asgnFree`, `nxtPrefixOk`.
Each answers "does this expression avoid a construct some rule's premise cannot survive",
and each was added because a rule without it was *unsound*: §F3 for declarations in a body,
§F23 for a `next` escaping past an assignment. They are pure syntax, over `Expr` alone.
-/

namespace Ratchet

/-! ### A body that declares (`found-issues.md` §F3)

`Ctx` describes *declarations* — `defs`, `classes`, `consts` — and every rule that types a
**call** concludes at the same `κ` it started from. That is a promise that running the body
leaves those tables describing the heap, and a body containing a `def` breaks it: the `def`
executes, `Heap.defineMethod` **replaces**, and the caller's table now names a method the
heap no longer has. `def bar; 1; end; def foo; def bar; "s"; end; 1; end; foo; bar + 1` was
certified `Integer` and raises `TypeError` in CRuby *and* in the model.

The fix is at the **lookup**, not at the rules, and that is worth a sentence because it is what
made it a five-line change instead of a premise on twenty rules: a rule can only type a call by
first *fetching the body* — `defGet?` for a top-level method, `defGet? c.methods` for an
instance method (the same function, `mroGet?` included), `closGet?` for a Proc or a block a
method may `yield`. Filter there and every call rule inherits the guard, with no premise added,
no derivation term moved and no `chk_sound` case touched.

What it costs is precision, exactly once: a method whose body declares becomes **uncallable by
this checker** rather than callable-and-wrong. Nothing else can reach it either — typing a body
requires a rule for every statement in it, so a method that merely *calls* the unrecordable one
is rejected in turn, and `define_method` has no rule at all.

The alternative, recorded because it is where this should end up: thread the context through the
judgment (`Judge κ Γ I e τ Γ' I' κ'`), which fixes this *and* `Judge.defStmt`'s false semantic
obligation (`Denote/Sem/notes.md` §The sixth stall point). That is a change to every derivation
on file and wants its own clink. -/

mutual

/-- Does this expression contain no **declaration** — no `def`, no `class`/`module`/`sclass`, no
constant assignment, no `undef`/`alias`?

Written as its own structural recursion (mutual with the list and pair walkers) rather than with
`List.all`, for `collectBlocks`' reason and `exprEq`'s: a helper outside the nested-inductive
bundle pushes the group onto well-founded recursion, and then it stops reducing in the kernel —
which every `rfl`-discharged `defGet? … = some d` premise in `Rungs.lean` depends on.

Parameters are **not** walked, and that is a known gap rather than an omission: a default
expression (`def f(x = (def bar; end; 1))`) is evaluated in the callee frame and could declare.
No rung writes one, walking `Param` would put a third inductive in the recursion bundle, and the
gap is recorded here so the fix has somewhere to start. -/
def declFree : Expr → Bool
  -- the declarations themselves
  | .def' .. | .defs .. | .casgn .. | .cpathAsgn .. => false
  | .class' .. | .module' .. | .scopedClass .. | .scopedModule .. | .sclass .. => false
  | .undef .. | .alias' .. => false
  -- containers
  | .vasgn _ _ e | .splat (some e) | .ret (some e) | .brk (some e) | .nxt (some e)
  | .blockpass (some e) | .cpath (some e) _ | .defined e => declFree e
  | .send recv _ args blk =>
    (match recv with | some r => declFree r | none => true) &&
    declFreeAll args &&
    (match blk with | some b => declFree b | none => true)
  | .block _ _ body => declFree body
  | .seq es | .array es | .yield' es => declFreeAll es
  | .hash ps => declFreePairs ps
  | .kwargs entries => declFreeKw entries
  | .if' c t e =>
    declFree c && declFree t && (match e with | some x => declFree x | none => true)
  | .while' c body => declFree c && declFree body
  | .dowhile body cond => declFree body && declFree cond
  | .for' _ coll body => declFree coll && declFree body
  | .begin' body rescues els ens =>
    declFree body && declFreeRescues rescues &&
    (match els with | some x => declFree x | none => true) &&
    (match ens with | some x => declFree x | none => true)
  | .super' args blk =>
    declFreeAll args && (match blk with | some b => declFree b | none => true)
  | .zsuper blk => (match blk with | some b => declFree b | none => true)
  -- leaves
  | .int _ | .flt _ | .str _ | .sym _ | .regexpLit .. | .tru | .fls | .nil | .self'
  | .var .. | .const _ | .vcall _ | .fwd | .retry' | .redo'
  | .cpath none _ | .splat none | .ret none | .brk none | .nxt none
  | .blockpass none => true

def declFreeAll : List Expr → Bool
  | [] => true
  | e :: es => declFree e && declFreeAll es

def declFreePairs : List (Expr × Expr) → Bool
  | [] => true
  | (k, v) :: ps => declFree k && declFree v && declFreePairs ps

def declFreeKw : List KwEntry → Bool
  | [] => true
  | .pair _ v :: es => declFree v && declFreeKw es
  | .dyn k v :: es => declFree k && declFree v && declFreeKw es
  | .splat e :: es => declFree e && declFreeKw es

def declFreeRescues :
    List (List Expr × Option (TargetKind × String) × Expr) → Bool
  | [] => true
  | (cls, _, handler) :: rs => declFreeAll cls && declFree handler && declFreeRescues rs

end

/-! ### `next` may not escape past an assignment — §F23

**A reachable soundness bug, found by reading `Judge.while'`'s semantic obligation** and
confirmed against CRuby (`corpus/…-while-next-escapes-unsafe`, `…-iter-block-next-escapes-unsafe`;
`found-issues.md` §F23). Both `Judge.while'` and `Judge.iterBlock` constrain the body's
**outgoing** environment — `Γb = Γ` for the loop, `capIntact … Γb'` for the block — and a `next`
leaves the iteration **mid-body**, at an environment neither premise mentions. So

```ruby
i = 0; x = 1
while i < 2
  i = i + 1; x = "s"
  next if i == 2
  x = 2
end
x + 1                     # x is "s": TypeError, and `validate` said Integer
```

was certified. The premise was being checked at the wrong point.

The fix is the conservative one the shape allows: **a `next` may only occur before anything has
assigned**, and then the environment at the escape *is* the body's incoming one, which is exactly
what the outgoing premise already pins. It keeps every climbed rung (`ctl-next`'s `next if x == 2`
is the body's first statement) and rejects both witnesses.

Recorded limitation, and it is `found-issues.md` §F13's: `noLocalAsgn` is **syntactic**, so a
`next` after a call to a closure that assigns a captured local is still accepted. That hole is
the fifteenth stall point's and is not made worse here. -/

mutual

/-- Does this expression contain no `next` that would escape to *this* body? A nested block,
loop or definition is a boundary: a `next` inside one belongs to it, not to us. -/
def nxtFree : Expr → Bool
  -- the escape itself
  | .nxt _ => false
  -- boundaries: an inner `next` belongs to the inner construct
  | .block .. | .def' .. | .defs .. | .class' .. | .module' .. => true
  | .scopedClass .. | .scopedModule .. | .sclass .. => true
  | .for' .. | .dowhile .. => true
  | .while' c _ => nxtFree c
  -- containers
  | .vasgn _ _ e | .splat (some e) | .ret (some e) | .brk (some e)
  | .blockpass (some e) | .cpath (some e) _ | .defined e | .casgn _ e
  | .cpathAsgn _ _ e => nxtFree e
  | .send recv _ args blk =>
    (match recv with | some r => nxtFree r | none => true) &&
    nxtFreeAll args &&
    (match blk with | some b => nxtFree b | none => true)
  | .seq es | .array es | .yield' es => nxtFreeAll es
  | .hash ps => nxtFreePairs ps
  | .kwargs entries => nxtFreeKw entries
  | .if' c t e =>
    nxtFree c && nxtFree t && (match e with | some x => nxtFree x | none => true)
  | .begin' body rescues els ens =>
    nxtFree body && nxtFreeRescues rescues &&
    (match els with | some x => nxtFree x | none => true) &&
    (match ens with | some x => nxtFree x | none => true)
  | .super' args blk =>
    nxtFreeAll args && (match blk with | some b => nxtFree b | none => true)
  | .zsuper blk => (match blk with | some b => nxtFree b | none => true)
  -- leaves
  | .int _ | .flt _ | .str _ | .sym _ | .regexpLit .. | .tru | .fls | .nil | .self'
  | .var .. | .const _ | .vcall _ | .fwd | .retry' | .redo'
  | .cpath none _ | .splat none | .ret none | .brk none
  | .undef .. | .alias' .. | .blockpass none => true

def nxtFreeAll : List Expr → Bool
  | [] => true
  | e :: es => nxtFree e && nxtFreeAll es

def nxtFreePairs : List (Expr × Expr) → Bool
  | [] => true
  | (k, v) :: ps => nxtFree k && nxtFree v && nxtFreePairs ps

def nxtFreeKw : List KwEntry → Bool
  | [] => true
  | .pair _ v :: es => nxtFree v && nxtFreeKw es
  | .dyn k v :: es => nxtFree k && nxtFree v && nxtFreeKw es
  | .splat e :: es => nxtFree e && nxtFreeKw es

def nxtFreeRescues :
    List (List Expr × Option (TargetKind × String) × Expr) → Bool
  | [] => true
  | (cls, _, handler) :: rs => nxtFreeAll cls && nxtFree handler && nxtFreeRescues rs

end

mutual

/-- Does this expression **assign no local**? Unlike `noLocalAsgn` — which is a whitelist of
shapes a *narrowing condition* may take, and answers `false` for anything it does not
recognise, `next` included — this is the honest question: is there a `vasgn` (or a `for`
target, or a block body that writes a captured local) anywhere in here.

Needed because §F23's premise is "no `next` **after an assignment**", and asking
`noLocalAsgn` instead rejects `next if c` itself — which is exactly the shape the climbed
`ctl-next` rung is built out of. Measured: the first version of this premise broke that rung. -/
def asgnFree : Expr → Bool
  -- the assignments
  | .vasgn .. => false
  | .for' .. => false
  -- a block can write a local it captured
  | .block _ _ body => asgnFree body
  -- containers
  | .splat (some e) | .ret (some e) | .brk (some e) | .nxt (some e)
  | .blockpass (some e) | .cpath (some e) _ | .defined e | .casgn _ e
  | .cpathAsgn _ _ e => asgnFree e
  | .send recv _ args blk =>
    (match recv with | some r => asgnFree r | none => true) &&
    asgnFreeAll args &&
    (match blk with | some b => asgnFree b | none => true)
  | .seq es | .array es | .yield' es => asgnFreeAll es
  | .hash ps => asgnFreePairs ps
  | .kwargs entries => asgnFreeKw entries
  | .if' c t e =>
    asgnFree c && asgnFree t && (match e with | some x => asgnFree x | none => true)
  | .while' c body => asgnFree c && asgnFree body
  | .dowhile body cond => asgnFree body && asgnFree cond
  | .begin' body rescues els ens =>
    asgnFree body && asgnFreeRescues rescues &&
    (match els with | some x => asgnFree x | none => true) &&
    (match ens with | some x => asgnFree x | none => true)
  | .super' args blk =>
    asgnFreeAll args && (match blk with | some b => asgnFree b | none => true)
  | .zsuper blk => (match blk with | some b => asgnFree b | none => true)
  -- declarations bind no local of *this* frame
  | .def' .. | .defs .. | .class' .. | .module' .. => true
  | .scopedClass .. | .scopedModule .. | .sclass .. => true
  | .undef .. | .alias' .. => true
  -- leaves
  | .int _ | .flt _ | .str _ | .sym _ | .regexpLit .. | .tru | .fls | .nil | .self'
  | .var .. | .const _ | .vcall _ | .fwd | .retry' | .redo'
  | .cpath none _ | .splat none | .ret none | .brk none | .nxt none
  | .blockpass none => true

def asgnFreeAll : List Expr → Bool
  | [] => true
  | e :: es => asgnFree e && asgnFreeAll es

def asgnFreePairs : List (Expr × Expr) → Bool
  | [] => true
  | (k, v) :: ps => asgnFree k && asgnFree v && asgnFreePairs ps

def asgnFreeKw : List KwEntry → Bool
  | [] => true
  | .pair _ v :: es => asgnFree v && asgnFreeKw es
  | .dyn k v :: es => asgnFree k && asgnFree v && asgnFreeKw es
  | .splat e :: es => asgnFree e && asgnFreeKw es

def asgnFreeRescues :
    List (List Expr × Option (TargetKind × String) × Expr) → Bool
  | [] => true
  | (cls, _, handler) :: rs => asgnFreeAll cls && asgnFree handler && asgnFreeRescues rs

end

/-- The statement walk: a `next` is allowed while nothing has assigned, and not after. -/
def nxtPrefixGo : List Expr → Bool
  | [] => true
  | s :: rest => if asgnFree s then nxtPrefixGo rest else nxtFree s && nxtFreeAll rest

/-- **§F23's premise**: in this body, no `next` follows an assignment — so every `next` escapes
at the body's *incoming* environment, which the enclosing rule's outgoing premise already pins. -/
def nxtPrefixOk : Expr → Bool
  | .seq es => nxtPrefixGo es
  | e => asgnFree e || nxtFree e

end Ratchet
