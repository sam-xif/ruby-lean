import Ratchet.Expr
import Semantics.Interp

/-!
# `Denote/Sem/Trans.lean` — the syntax bridge

`Ratchet/Expr.lean` is `RubyCore/Syntax.lean`'s `Expr` **copied as text** (`AGENTS.md`
§Isolation), so the two are structurally identical inductives with no relation Lean knows
about. Every judgment in `Ratchet/` is about the copy; the only executable semantics is over
the original. Nothing could relate them, and `Denote/notes.md` recorded that as the reason
there was no `Judge`-soundness theorem: *"it needs an evaluation relation for `Ratchet.Expr`
and the only executable one in reach is over `RubyCore.Expr`."*

This file is that relation. `toRuby` is the identity-on-structure translation, 48 arms, one
per constructor, and it is what turns a claim about a `Ratchet.Expr` into a claim about a run
of the machine.

## Why a translation rather than deleting one copy

Deleting the copy would be the obvious simplification and it is the wrong trade. The copy is
load-bearing: `Ratchet/` importing nothing from `../lean/RubyCore/` is what makes a divergence
between the two a **deliberate fork to notice** rather than a build error to paper over, and
that isolation is the reason this restart exists. So the boundary stays and gets a function
across it, whose one job — being the identity — is checkable:

* **Mechanically total.** Every constructor maps to its namesake; there is no default arm and
  no `Option`, so a constructor added on either side breaks the build rather than silently
  falling through.
* **`toRuby_ofJson` (not built)**: the sharper check available later is that decoding a corpus
  JSON with `Ratchet.Decode.program` and then translating equals decoding it with
  `RubyCore.Decode.program`. `CheckRungs.lean` already decodes both ways for every rung, so
  the two decoders are pinned against each other per-rung today; a theorem would replace 177
  data points with one statement. Recorded as a target, not claimed.

## What it closes

`Denote/Den.lean` §Two stated gaps said `Ty.clos`'s `idx` has no denotation, because it
indexes the *checker's* table of `Ratchet.Expr` block literals while the heap holds a
`RubyCore.Closure` — "two separately-copied inductives with no coercion between them". With
`toRuby` there is a coercion, so `Denote/Sem/State.lean`'s `closTblOk` can compare a live
Proc's params and body against the table entry `idx` names. That gap is now a *provable
statement* rather than a structural impossibility.
-/

set_option autoImplicit false

namespace Ratchet.Denote

/-! ## Params, keyword entries, and the small enumerations -/

def toRubyVarKind : Ratchet.VarKind → RubyCore.VarKind
  | .lvar => .lvar
  | .ivar => .ivar
  | .cvar => .cvar
  | .gvar => .gvar

def toRubyTargetKind : Ratchet.TargetKind → RubyCore.TargetKind
  | .lvar => .lvar
  | .ivar => .ivar
  | .cvar => .cvar
  | .gvar => .gvar
  | .const => .const

mutual

/-- The translation. One arm per `Ratchet.Expr` constructor, in the inductive's own order;
no default case, on purpose (see the module docstring). -/
def toRuby : Ratchet.Expr → RubyCore.Expr
  | .int n => .int n
  | .regexpLit src opts => .regexpLit src opts
  | .flt bits => .flt bits
  | .str s => .str s
  | .sym s => .sym s
  | .tru => .tru
  | .fls => .fls
  | .nil => .nil
  | .self' => .self'
  | .var k name => .var (toRubyVarKind k) name
  | .vasgn k name e => .vasgn (toRubyVarKind k) name (toRuby e)
  | .const name => .const name
  | .casgn name e => .casgn name (toRuby e)
  | .cpath base name => .cpath (toRubyOpt base) name
  | .cpathAsgn base name e => .cpathAsgn (toRubyOpt base) name (toRuby e)
  | .send recv m args blk => .send (toRubyOpt recv) m (toRubyList args) (toRubyOpt blk)
  | .vcall m => .vcall m
  | .kwargs entries => .kwargs (toRubyKwList entries)
  | .fwd => .fwd
  | .block params locals body => .block (toRubyParams params) locals (toRuby body)
  | .yield' args => .yield' (toRubyList args)
  | .blockpass e => .blockpass (toRubyOpt e)
  | .if' c t e => .if' (toRuby c) (toRuby t) (toRubyOpt e)
  | .while' c body => .while' (toRuby c) (toRuby body)
  | .dowhile body cond => .dowhile (toRuby body) (toRuby cond)
  | .for' targets coll body => .for' (toRubyTargets targets) (toRuby coll) (toRuby body)
  | .def' name params body => .def' name (toRubyParams params) (toRuby body)
  | .array elems => .array (toRubyList elems)
  | .hash pairs => .hash (toRubyPairs pairs)
  | .splat e => .splat (toRubyOpt e)
  | .ret e => .ret (toRubyOpt e)
  | .brk e => .brk (toRubyOpt e)
  | .nxt e => .nxt (toRubyOpt e)
  | .retry' => .retry'
  | .redo' => .redo'
  | .class' name sup body => .class' name (toRubyOpt sup) (toRuby body)
  | .module' name body => .module' name (toRuby body)
  | .scopedClass base name body => .scopedClass (toRubyOpt base) name (toRuby body)
  | .scopedModule base name body => .scopedModule (toRubyOpt base) name (toRuby body)
  | .sclass obj body => .sclass (toRuby obj) (toRuby body)
  | .defs recv name params body =>
      .defs (toRuby recv) name (toRubyParams params) (toRuby body)
  | .begin' body rescues els ens =>
      .begin' (toRuby body) (toRubyRescues rescues) (toRubyOpt els) (toRubyOpt ens)
  | .super' args blk => .super' (toRubyList args) (toRubyOpt blk)
  | .zsuper blk => .zsuper (toRubyOpt blk)
  | .undef names => .undef names
  | .alias' newName oldName => .alias' newName oldName
  | .defined e => .defined (toRuby e)
  | .seq es => .seq (toRubyList es)

def toRubyOpt : Option Ratchet.Expr → Option RubyCore.Expr
  | none => none
  | some e => some (toRuby e)

def toRubyList : List Ratchet.Expr → List RubyCore.Expr
  | [] => []
  | e :: es => toRuby e :: toRubyList es

def toRubyPairs : List (Ratchet.Expr × Ratchet.Expr) → List (RubyCore.Expr × RubyCore.Expr)
  | [] => []
  | (k, v) :: ps => (toRuby k, toRuby v) :: toRubyPairs ps

def toRubyTargets : List (Ratchet.TargetKind × String) →
    List (RubyCore.TargetKind × String)
  | [] => []
  | (k, n) :: ts => (toRubyTargetKind k, n) :: toRubyTargets ts

def toRubyRescues :
    List (List Ratchet.Expr × Option (Ratchet.TargetKind × String) × Ratchet.Expr) →
    List (List RubyCore.Expr × Option (RubyCore.TargetKind × String) × RubyCore.Expr)
  | [] => []
  | (cls, binding, handler) :: rs =>
      (toRubyList cls, toRubyBinding binding, toRuby handler) :: toRubyRescues rs

def toRubyBinding : Option (Ratchet.TargetKind × String) →
    Option (RubyCore.TargetKind × String)
  | none => none
  | some (k, n) => some (toRubyTargetKind k, n)

def toRubyParams : List Ratchet.Param → List RubyCore.Param
  | [] => []
  | p :: ps => toRubyParam p :: toRubyParams ps

def toRubyParam : Ratchet.Param → RubyCore.Param
  | .req name => .req name
  | .opt name dflt => .opt name (toRuby dflt)
  | .rest name => .rest name
  | .key name dflt => .key name (toRubyOpt dflt)
  | .kwrest name => .kwrest name
  | .block name => .block name
  | .fwd => .fwd
  | .destr subs => .destr (toRubyParams subs)

def toRubyKwList : List Ratchet.KwEntry → List RubyCore.KwEntry
  | [] => []
  | k :: ks => toRubyKw k :: toRubyKwList ks

def toRubyKw : Ratchet.KwEntry → RubyCore.KwEntry
  | .pair key val => .pair key (toRuby val)
  | .dyn key val => .dyn (toRuby key) (toRuby val)
  | .splat e => .splat (toRuby e)

end

end Ratchet.Denote
