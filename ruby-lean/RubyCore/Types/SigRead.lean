import RubyCore.Syntax
import RubyCore.Types.Ty

/-!
# P1a — reading Sorbet signatures off the AST

`docs/semantics/static-soundness-poc.md` §8.3. Sorbet adds no syntax: a `sig` is
an ordinary send with a block, and a type is an ordinary expression, so the
desugarer needs no special support and the declared types survive as data [V].
This file recovers them.

## What this is *not* yet wired to

It does **not** feed `check`'s `accept`. §8.3 measured why: a sig'd call costs
~256 extra steps of `T`-shim execution, and `Inv` works by *restriction*, so the
machine leaves any small fragment the instant `sig` is evaluated. Reading a
declared type is a static question and is unblocked; concluding safety about a
machine that runs the shim is not. Sig-bearing programs therefore stay `unknown`
until P1d's two-machine argument exists.

## `SigTy` is deliberately wider than `Ty`

`Ty` (`Types/Core.lean`) is what the *proof* understands — three ground types.
`SigTy` is what a *program can declare*, which is much more. Keeping them
separate means the reader reports faithfully instead of silently lossily, and
`toTy` is the explicit, partial bridge. Conflating them would have forced `Ty` to
grow for reasons the proof does not need yet.

`render` reproduces Sorbet's own surface syntax exactly, so a reader output can
be compared against the string a generator declared without a translation layer
in between (`difftest/difftest/sig_gen.py`'s `Ty.render`).
-/

namespace RubyCore.Types

/-- A type as *declared*. `other` is the honest catch-all: recognisably a type
    expression we do not model, kept distinct from "not a type at all" (`none`). -/
inductive SigTy where
  | nominal (name : String)
  | boolean
  | untyped
  | nilable (t : SigTy)
  | anyOf (ts : List SigTy)
  | allOf (ts : List SigTy)
  | array (t : SigTy)
  | hashT (k v : SigTy)
  /-- **`T.proc.params(...).returns(...)`** (typed-lambdas L1), carrying what the
      chain actually declared: `params`, positionally (the keyword spelling
      `params(a: String, b: String)` is Sorbet surface syntax for a *positional*
      arrow — the plan's own note, "Sorbet's `T.proc` params are positional
      despite the keyword spelling"), and the return type. `none` return is
      `.void` (mirrors `SigDecl.ret`). Previously a bare marker with no payload
      — the chain was *detected*, never *read*; `readProcChain` below is what
      reads it. -/
  | procT (params : List SigTy) (ret : Option SigTy)
  | other (what : String)
-- No `DecidableEq`: the nested `List SigTy` defeats the deriving handler and
-- nothing here needs it.
deriving Repr, Inhabited

mutual

def SigTy.render : SigTy → String
  | .nominal n => n
  | .boolean => "T::Boolean"
  | .untyped => "T.untyped"
  | .nilable t => "T.nilable(" ++ t.render ++ ")"
  | .anyOf ts => "T.any(" ++ SigTy.renderList ts ++ ")"
  | .allOf ts => "T.all(" ++ SigTy.renderList ts ++ ")"
  | .array t => "T::Array[" ++ t.render ++ "]"
  | .hashT k v => "T::Hash[" ++ k.render ++ ", " ++ v.render ++ "]"
  | .procT ps r =>
    "T.proc.params(" ++ SigTy.renderList ps ++ ")" ++
      (match r with
       | some t => ".returns(" ++ t.render ++ ")"
       | none => ".void")
  | .other w => w

def SigTy.renderList : List SigTy → String
  | [] => ""
  | [t] => t.render
  | t :: ts => t.render ++ ", " ++ SigTy.renderList ts

end

/-! ## The bridge to `Ty`, and reading a type expression

`toTy`/`toTyList` and `readTy`/`readTyList`/`readKw`/`readProcChain` are each
split into a pair for the same reason `SigTy.render`/`renderList` already is:
`SigTy` nests a `List SigTy`, so any function that recurses into a payload
list needs the sibling to recurse *with*. -/

mutual

/-- The bridge to what the proof understands. Partial on purpose: everything
    outside P0's ground types (+ arrows, L1) is `none`, which the caller must
    read as "cannot say", never as a default. -/
def toTy : SigTy → Option Ty
  | .nominal "Integer" => some .int
  | .nominal "String" => some (.cls "String")
  | .nominal "NilClass" => some .nilT
  | .nominal "TrueClass" => some .bool
  | .nominal "FalseClass" => some .bool
  | .boolean => some .bool
  -- **L1's bridge lands here.** `ret = none` (`.void`) has no `Ty` to name — a
  -- lambda always evaluates to something, so a `T.proc` with no declared
  -- `.returns` is out of this bridge's range, same honest `none` as any other
  -- unmodeled `SigTy`.
  | .procT ps (some r) =>
    match toTyList ps, toTy r with
    | some doms, some cod => some (arrowOf doms cod)
    | _, _ => none
  | _ => none

def toTyList : List SigTy → Option (List Ty)
  | [] => some []
  | t :: ts =>
    match toTy t, toTyList ts with
    | some ty, some tys => some (ty :: tys)
    | _, _ => none

end

/-! ## Reading a type expression -/

/-- `A`, `A::B`, `::A` — the constant path as written. -/
def constPath : Expr → Option String
  | .const n => some n
  | .cpath none n => some ("::" ++ n)
  | .cpath (some b) n => (constPath b).map (· ++ "::" ++ n)
  | _ => none

/-- Is this expression rooted at `T.proc`? `T.proc.params(...).returns(...)` is a
    send chain, so the root has to be found rather than pattern-matched. -/
def rootsAtTProc : Expr → Bool
  | .send (some (.const "T")) "proc" [] _ => true
  | .send (some r) _ _ _ => rootsAtTProc r
  | _ => false

mutual

/-- **The `T.proc` arm walks its own chain via `readTy` on the receiver** (L1),
    never on `e` itself — `.params(...)`/`.returns(...)` peel one send layer at
    a time, each landing on `r`, a *strict* subterm, so the recursion is the
    same shape every other arm already has (structural on `sizeOf e`). A
    dedicated `readProcChain` sibling was tried first and rejected: called from
    `readTy` at the *same* `e` it just matched, it gives the equation compiler
    no decreasing measure at all. Folding the walk into `readTy`'s own
    recursion is what a strict subterm buys back.

    `.procT` accumulates params right-to-left as the chain is peeled outside-in
    (`.returns` is the outermost link, `.params` inside it, `T.proc` at the
    root) — the accumulator is simply "whatever `readTy` on the receiver
    already read", which is exactly the associativity `readSigChain` (below,
    the bare-`sig` twin) relies on too. -/
def readTy (e : Expr) : Option SigTy :=
  match e with
  | .send (some (.const "T")) "untyped" [] _ => some .untyped
  | .send (some (.const "T")) "nilable" [t] _ => (readTy t).map .nilable
  | .send (some (.const "T")) "any" ts _ => (readTyList ts).map .anyOf
  | .send (some (.const "T")) "all" ts _ => (readTyList ts).map .allOf
  | .send (some (.cpath (some (.const "T")) "Array")) "[]" [t] _ =>
    (readTy t).map .array
  | .send (some (.cpath (some (.const "T")) "Hash")) "[]" [k, v] _ =>
    match readTy k, readTy v with
    | some kt, some vt => some (.hashT kt vt)
    | _, _ => none
  | .send (some (.const "T")) "self_type" [] _ => some (.other "T.self_type")
  | .send (some (.const "T")) "attached_class" [] _ =>
    some (.other "T.attached_class")
  | .send (some (.const "T")) "noreturn" [] _ => some (.other "T.noreturn")
  -- **The base of a `T.proc` chain** — no params read yet, no return.
  | .send (some (.const "T")) "proc" [] _ => some (.procT [] none)
  -- **`.params(...)` off a `T.proc` chain.** Guarded on `rootsAtTProc r`
  -- (rather than on `readTy r` answering `.procT`) so a malformed receiver
  -- refuses rather than silently reading `[]`.
  | .send (some r) "params" [.kwargs entries] _ =>
    if rootsAtTProc r then
      match readTy r, readKw entries with
      | some (.procT _ ret), some ps => some (.procT (ps.map Prod.snd) ret)
      | _, _ => none
    else none
  -- **`.returns(...)` off a `T.proc` chain.** Tried before the bare-`sig`
  -- `readSigChain`-style arm would ever see this shape, since that one lives
  -- in a separate function entirely — this is `readTy`'s own arrow rule.
  | .send (some r) "returns" [t] _ =>
    if rootsAtTProc r then
      match readTy r, readTy t with
      | some (.procT ps _), some retTy => some (.procT ps (some retTy))
      | _, _ => none
    else none
  | .const n => some (.nominal n)
  | .cpath (some (.const "T")) "Boolean" => some .boolean
  | .cpath b n =>
    (constPath (.cpath b n)).map .nominal
  -- **An unrecognised link on an otherwise-`T.proc`-rooted chain is skipped**
  -- (`.checked(:tests)` and friends), `readSigChain`'s reason verbatim.
  | .send (some r) _ _ _ => if rootsAtTProc r then readTy r else none
  | _ => none
termination_by sizeOf e

def readTyList (es : List Expr) : Option (List SigTy) :=
  match es with
  | [] => some []
  | e :: rest =>
    match readTy e, readTyList rest with
    | some t, some ts => some (t :: ts)
    | _, _ => none
termination_by sizeOf es

/-- `readKw`, folded into this mutual group because it calls `readTy` and
    (via `readSigChain` below, and via `readTy`'s own `.params` arm) is
    called back into. Unchanged behaviour from the pre-L1 standalone
    version. -/
def readKw : List KwEntry → Option (List (String × SigTy))
  | [] => some []
  | .pair k v :: rest =>
    match readTy v, readKw rest with
    | some t, some ps => some ((k, t) :: ps)
    | _, _ => none
  | .dyn _ _ :: _ => none
  | .splat _ :: _ => none
termination_by es => sizeOf es

end

/-! ## Reading a `sig` -/

/-- A declared signature. `ret = none` is `.void` — Sorbet's own way of saying
    "no meaningful return", not an absence of information. -/
structure SigDecl where
  params : List (String × SigTy)
  ret : Option SigTy
deriving Repr, Inhabited

/-- Walk the `params(...).returns(...)` chain from the outside in. Unrecognised
    links (`.checked`, `.override`, `.abstract`, `.type_parameters`, …) are
    *skipped* rather than failed: they modify enforcement or dispatch, not the
    declared types, and refusing them would lose signatures we can read. -/
def readSigChain (e : Expr) : Option SigDecl :=
  match e with
  | .send none "params" [.kwargs entries] _ =>
    (readKw entries).map (fun ps => { params := ps, ret := none })
  | .send none "returns" [t] _ =>
    (readTy t).map (fun ty => { params := [], ret := some ty })
  | .send none "void" [] _ => some { params := [], ret := none }
  | .send (some r) "returns" [t] _ =>
    match readSigChain r, readTy t with
    | some d, some ty => some { d with ret := some ty }
    | _, _ => none
  | .send (some r) "void" [] _ => readSigChain r
  | .send (some r) _ _ _ => readSigChain r
  | _ => none
termination_by sizeOf e

/-- The block body of a `sig { … }`, if this statement is one. -/
def sigBody? : Expr → Option Expr
  | .send none "sig" _ (some (.block _ _ body)) => some body
  | .send (some recv) _ _ _ => sigBody? recv
  | _ => none

/-! ## Associating sigs with definitions

A `sig` is a *separate statement preceding* the `def`, so association is by
adjacency — the same shape `Fragment.lean` threads a `sigPrecedes` flag for
(L82). Here the pending declaration is threaded instead of a flag, which is the
same single traversal carrying slightly more.
-/

/-- `(method name, declared signature)` for every `def` a readable `sig`
    precedes. A `def` with no preceding sig contributes nothing — that is the
    gradual boundary, not an error. -/
partial def collectSigs (e : Expr) : List (String × SigDecl) :=
  go e none |>.1
where
  /-- Returns the pairs found and the still-pending sig, so nesting composes. -/
  go (e : Expr) (pending : Option SigDecl) :
      List (String × SigDecl) × Option SigDecl :=
    match e with
    | .seq es => goList es pending
    | .class' _ _ body => (go body none |>.1, pending)
    | .module' _ body => (go body none |>.1, pending)
    | .def' name _ _ =>
      match pending with
      | some d => ([(name, d)], none)
      | none => ([], none)
    | other =>
      match sigBody? other with
      | some body => ([], readSigChain body)
      | none => ([], pending)
  goList (es : List Expr) (pending : Option SigDecl) :
      List (String × SigDecl) × Option SigDecl :=
    match es with
    | [] => ([], pending)
    | e :: rest =>
      let (found, p) := go e pending
      let (found', p') := goList rest p
      (found ++ found', p')

end RubyCore.Types
