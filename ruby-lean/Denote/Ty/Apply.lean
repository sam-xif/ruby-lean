import Denote.Ty.Val

/-!
# `Denote/Ty/Apply.lean` — calling a Proc value from inside a predicate

An arrow type is a claim about what happens when you **call** something, so a semantic
denotation of an arrow needs a way to say "call this Proc value with these argument values"
*inside a Lean proposition*. That is what this file provides, and it is the only place in
`Denote/` that builds machine states.

## The obstacle: values are not syntax

`RubyCore.Expr` is syntax; there is no `Expr` constructor that carries a `Value`. So the
call cannot be written as an expression to evaluate. `applyIn` gets around it the way Ruby
itself would: it **pre-binds the values as locals** in a fresh frame and evaluates
`__den_f.call(__den_a0, …)`, a piece of syntax whose free names the frame already answers.

## Why a `Machine` and not just a `Heap`

The user-facing shape of the denotation is `Ty → Heap → Value → Bool`, and for every
first-order type that is exactly right — `Denote/Ty/Den.lean`'s `denM_heap_only` proves the
machine is irrelevant there. For a Proc it is *not* right, and the reason is a fact about
the model rather than a design choice: `Closure.captured` and `Closure.home` are
`FrameId`s — indices into `Machine.frames` — so **a closure's captured environment does not
live in the heap**. Handed only a heap, there is no way to reconstruct the scope a lambda
closed over, and `callClosure` would run its body against `frames.getD cl.captured default`:
a default frame, wrong `self`, no captured locals. The call would not be the call the
program would make.

So the master denotation is machine-indexed. `applyIn` preserves `m.frames` wholesale (it
*pushes* a frame rather than replacing the array) precisely so that every `captured`/`home`
index a Proc in `m.heap` might hold still resolves to the frame it meant.

## What is deliberately not modelled

The pushed frame is a `.toplevel` frame with `self = main`, and `m.kont`/`m.stack` are
replaced. Consequences, stated rather than hidden:

* A **non-lambda** `return`/`break` inside the proc unwinds toward `cl.home`, a frame that
  is still in `frames` but no longer on `stack`. The machine will raise `LocalJumpError`
  where a live call might have returned — the same thing real Ruby does to a proc whose
  defining method has returned, but *not* necessarily what would happen at the call site the
  checker is reasoning about. The denotation quantifies over runs that end in `.value`, so
  such a run simply imposes no obligation: an arrow type says nothing about a proc that
  jumps instead of returning. That is the honest reading, and it is why the arrow is stated
  over `.value` outcomes only (`Denote/Ty/Den.lean`).
* `$~` (per-frame in this model) starts `nil` in the pushed frame.
-/

set_option autoImplicit false

namespace Ratchet.Denote

open RubyCore

/-- The local name the `i`-th argument is pre-bound to. Prefixed so it cannot collide with
a desugared program's own names (`__dt_*` is the desugarer's; `__den_*` is ours). -/
def argName (i : Nat) : String := s!"__den_a{i}"

/-- The local the callee is pre-bound to. -/
def fnName : String := "__den_f"

/-- The syntax evaluated by `applyIn`: `__den_f.call(__den_a0, …, __den_a(n-1))`.

`call` rather than `[]` or `yield`: `Proc#call` is the one entry point that works for a
proc, a lambda, and a `Symbol#to_proc` alike, and it is what `Ratchet.Judge.closCall`
already keys on. -/
def callExpr (n : Nat) : Expr :=
  .send (some (.var .lvar fnName)) "call"
    ((List.range n).map (fun i => .var .lvar (argName i))) none

/-- **The application state**: `m`, redirected to evaluate `f.call(args…)` from a fresh
toplevel frame, with `f` and each argument pre-bound as locals.

`frames` is extended, never rewritten — see the module docstring. `kont := []` so that the
call's own return value is the whole machine's result: `applyKont` on an empty continuation
is `.done`, so `Interp.run` reports `.value v m'` exactly when the call returned `v`. -/
def applyIn (m : Machine) (f : Value) (args : List Value) : Machine :=
  let binds := (fnName, f) :: (List.range args.length).map
    (fun i => (argName i, args.getD i .nil))
  let fr : Frame :=
    { self := .ref Boot.mainId, defmod := Boot.objectId, kind := .toplevel,
      cref := [Boot.objectId], locals := binds }
  { m with
    ctl := .eval (callExpr args.length),
    kont := [],
    stack := [m.frames.size],
    frames := m.frames.push fr }

/-- "Calling `f` with `args` in `m` returns `v`, leaving machine `m'`" — for *some* fuel.
The existential over fuel is not a weakening: `Interp.run` is monotone in fuel once it has
landed on a `.value`, so this says "the call terminates with `v`", full stop. -/
def Returns (m : Machine) (f : Value) (args : List Value) (v : Value) (m' : Machine) : Prop :=
  ∃ fuel, Interp.run fuel (applyIn m f args) = .value v m'

/-! ## Reachability — the "possible machine states" an arrow must survive

`Denote/Ty/Den.lean`'s arrow denotation is stated at *one* machine: "called here, this proc
answers in the codomain". A proc is usually called *later*, from a state the program has
evolved into, and a type that only held at the state where the lambda was created would be
worth very little. `Reaches` is the relation that lets the stronger statement be written
(`Den.lean`'s `ArrowStable`): the reflexive-transitive closure of the model's own `Interp.stepFn`.

Kept a `Prop`-level inductive rather than a fuel-indexed `Bool`: it is used only in
hypotheses of statements about arrows, never computed. -/
inductive Reaches : Machine → Machine → Prop where
  | refl (m : Machine) : Reaches m m
  | step {m m' m'' : Machine} (h : Interp.stepFn m = .next m') (t : Reaches m' m'') : Reaches m m''

theorem Reaches.trans {a b c : Machine} : Reaches a b → Reaches b c → Reaches a c := by
  intro hab hbc
  induction hab with
  | refl => exact hbc
  | step h t ih => exact .step h (ih hbc)

/-! ## Reading a closure's captured scope

`Ty.clos` carries the locals the block captured, and `Ty.inst` carries an object's ivars;
the second lives in the heap and the first does **not** (see the module docstring). These
two are the `clos` side's probes, and they are here rather than in `Denote/Ty/Val.lean` because
they need the frame array.

`frameLocal` mirrors `Machine.getLocal` exactly — including the walk up the `captured`
chain, so a name the block did not bind itself but its enclosing scope did resolves the way
a read in the block body would — but starts at a *given* frame instead of the current one. -/

/-- `x`'s value as seen from frame `fid`, walking the `captured` chain outward. `nil` for an
unbound name, matching `Machine.getLocal`. -/
def frameLocal (m : Machine) (fid : FrameId) (x : String) : Value :=
  let rec go : FrameId → Nat → Value
    | _, 0 => .nil
    | fid, fuel + 1 =>
      let f := m.frames.getD fid default
      match f.locals.find? (·.1 == x) with
      | some (_, v) => v
      | none => match f.captured with
        | some p => go p fuel
        | none => .nil
  go fid (m.frames.size + 1)

/-- `frameLocal` from an **optional** frame, which is what `Closure.captured` is since
L266: `none` binds nothing at all. Not the same as reading frame `0` — a capture-free
closure (the `Symbol#to_proc` pair, the only source) is pushed by `callClosure` with
`captured := none`, so its body's walk stops at its own activation and every name it did
not bind itself reads `nil`. -/
def frameLocal? (m : Machine) : Option FrameId → String → Value
  | some fid, x => frameLocal m fid x
  | none, _ => .nil

/-- The `self` a closure's body will see: its capture frame's, which is exactly what
`Interp.callClosure` copies into the block frame it pushes — including the `getD 0`
it uses for a capture-free closure. -/
def closSelf (m : Machine) (cl : Closure) : Value :=
  (m.frames.getD (cl.captured.getD 0) default).self

/-- A closure's captured-scope reader, as the `String → Value` a spine denotation wants. -/
def closLocal (m : Machine) (cl : Closure) : String → Value :=
  frameLocal? m cl.captured

#print axioms Reaches.trans

end Ratchet.Denote
