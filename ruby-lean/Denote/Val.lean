import Semantics.Interp

/-!
# `Denote/Val.lean` — reading a `Value` through a `Heap`

The bottom layer of the semantic denotation: the *probes*. Every one of these answers a
question about a machine value that the denotation of some `Ty` needs to ask, and every one
of them asks it of the **real** `RubyCore` heap — no re-modelling of the object model here,
just projections out of it.

Three kinds of probe, and the split matters for what the layers above can do:

1. **Immediate shape** (`isIntV`, `isBoolV`, …) — decided by the `Value` constructor alone,
   no heap needed. This is the fragment the user-facing summary calls "simple: just check
   what's in `Value`".
2. **Nominal, through the heap** (`classNamed?`, `isAName`, `isClassRefNamed`) — a class
   *name* (which is all `Ty.cls`/`Ty.clsOf`/`Ty.inst` carry) resolved to an `ObjId` by the
   heap's own constant table, then handed to the machine's own `isA` ancestors walk. Note
   what this buys: the denotation is **heap-indexed**, so a class reopened or a subclass
   created by executing code changes which values inhabit `.cls "Foo"`. That is the point —
   a semantic denotation of a Ruby type has to be heap-indexed or it is lying.
3. **Payload projections** (`arrElems?`, `hshEntries?`, `procClosure?`) — the contents a
   parameterised type quantifies over. `arrayOf`/`hashOf`/`clos` are exactly the arms that
   need these.

Nothing here is about *types*: `Ratchet.Ty` is not imported by this file. That is deliberate
— see `Denote/notes.md` §The two-language boundary.
-/

set_option autoImplicit false

namespace Ratchet.Denote

open RubyCore

/-! ## Immediate shape -/

def isIntV : Value → Bool | .int _ => true | _ => false
def isFltV : Value → Bool | .flt _ => true | _ => false
def isSymV : Value → Bool | .sym _ => true | _ => false
def isBoolV : Value → Bool | .bool _ => true | _ => false
def isNilV : Value → Bool | .nil => true | _ => false

/-! ## Nominal, through the heap -/

/-- The `ObjId` of the class object a **name** denotes at this heap, by the heap's own
toplevel constant table. `none` if the name is not a constant, or is a constant that is not
a class/module object.

This is the whole bridge from `Ty`'s `String`-keyed nominal types to the machine's
`ObjId`-keyed ones, and it is a *lookup in the heap*, not a table in this package: if the
program has not defined `Foo` yet, `.cls "Foo"` is inhabited by nothing at all. -/
def classNamed? (h : Heap) (name : String) : Option ObjId :=
  match constLookup h name with
  | some (.ref o) => if (h.classPayload? o).isSome then some o else none
  | _ => none

/-- `v.is_a?(name)` — the machine's own ancestors walk, at the class the name resolves to.
`false` when the name names no class, which is the honest answer: an undefined class has no
instances. -/
def isAName (h : Heap) (v : Value) (name : String) : Bool :=
  match classNamed? h name with
  | some k => isA h v k
  | none => false

/-- **Is `v` a live object of *exactly* the class named `name`?** `Ty.inst`'s probe, and the
difference from `isAName` is the whole of `found-issues.md` §F12.

`isAName` is is-a, which is right for `Ty.cls` (`rescue StandardError => e` binds a subclass)
and wrong for `Ty.inst`: every rule that *dispatches* on an `.inst n` receiver looks the method
up in `n`'s own table, so a value of a subclass that redefined the method makes the rule's
conclusion false. `Judge` produces an `.inst n` only by allocating exactly `n` or from a
`self` whose class `κ.frame.recvClass` names exactly, so the exact reading is what the judgment
actually means.

**Liveness is part of it, and not incidentally.** `Heap.get` is total, so a dangling reference
reads back as `default`, whose class is `0` — and after an allocation fills that id it has a
real class. The is-a reading survives that (`0` is `BasicObject`, an ancestor of everything, so
`isAName` only grows); the *exact* reading would not, and `denM_ext`/`StateOk_ext` would break
for any machine holding an `.inst`-typed local. Requiring the id to be in range makes the
reading `Ext`-monotone again, and it is true of anything the judgment produces.

**`realClassOf`, not `classOf`.** They differ at an object with a *singleton* class: `classOf`
answers the eigenclass, because that is where dispatch starts, while `realClassOf` answers the
`klass` field, which is what Ruby's `Object#class` reports and what "an instance of `n`" means.
Using `classOf` would make `denM (.inst n I)` false for any object that has ever had a
`def obj.foo` — sound but useless, and it would not even match `Judge.classOf`'s conclusion. -/
def isExactInst (h : Heap) (v : Value) (name : String) : Bool :=
  match classNamed? h name, v with
  | some k, .ref o => o < h.objs.size && (h.get o).eigen.isNone && (h.get o).klass == k
  | _, _ => false

/-- Is `v` *the class object* named `name` (not an instance of it)? `Ty.clsOf`'s probe.
Compared by `ObjId` identity: there is exactly one class object per name at a heap. -/
def isClassRefNamed (h : Heap) (v : Value) (name : String) : Bool :=
  match classNamed? h name, v with
  | some k, .ref o => k == o
  | _, _ => false

/-! ## Payload projections -/

def arrElems? (h : Heap) : Value → Option (Array Value)
  | .ref o => match (h.get o).payload with | .arr xs => some xs | _ => none
  | _ => none

def hshEntries? (h : Heap) : Value → Option (Array (Value × Value))
  | .ref o => match (h.get o).payload with | .hsh es => some es | _ => none
  | _ => none

/-- The `Closure` behind a Proc value — its params, body, and the **frame ids** of its
captured scope and its `return` home. Those two ids are indices into `Machine.frames`, not
into the heap, which is the single fact that forces the denotation above to be indexed by a
`Machine` and not by a `Heap`: a closure's captured environment is *not in the heap*. See
`Denote/Apply.lean`. -/
def procClosure? (h : Heap) : Value → Option Closure
  | .ref o => match (h.get o).payload with | .proc c => some c | _ => none
  | _ => none

def isProcV (h : Heap) (v : Value) : Bool := (procClosure? h v).isSome

/-- An object's instance variable, defaulting to `nil` when it was never assigned.

The default is not a convenience: in Ruby, reading an unassigned instance variable *is*
`nil` (it does not raise), which is the same fact `Ratchet.ivarGet?`'s docstring records for
the type side and `corpus/…-class-ivar-lazy-nil` pins on the semantics side. So the type
`.inst "Box" (ivarCons "@secret" .nilT ivar0)` should be inhabited by a `Box` that never ran
its constructor, and with this default it is. -/
def ivarOf (h : Heap) (v : Value) (x : String) : Value :=
  match v with
  | .ref o => match (h.get o).ivars.find? (·.1 == x) with
    | some (_, w) => w
    | none => .nil
  | _ => .nil

end Ratchet.Denote
