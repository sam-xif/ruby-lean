import Denote.ArrowCheck
import Semantics.Interp

/-!
# `Denote/Examples.lean` — the denotation, against the real booted heap

Every check in this file runs a real program under the real `stepFn` from the real
prelude-booted heap (`Ratchet.Semantics.run`) and then asks `denB`/`closB`/`arrowCheck` about
the value it produced. Nothing is hand-simulated and nothing is decided from syntax.

The `#guard`s make the build the gate: if the denotation and the semantics ever disagree
about one of these, `lake build Denote` fails. That is the same discipline `checkrungs`
applies to the syntactic side — the difference being that `checkrungs` can only compare the
*class name* of the result (`CheckRungs.lean`'s `expectedClasses`, whose docstrings say three
times that it cannot look inside an array, an object, or a Proc), and these can look inside.

Fuel is generous and uniform; a program here that ran out would be a bug in the example, not
a finding.
-/

set_option autoImplicit false

namespace Ratchet.Denote.Examples

open RubyCore
open Ratchet Ratchet.Denote

def fuel : Nat := 200000

/-- Run `p`, then ask the denotation about the result. `none` when the program did not
produce a value at all (which every example here does). -/
def denAfter (p : Expr) (τ : Ty) : Option Bool :=
  match Semantics.run fuel p with
  | .value v m => some (denB τ m.heap v)
  | _ => none

/-- The same, for the machine-indexed `clos` arm. -/
def closAfter (p : Expr) (κ : Ty) : Option Bool :=
  match Semantics.run fuel p with
  | .value v m => some (closB κ m v)
  | _ => none

/-- The same, for a bounded arrow check. -/
def arrowAfter (p : Expr) (ps : List Ty) (r : Ty) (samples : List (List Value)) :
    Option Bool :=
  match Semantics.run fuel p with
  | .value v m => some (arrowCheck fuel ps r m v samples)
  | _ => none

/-! ## Immediates and the nominal core -/

/-- `1 + 2` -/
def pAdd : Expr := .send (some (.int 1)) "+" [.int 2] none
/-- `"a" + "b"` -/
def pConcat : Expr := .send (some (.str "a")) "+" [.str "b"] none

#guard denAfter pAdd .int == some true
#guard denAfter pAdd .float == some false
-- `.never` is inhabited by nothing at all, including a perfectly good `3`.
#guard denAfter pAdd .never == some false
-- `.any` is inhabited by everything.
#guard denAfter pAdd .any == some true
#guard denAfter pConcat (.cls "String") == some true
-- Nominal *through the ancestors walk*: a String is an Object. This is `is_a?`, read off the
-- heap, not a name comparison — which is the whole difference from `expectedClasses`.
#guard denAfter pConcat (.cls "Object") == some true
#guard denAfter pConcat (.cls "Integer") == some false
-- A class that does not exist at this heap has no instances.
#guard denAfter pConcat (.cls "Nonesuch") == some false

/-! ## Parameterised types: looking *inside* the value -/

/-- `[1, 2, 3]` -/
def pArr : Expr := .array [.int 1, .int 2, .int 3]
/-- `[]` -/
def pArrEmpty : Expr := .array []
/-- `[1, "a"]` -/
def pArrMixed : Expr := .array [.int 1, .str "a"]

#guard denAfter pArr (.arrayOf .int) == some true
#guard denAfter pArr (.arrayOf .float) == some false
-- `arrayOf .never` reads "provably empty" (`Ty.arrayOf`/`Ty.never`'s docstrings) and the
-- denotation confirms it: exactly the empty arrays inhabit it.
#guard denAfter pArrEmpty (.arrayOf .never) == some true
#guard denAfter pArr (.arrayOf .never) == some false
-- The join `elemTy` computes for `[1, "a"]` really is an upper bound on the elements.
#guard denAfter pArrMixed (.arrayOf (joinT .int (.cls "String"))) == some true
#guard denAfter pArrMixed (.arrayOf .int) == some false

/-- `{"a" => 1.5, "b" => 2.5}` — the tier-17b `hashOf`, whose whole motivation was a frozen
table read by a variable key (`Ty.hashOf`'s docstring). The useful fact there is "every value
is a Float", and that is a statement about the payload, so this is a type `expectedClasses`
could only have answered `["Hash"]` for. -/
def pHash : Expr :=
  .hash [(.str "a", .flt (1.5 : Float).toBits), (.str "b", .flt (2.5 : Float).toBits)]

#guard denAfter pHash (.hashOf (.cls "String") .float) == some true
#guard denAfter pHash (.hashOf (.cls "String") .int) == some false
#guard denAfter (.hash []) (.hashOf .never .never) == some true

/-! ## An object, and its ivar spine -/

/-- `class Box; def initialize(x); @x = x; end; end; Box.new(1)` -/
def pBox : Expr :=
  .seq [
    .class' "Box" none
      (.def' "initialize" [.req "x"] (.vasgn .ivar "@x" (.var .lvar "x"))),
    .send (some (.const "Box")) "new" [.int 1] none]

#guard denAfter pBox (.inst "Box" (.ivarCons "@x" .int .ivar0)) == some true
#guard denAfter pBox (.inst "Box" (.ivarCons "@x" (.cls "String") .ivar0)) == some false
-- The spine is a *lower* bound: a type that mentions no ivar is inhabited by an object that
-- has one.
#guard denAfter pBox (.inst "Box" .ivar0) == some true
-- And an ivar the object never assigned reads `nil`, which is what `ivarGet?`'s default and
-- `class-ivar-lazy-nil` both say.
#guard denAfter pBox (.inst "Box" (.ivarCons "@y" .nilT .ivar0)) == some true
#guard denAfter pBox (.inst "Nonesuch" .ivar0) == some false

/-! ## A closure: the captured scope, read out of `Machine.frames`

This is the check that pins `Denote/Apply.lean`'s central claim — that a closure's captured
environment is **not in the heap**. `closB` finds `x = 7` by walking `Closure.captured` into
the frame array; a heap-only denotation has no way to reach it. -/

/-- `x = 7; lambda { x }` -/
def pClosCapture : Expr :=
  .seq [
    .vasgn .lvar "x" (.int 7),
    .send none "lambda" [] (some (.block [] [] (.var .lvar "x")))]

-- `.never` in `selfTy` is the "created where `self` was not typed" sentinel (top level here),
-- not the bottom type — see `Denote/Den.lean` §Two stated gaps. The index is unused.
#guard closAfter pClosCapture (.clos 0 (.ivarCons "x" .int .ivar0) .never) == some true
#guard closAfter pClosCapture (.clos 0 (.ivarCons "x" (.cls "String") .ivar0) .never)
  == some false
#guard closAfter pClosCapture (.clos 0 .ivar0 .never) == some true
-- Not a Proc at all.
#guard closAfter pAdd (.clos 0 .ivar0 .never) == some false

/-! ## The arrow: bounded checking

`arrowCheck` can only *refute* (`Denote/ArrowCheck.lean`), and both halves of that show up
here: the `Integer → Integer` arrow survives every sample, and the `Integer → String` one is
refuted by the first. -/

/-- `lambda { |x| x + 1 }` -/
def pSucc : Expr :=
  .send none "lambda" []
    (some (.block [.req "x"] [] (.send (some (.var .lvar "x")) "+" [.int 1] none)))

/-- `lambda { |s| s.length }` -/
def pLength : Expr :=
  .send none "lambda" []
    (some (.block [.req "s"] [] (.send (some (.var .lvar "s")) "length" [] none)))

def intSamples : List (List Value) := [[.int 0], [.int 1], [.int (-5)], [.int 1000]]

#guard arrowAfter pSucc [.int] .int intSamples == some true
-- Refuted: `succ` of an Integer is not a String, and sample `[0]` is the witness.
#guard arrowAfter pSucc [.int] (.cls "String") intSamples == some false
-- The domain is a *hypothesis*: samples outside it are skipped, so a wrong-domain sample
-- cannot refute. `["a"]` is not an `Integer`, so it says nothing about this arrow.
#guard arrowAfter pSucc [.int] .int [[.sym "a"]] == some true
-- `String#length : Integer`. The samples are Symbols rather than Strings only because a
-- String *value* cannot be written down here without allocating one in the heap first — which
-- is itself the point that `Value` is a machine artifact, not syntax.
#guard arrowAfter pLength [.any] .int [[.sym "abc"]] == some true

/-- One printable report, for a human reading the build log. -/
def report : String :=
  let rows : List (String × Option Bool) :=
    [("1 + 2 : Integer", denAfter pAdd .int),
     ("1 + 2 : Float", denAfter pAdd .float),
     ("\"a\" + \"b\" : Object", denAfter pConcat (.cls "Object")),
     ("[1,2,3] : Array[Integer]", denAfter pArr (.arrayOf .int)),
     ("[] : Array[never]", denAfter pArrEmpty (.arrayOf .never)),
     ("{..} : Hash[String, Float]", denAfter pHash (.hashOf (.cls "String") .float)),
     ("Box.new(1) : Box{@x: Integer}",
       denAfter pBox (.inst "Box" (.ivarCons "@x" .int .ivar0))),
     ("lambda{x} : clos{x: Integer}",
       closAfter pClosCapture (.clos 0 (.ivarCons "x" .int .ivar0) .never)),
     ("lambda{|x| x+1} : (Integer) -> Integer  [bounded]",
       arrowAfter pSucc [.int] .int intSamples),
     ("lambda{|x| x+1} : (Integer) -> String   [refuted]",
       arrowAfter pSucc [.int] (.cls "String") intSamples)]
  String.intercalate "\n" (rows.map fun (name, r) =>
    let v := match r with
      | some true => "yes"
      | some false => "no "
      | none => "??? (no value)"
    s!"  {v}  {name}")

end Ratchet.Denote.Examples
