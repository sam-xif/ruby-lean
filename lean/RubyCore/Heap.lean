/-
Values, objects, the heap, and the pure object-model operations
(artifacts 01–02). Per lean-model-sketch.md §1.3, the step relation touches
the heap only through the functions defined here; they get their own lemmas
later.

L0 representation notes (implementation-notes to be recorded harness-side):
- ObjId is a dense index into `Heap.objs` (allocation order, never reused).
- Ancestors = the superclass chain only: `include`/`prepend` are out of the
  L0 fragment, so no MRO expansion yet (artifact 02 §1 covers the general
  case; the ANCESTORS rule degenerates to the chain walk below).
- Kernel is not modeled as a separate module yet: kernel methods live
  directly on Object. Observable only via `.ancestors` introspection, which
  is out of fragment.
- Visibility is recorded but not yet checked (L0 has no explicit-receiver
  private-call cases the desugar admits that we support; revisit at L2).
-/
import RubyCore.Syntax

namespace RubyCore

abbrev ObjId := Nat

inductive Value where
  | ref (o : ObjId)
  | int (n : Int)
  | flt (x : Float)
  | sym (s : String)
  | bool (b : Bool)
  | nil
deriving Repr, Inhabited

/-- Immediate structural equality — identity for refs, value identity for
    immediates. This is `equal?`, not `==` (artifact 01 §6). Type-strict:
    `1` and `1.0` are NOT `eql?`. -/
def Value.identEq : Value → Value → Bool
  | .ref a, .ref b => a == b
  | .int a, .int b => a == b
  | .flt a, .flt b => a == b || (a.isNaN && b.isNaN && false)  -- NaN never equal
  | .sym a, .sym b => a == b
  | .bool a, .bool b => a == b
  | .nil, .nil => true
  | _, _ => false

/-- Truthiness (artifact 01 §6): exactly false and nil are falsey. -/
def Value.truthy : Value → Bool
  | .bool false => false
  | .nil => false
  | _ => true

structure MethodDef where
  params : List String
  body : Expr
  owner : ObjId
  /-- `some bid` marks an axiomatized builtin (artifact 01 §2); `body` is
      then ignored and Builtins.lean supplies the behavior keyed on `bid`. -/
  builtin : Option String := none
  private' : Bool := false
deriving Inhabited

structure ClassPayload where
  superclass : Option ObjId
  methods : List (String × MethodDef) := []
  consts : List (String × Value) := []
  name : String
  isModule : Bool := false
deriving Inhabited

/-- A block/proc/lambda closure (artifact 04 §1). Frame identity supplies
    Essence's generative jump targets (sketch §1.1):
    - `captured` is the FrameId of the defining frame — free variables resolve
      up its chain and `self`/`defmod`/method-block are inherited from it.
    - `home` is the method activation that a non-lambda `return` unwinds to.
    - `lam` selects lambda semantics (strict arity, local `return`/`break`).
    FrameId = Nat (defined in Machine); kept as Nat here to avoid an import
    cycle. -/
structure Closure where
  params : List String
  locals : List String
  body : Expr
  captured : Nat
  home : Nat
  lam : Bool := false
deriving Inhabited

inductive Payload where
  | none
  | str (s : String)
  | arr (elems : Array Value)
  | hsh (entries : Array (Value × Value))
  | cls (c : ClassPayload)
  /-- Exception instance: just the message for L0. -/
  | exc (msg : String)
  /-- A Proc (block/proc/lambda), artifact 04 §1. -/
  | proc (c : Closure)
deriving Inhabited

structure Object where
  klass : ObjId
  ivars : List (String × Value) := []
  frozen : Bool := false
  eigen : Option ObjId := none
  payload : Payload := .none
deriving Inhabited

/-- ObjId = index; allocation appends (ids never reused, artifact 01 §2). -/
structure Heap where
  objs : Array Object
deriving Inhabited

namespace Heap

def get? (h : Heap) (o : ObjId) : Option Object := h.objs[o]?

def get (h : Heap) (o : ObjId) : Object := h.objs.getD o default

def set (h : Heap) (o : ObjId) (obj : Object) : Heap :=
  ⟨h.objs.set! o obj⟩

def alloc (h : Heap) (obj : Object) : ObjId × Heap :=
  (h.objs.size, ⟨h.objs.push obj⟩)

def classPayload? (h : Heap) (o : ObjId) : Option ClassPayload :=
  match (h.get o).payload with
  | .cls c => some c
  | _ => Option.none

def setClassPayload (h : Heap) (o : ObjId) (c : ClassPayload) : Heap :=
  h.set o { h.get o with payload := .cls c }

end Heap

/-! ## Bootstrap heap H₀ (artifact 01 §4)

Fixed ids for the classes every rule needs. The metaclass knot
(`Class.class == Class`, `Class < Module < Object < BasicObject`) lives
entirely in this initial data. -/

namespace Boot

def basicObjectId : ObjId := 0
def objectId : ObjId := 1
def moduleId : ObjId := 2
def classId  : ObjId := 3
def nilClassId : ObjId := 4
def trueClassId : ObjId := 5
def falseClassId : ObjId := 6
def integerId : ObjId := 7
def floatId : ObjId := 8
def stringId : ObjId := 9
def symbolId : ObjId := 10
def arrayId : ObjId := 11
def hashId : ObjId := 12
def exceptionId : ObjId := 13
def standardErrorId : ObjId := 14
def runtimeErrorId : ObjId := 15
def argumentErrorId : ObjId := 16
def typeErrorId : ObjId := 17
def nameErrorId : ObjId := 18
def noMethodErrorId : ObjId := 19
def zeroDivisionErrorId : ObjId := 20
def localJumpErrorId : ObjId := 21
def frozenErrorId : ObjId := 22
def indexErrorId : ObjId := 23
def keyErrorId : ObjId := 24
def rangeErrorId : ObjId := 25
def stopIterationId : ObjId := 26
def notImplementedErrorId : ObjId := 27
def scriptErrorId : ObjId := 28
def procId : ObjId := 29
/-- Toplevel self (`main`), an ordinary Object instance. -/
def mainId : ObjId := 30

/-- (id, name, superclass) for every bootstrap class, in id order. -/
def classTable : List (ObjId × String × Option ObjId) := [
  (basicObjectId, "BasicObject", Option.none),
  (objectId, "Object", some basicObjectId),
  (moduleId, "Module", some objectId),
  (classId, "Class", some moduleId),
  (nilClassId, "NilClass", some objectId),
  (trueClassId, "TrueClass", some objectId),
  (falseClassId, "FalseClass", some objectId),
  (integerId, "Integer", some objectId),   -- Numeric omitted at L0
  (floatId, "Float", some objectId),
  (stringId, "String", some objectId),
  (symbolId, "Symbol", some objectId),
  (arrayId, "Array", some objectId),
  (hashId, "Hash", some objectId),
  (exceptionId, "Exception", some objectId),
  (standardErrorId, "StandardError", some exceptionId),
  (runtimeErrorId, "RuntimeError", some standardErrorId),
  (argumentErrorId, "ArgumentError", some standardErrorId),
  (typeErrorId, "TypeError", some standardErrorId),
  (nameErrorId, "NameError", some standardErrorId),
  (noMethodErrorId, "NoMethodError", some nameErrorId),
  (zeroDivisionErrorId, "ZeroDivisionError", some standardErrorId),
  (localJumpErrorId, "LocalJumpError", some standardErrorId),
  (frozenErrorId, "FrozenError", some runtimeErrorId),
  (indexErrorId, "IndexError", some standardErrorId),
  (keyErrorId, "KeyError", some indexErrorId),
  (rangeErrorId, "RangeError", some standardErrorId),
  (stopIterationId, "StopIteration", some indexErrorId),
  (notImplementedErrorId, "NotImplementedError", some scriptErrorId),
  (scriptErrorId, "ScriptError", some exceptionId),
  (procId, "Proc", some objectId)
]

/-- Builtin method table: class id → method names given by primitive rules.
    Builtin bid = "ClassName#name". Registered into each class's `methods`
    so lookup (incl. inheritance) is uniform. -/
def builtinMethods : List (ObjId × List String) := [
  (basicObjectId, ["==", "!", "!=", "equal?"]),
  -- Kernel/Object layer (Kernel folded into Object at L0)
  (objectId, ["==", "!=", "!", "equal?", "eql?", "class", "nil?", "inspect",
              "to_s", "freeze", "frozen?", "is_a?", "kind_of?", "instance_of?",
              "puts", "print", "p", "raise", "String", "block_given?"]),
  (nilClassId, ["to_s", "inspect", "nil?", "to_a", "&", "|"]),
  (trueClassId, ["to_s", "inspect", "&", "|"]),
  (falseClassId, ["to_s", "inspect", "&", "|"]),
  (integerId, ["+", "-", "*", "/", "%", "**", "-@", "==", "!=", "<", ">",
               "<=", ">=", "<=>", "to_s", "inspect", "to_i", "abs", "succ",
               "pred", "zero?", "positive?", "negative?", "even?", "odd?",
               "eql?", "hash"]),
  (floatId, ["+", "-", "*", "/", "-@", "==", "<", ">", "<=", ">=", "<=>",
             "to_s", "inspect", "to_i", "abs", "zero?", "nan?", "eql?"]),
  (stringId, ["+", "*", "==", "!=", "<", ">", "<=", ">=", "<=>", "length",
              "size", "to_s", "to_str", "inspect", "<<", "concat", "empty?",
              "include?", "reverse", "upcase", "downcase", "strip", "chomp",
              "start_with?", "end_with?", "eql?", "freeze", "frozen?", "dup",
              "to_sym", "[]"]),
  (symbolId, ["to_s", "inspect", "==", "to_sym", "to_proc"]),
  (arrayId, ["==", "!=", "[]", "[]=", "<<", "push", "pop", "shift", "unshift",
             "length", "size", "first", "last", "empty?", "include?", "+",
             "-", "*", "inspect", "to_s", "to_a", "reverse", "join", "flatten",
             "compact", "uniq", "concat", "index", "eql?", "dup", "freeze",
             "frozen?", "sort", "min", "max", "sum"]),
  (hashId, ["==", "[]", "[]=", "length", "size", "empty?", "key?", "has_key?",
            "include?", "member?", "keys", "values", "delete", "fetch",
            "inspect", "to_s", "dup"]),
  (exceptionId, ["message", "to_s", "inspect"]),
  (moduleId, ["===", "name", "to_s", "inspect", "==", "ancestors"]),
  (classId, ["new"]),
  -- Proc#call/()/[]/yield are intercepted in `invoke` (they push a block
  -- frame, which a pure builtin cannot); only the pure introspectors are
  -- registered here.
  (procId, ["lambda?", "to_proc"])
]

def mkClassObj (name : String) (sup : Option ObjId) : Object :=
  { klass := classId,
    payload := .cls { superclass := sup, name := name } }

def install (h : Heap) (cls : ObjId) (names : List String) : Heap :=
  match h.classPayload? cls with
  | Option.none => h
  | some c =>
    let cname := c.name
    let methods := names.foldl (init := c.methods) fun ms n =>
      (n, { params := [], body := .nil, owner := cls,
            builtin := some s!"{cname}#{n}" : MethodDef }) :: ms
    h.setClassPayload cls { c with methods }

/-- H₀: bootstrap classes at their fixed ids, builtins installed, every class
    registered as a constant on Object, `main` allocated last. -/
def initHeap : Heap := Id.run do
  -- classTable is in id order except ScriptError; build by sorted id.
  let sorted := classTable.toArray.qsort (fun a b => a.1 < b.1)
  let mut h : Heap := ⟨#[]⟩
  for (_, name, sup) in sorted do
    let (_, h') := h.alloc (mkClassObj name sup)
    h := h'
  -- main object
  let (_, h') := h.alloc { klass := objectId }
  h := h'
  -- install builtins
  for (cls, names) in builtinMethods do
    h := install h cls names
  -- register constants on Object
  match h.classPayload? objectId with
  | some c =>
    let consts := classTable.map (fun (o, name, _) => (name, Value.ref o))
    h := h.setClassPayload objectId { c with consts }
  | Option.none => pure ()
  return h

end Boot

/-! ## Pure object-model operations (artifact 01 §4, 02 §1–2) -/

/-- Direct class of a value (CLASS-*). Eigenclasses: none at L0. -/
def classOf (h : Heap) : Value → ObjId
  | .ref o => match (h.get o).eigen with
    | some e => e
    | Option.none => (h.get o).klass
  | .int _ => Boot.integerId
  | .flt _ => Boot.floatId
  | .sym _ => Boot.symbolId
  | .bool true => Boot.trueClassId
  | .bool false => Boot.falseClassId
  | .nil => Boot.nilClassId

/-- Ancestor chain = superclass walk (no mixins at L0). Fuel-bounded against
    cyclic heaps (unreachable from H₀, but stepFn must be total). -/
def ancestors (h : Heap) (k : ObjId) : List ObjId :=
  go k (h.objs.size + 1)
where
  go (k : ObjId) : Nat → List ObjId
    | 0 => []
    | fuel + 1 =>
      match h.classPayload? k with
      | Option.none => [k]
      | some c => k :: (match c.superclass with
        | some s => go s fuel
        | Option.none => [])

/-- LOOKUP: first module in `ancestors (classOf v)` defining `m` directly,
    returned with its owner (needed for `super`, artifact 02 §2). -/
def lookup (h : Heap) (v : Value) (m : String) : Option (ObjId × MethodDef) :=
  go (ancestors h (classOf h v))
where
  go : List ObjId → Option (ObjId × MethodDef)
    | [] => Option.none
    | k :: rest =>
      match h.classPayload? k with
      | some c =>
        match c.methods.find? (·.1 == m) with
        | some (_, md) => some (k, md)
        | Option.none => go rest
      | Option.none => go rest

/-- `is_a?` test: does `v`'s ancestor chain include class `k`? -/
def isA (h : Heap) (v : Value) (k : ObjId) : Bool :=
  (ancestors h (classOf h v)).contains k

/-- Class name (for error messages / inspect). -/
def className (h : Heap) (k : ObjId) : String :=
  match h.classPayload? k with
  | some c => c.name
  | Option.none => "Object"

/-- Look up a constant on Object (L0: flat toplevel namespace,
    artifact 03's two-phase lookup degenerates to this). -/
def constLookup (h : Heap) (name : String) : Option Value :=
  match h.classPayload? Boot.objectId with
  | some c => (c.consts.find? (·.1 == name)).map (·.2)
  | Option.none => Option.none

def constSet (h : Heap) (name : String) (v : Value) : Heap :=
  match h.classPayload? Boot.objectId with
  | some c =>
    h.setClassPayload Boot.objectId
      { c with consts := (name, v) :: c.consts.filter (·.1 != name) }
  | Option.none => h

/-- Set constant `name` on class object `cls` (its own namespace, artifact 03).
    A `casgn` inside `class C … end` writes to `C`, not the flat toplevel. -/
def constSetIn (h : Heap) (cls : ObjId) (name : String) (v : Value) : Heap :=
  match h.classPayload? cls with
  | some c =>
    h.setClassPayload cls
      { c with consts := (name, v) :: c.consts.filter (·.1 != name) }
  | Option.none => h

/-- Constant lookup from cref `cls`: the *inheritance* phase of artifact 03's
    two-phase rule — walk `cls`'s ancestors (which bottoms out at Object, the
    toplevel namespace). The lexical phase (cref nesting) is not modeled at L0;
    `cls` is the innermost enclosing class (`defmod`). -/
def constLookupFrom (h : Heap) (cls : ObjId) (name : String) : Option Value :=
  (ancestors h cls).firstM fun k =>
    match h.classPayload? k with
    | some c => (c.consts.find? (·.1 == name)).map (·.2)
    | Option.none => Option.none

/-- Install a method (def'). Returns the updated heap. -/
def defineMethod (h : Heap) (cls : ObjId) (name : String) (md : MethodDef) : Heap :=
  match h.classPayload? cls with
  | some c =>
    h.setClassPayload cls
      { c with methods := (name, md) :: c.methods.filter (·.1 != name) }
  | Option.none => h

end RubyCore
