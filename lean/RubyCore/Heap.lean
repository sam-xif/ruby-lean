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
import RubyCore.MT

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

/-- Method visibility (artifact 02 §5, L71). `protected` differs from `private`
    only in the dispatch check: an explicit receiver is allowed when the *caller's*
    `self` is a kind of the method's owner. -/
inductive Visibility where
  | pub | priv | prot
deriving Repr, DecidableEq, Inhabited

structure MethodDef where
  params : List Param
  body : Expr
  owner : ObjId
  /-- Lexical constant scope captured at definition (innermost enclosing
      class/module first), threaded to the activation frame for cref-scoped
      constant lookup (artifact 03 §4). Empty = toplevel/`[Object]`. -/
  cref : List ObjId := []
  /-- The name `super` searches for from inside this body. Normally the name the
      method is installed under, but an **alias** keeps the *original* name: in
      CRuby `alias_method :b, :a` then `super` inside `b` looks for `a` in the
      superclass, not `b` [V] (L108). The sorbet-runtime shim depends on this —
      it aliases a method aside as `__t_unchecked_x` and a `super` in the body
      must still reach `x`'s parent. -/
  superName : Option String := none
  /-- `some bid` marks an axiomatized builtin (artifact 01 §2); `body` is
      then ignored and Builtins.lean supplies the behavior keyed on `bid`. -/
  builtin : Option String := none
  visibility : Visibility := .pub
  /-- `define_method`: the frame this body **closes over** — free variables
      resolve up its `captured` chain, exactly as in the block it came from
      (L64). `none` for an ordinary `def`, whose body has no enclosing scope.
      `Nat` rather than `FrameId` to avoid the Machine import cycle (as
      `Closure` does). -/
  capturedFrame : Option Nat := none
  /-- Names the body binds **itself** rather than up the `capturedFrame` chain:
      the block-locals of the block a `define_method` was built from, explicit
      (`|;x|`) and parse-time-implicit (C35) alike. Empty for an ordinary `def`,
      whose frame has no enclosing scope to clobber. Pre-declared nil in the
      activation, next to the `localsB` formals that need the same treatment for
      the same reason (L125). -/
  declared : List String := []
  /-- Defined by the **prelude** (the core library written in RubyCore itself,
      `prelude/prelude.rb`) rather than by the program under test. Such a method
      *is* the model of the CRuby builtin of the same name, so it suppresses the
      "unmodeled builtin would shadow" gate for its own name (L62). -/
  fromPrelude : Bool := false
  /-- `undef name` tombstone (artifact 02): the entry exists so the ancestor
      walk stops here (blocking any inherited definition), but dispatch treats
      it as a miss → `NoMethodError`/`method_missing`. -/
  undefined : Bool := false
deriving Inhabited

structure ClassPayload where
  superclass : Option ObjId
  methods : List (String × MethodDef) := []
  consts : List (String × Value) := []
  /-- Constants declared `private_constant`: still visible to lexical lookup
      from inside the module, invisible to `A::B` from outside (L104). -/
  privateConsts : List String := []
  name : String
  isModule : Bool := false
  /-- Modules mixed in via `include` (most-recently-included **last**); inserted
      into the ancestor chain just above this class, most-recent first (MRO). -/
  includes : List ObjId := []
  /-- Class variables `@@x` (artifact 03 §3): stored on the class/module, looked
      up along the ancestor chain, and *assigned* in the highest ancestor that
      already has one (L67). -/
  cvars : List (String × Value) := []
  /-- Modules mixed in via `prepend` (most-recently-prepended **last**); inserted
      *below* this class in the chain, so their methods win over the class's own
      and `super` from them reaches the class (artifact 02 §1, L65). -/
  prepends : List ObjId := []
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
  params : List Param
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
  /-- A `Random` instance's MT19937 state (mutated in place by `#rand`). -/
  | rng (s : MT.State)
  /-- A `Range` (`lo..hi` / `lo...hi`): endpoints and exclusivity. -/
  | range (lo hi : Value) (excl : Bool)
  /-- A `Regexp`: the pattern source and the option word, exactly as
      `Regexp.new` received them. The compiled `Rx.Regex` is *not* stored — it
      is re-parsed at each use, so the heap stays a plain data structure and no
      `Regex` value has to be `Inhabited`/`Repr`-able alongside `Value`. Parsing
      is linear and the patterns are short. -/
  | regexp (src : String) (opts : Nat)
  /-- A `MatchData`: the subject string, the whole-match span, the capture
      spans (index 0 is the whole match), and the named-group map. Character
      offsets throughout, matching Ruby. -/
  | mdata (subject : String) (caps : Array (Option (Nat × Nat)))
      (names : List (String × Nat))
deriving Inhabited

/-- A Hash's default for missing keys: `Hash.new(v)` stores a static value `val v`;
    `Hash.new { |h,k| … }` stores a default_proc `prc p` (the Proc's ObjId), called
    on a `[]` miss. `none` (the field default) means a miss returns `nil`. -/
inductive HashDefault where
  | val (v : Value)
  | prc (p : ObjId)
deriving Inhabited

structure Object where
  klass : ObjId
  ivars : List (String × Value) := []
  frozen : Bool := false
  eigen : Option ObjId := none
  payload : Payload := .none
  /-- Present only on Hash objects created with a default (value or proc). -/
  hashDflt : Option HashDefault := none
  /-- String objects only: this String is **ASCII-8BIT** (`String#b`,
      `Integer#chr` above 127). Then the invariant is that every character of the
      `.str` payload is below 256 and *is* one byte — so `length`, `[]`, `ord`,
      `each_char` and the matcher all operate per byte with no other change, which
      is exactly what `Purl.encode` needs. A field on the object rather than on
      the payload, because the payload's constructor arity is matched in ~40
      places and an encoding is a property of the object anyway (L117). -/
  binary : Bool := false
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
def randomId : ObjId := 30
def mathId : ObjId := 31
def rangeId : ObjId := 32
/-- `Kernel` — a real module in `Object`'s ancestor chain (L65). Its *methods*
    still live directly on Object at L0, so the module itself is empty; what it
    buys is a faithful `ancestors` (`[Object, Kernel, BasicObject]`) and a
    reopened `Kernel` resolving through the ordinary MRO. -/
def kernelId : ObjId := 33
/-- `Numeric` — Integer's and Float's real superclass (and where `Comparable` is
    mixed in), so `1.is_a?(Numeric)` and `Integer.ancestors` are faithful (L65).
    Carries no methods of its own at L0. -/
def numericId : ObjId := 34
/-- `UncaughtThrowError < ArgumentError` — a `throw` with no matching `catch`
    (L69). -/
def uncaughtThrowErrorId : ObjId := 35
/-- `Regexp` (L101). -/
def regexpId : ObjId := 36
/-- `MatchData` (L101) — the object `Regexp#match` returns and `$~` holds. -/
def matchDataId : ObjId := 37
/-- `RegexpError < StandardError` — raised by `Regexp.new` on a bad pattern. -/
def regexpErrorId : ObjId := 38
/-- Toplevel self (`main`), an ordinary Object instance. **Must stay last**:
    `initHeap` allocates every `classTable` entry densely and then `main`, so
    `mainId = classTable.length`. Adding a bootstrap class means bumping this. -/
def mainId : ObjId := 39

/-- (id, name, superclass) for every bootstrap class, in id order. -/
def classTable : List (ObjId × String × Option ObjId) := [
  (basicObjectId, "BasicObject", Option.none),
  (objectId, "Object", some basicObjectId),
  (moduleId, "Module", some objectId),
  (classId, "Class", some moduleId),
  (nilClassId, "NilClass", some objectId),
  (trueClassId, "TrueClass", some objectId),
  (falseClassId, "FalseClass", some objectId),
  (integerId, "Integer", some numericId),
  (floatId, "Float", some numericId),
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
  (procId, "Proc", some objectId),
  (randomId, "Random", some objectId),
  (mathId, "Math", some objectId),   -- modeled as a constant with singleton fns
  (rangeId, "Range", some objectId),
  (kernelId, "Kernel", Option.none),     -- patched to a module in `initHeap`
  (numericId, "Numeric", some objectId),
  (uncaughtThrowErrorId, "UncaughtThrowError", some argumentErrorId),
  (regexpId, "Regexp", some objectId),
  (matchDataId, "MatchData", some objectId),
  (regexpErrorId, "RegexpError", some standardErrorId)
]

/-- Builtin method table: class id → method names given by primitive rules.
    Builtin bid = "ClassName#name". Registered into each class's `methods`
    so lookup (incl. inheritance) is uniform. -/
def builtinMethods : List (ObjId × List String) := [
  (basicObjectId, ["==", "!", "equal?"]),
  -- Kernel/Object layer (Kernel folded into Object at L0)
  (objectId, ["==", "!", "equal?", "eql?", "class", "nil?", "inspect",
              "to_s", "freeze", "frozen?", "is_a?", "kind_of?", "instance_of?",
              "puts", "print", "p", "raise", "String", "block_given?", "rand",
              "require", "require_relative", "__unsupported__", "dup", "clone",
              "__user_defines?", "__default_inspect?", "__write", "__addr_str",
              "__any_to_s", "__match_to_caller",
              "__coerce_failed", "__cmp_failed",
              "initialize"]),
  (nilClassId, ["to_s", "inspect", "nil?", "to_a", "&", "|", "dup", "clone"]),
  (trueClassId, ["to_s", "inspect", "&", "|", "dup", "clone"]),
  (falseClassId, ["to_s", "inspect", "&", "|", "dup", "clone"]),
  (integerId, ["+", "-", "*", "/", "%", "**", "-@", "==", "<", ">",
               "<=", ">=", "<=>", "to_s", "inspect", "to_i", "to_f", "abs", "succ",
               "pred", "zero?", "positive?", "negative?", "even?", "odd?", "chr",
               "round", "ceil", "floor", "truncate", "divmod", "nonzero?",
               "eql?", "hash", "dup", "clone"]),
  (floatId, ["round", "ceil", "floor", "truncate", "divmod", "nonzero?",
             "+", "-", "*", "/", "%", "**", "-@", "==", "<", ">", "<=", ">=", "<=>",
             "to_s", "inspect", "to_i", "to_f", "abs", "zero?", "nan?", "eql?",
             "dup", "clone"]),
  (stringId, ["+", "*", "==", "<", ">", "<=", ">=", "<=>", "length",
              "size", "to_s", "to_str", "inspect", "<<", "concat", "empty?",
              "include?", "reverse", "upcase", "downcase", "strip", "chomp",
              "start_with?", "end_with?", "eql?", "freeze", "frozen?", "dup", "clone",
              "initialize", "+@", "-@",
              "to_sym", "[]"]),
  (symbolId, ["to_s", "inspect", "==", "to_sym", "to_proc", "dup", "clone"]),
  (arrayId, ["==", "[]", "[]=", "<<", "push", "pop", "shift", "unshift",
             "length", "size", "first", "last", "empty?", "include?", "+",
             "-", "*", "&", "|", "inspect", "to_s", "to_a", "reverse", "join", "flatten",
             "compact", "uniq", "concat", "index", "eql?", "dup", "clone", "freeze",
             "initialize",
             "frozen?", "sort", "min", "max", "sum"]),
  (hashId, ["==", "[]", "[]=", "length", "size", "empty?", "key?", "has_key?",
            "freeze", "frozen?",
            "include?", "member?", "keys", "values", "delete", "fetch",
            "inspect", "to_s", "dup", "clone", "merge", "initialize"]),
  (exceptionId, ["message", "to_s", "inspect", "dup", "clone", "initialize"]),
  (classId, ["superclass"]),
  (stringId, ["try_convert"]),
  (moduleId, ["===", "name", "to_s", "inspect", "==", "ancestors",
              "private_constant", "public_constant"]),
  (classId, ["new", "allocate", "__range_new_unchecked"]),
  -- Proc#call/()/[]/yield are intercepted in `invoke` (they push a block
  -- frame, which a pure builtin cannot); only the pure introspectors are
  -- registered here.
  (procId, ["lambda?", "to_proc"]),
  (randomId, ["rand"]),
  (rangeId, ["first", "last", "begin", "end", "exclude_end?", "inspect", "to_s"]),
  (stringId, ["=~", "match", "match?", "scan", "__sub_rep", "__gsub_rep", "split", "to_i",
              "__search_at",
              "ord", "chars", "to_f",
              "__binary?", "__bytes", "__as_binary", "__as_utf8",
              "__force_binary", "__force_utf8"]),
  (regexpId, ["escape", "quote", "union", "source", "options", "match", "match?", "=~", "===", "inspect",
              "to_s", "names", "==", "eql?", "hash"]),
  (matchDataId, ["[]", "captures", "named_captures", "names", "begin", "end",
                 "pre_match", "post_match", "to_a", "size", "length", "to_s",
                 "inspect", "values_at"])
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

/-- Reducible insertion sort by id (`.1`), replacing `Array.qsort` in `initHeap`.
    `qsort` is opaque to the kernel, so any `decide`/`rfl` over `initHeap` got
    stuck; a structural `def` reduces (metatheory needs concrete boot-heap facts,
    L55). Ids are distinct, so this yields the same strictly-ascending order. -/
def insertById (x : ObjId × String × Option ObjId) :
    List (ObjId × String × Option ObjId) → List (ObjId × String × Option ObjId)
  | [] => [x]
  | y :: ys => if Nat.ble x.1 y.1 then x :: y :: ys else y :: insertById x ys

def sortById :
    List (ObjId × String × Option ObjId) → List (ObjId × String × Option ObjId)
  | [] => []
  | x :: xs => insertById x (sortById xs)

/-- H₀: bootstrap classes at their fixed ids, builtins installed, every class
    registered as a constant on Object, `main` allocated last.
    Written as pure `List.foldl` (no `Id.run do`/`for`/`qsort`) so the whole
    heap reduces in the kernel — see `insertById`/L55. -/
def initHeap : Heap :=
  -- classes allocated in ascending-id order ⇒ alloc index = id.
  let hClasses := (sortById classTable).foldl
    (fun h (e : ObjId × String × Option ObjId) => (h.alloc (mkClassObj e.2.1 e.2.2)).2)
    (⟨#[]⟩ : Heap)
  -- main object (allocated last, after all classes)
  let hMain := (hClasses.alloc { klass := objectId }).2
  -- install builtins
  let hBuiltins := builtinMethods.foldl (fun h (e : ObjId × List String) => install h e.1 e.2) hMain
  -- Kernel is a *module*, and `Object` includes it (L65): allocated as an
  -- ordinary classTable entry (so ids stay dense and `initHeap` stays a plain
  -- fold), then patched here.
  let kernObj : Object :=
    { klass := moduleId,
      payload := .cls { superclass := Option.none, name := "Kernel", isModule := true } }
  let hKern := hBuiltins.set kernelId kernObj
  let hBuiltins := match hKern.classPayload? objectId with
    | some c => hKern.setClassPayload objectId { c with includes := [kernelId] }
    | Option.none => hKern
  -- `Float::NAN` / `Float::INFINITY`: real constants of the class object, not
  -- methods, so they belong in the boot heap rather than in a rule (L109).
  let hBuiltins := match hBuiltins.classPayload? floatId with
    | some c => hBuiltins.setClassPayload floatId
        { c with consts := c.consts ++
            [("NAN", Value.flt (0.0 / 0.0)), ("INFINITY", Value.flt (1.0 / 0.0))] }
    | Option.none => hBuiltins
  -- register every class name as a constant on Object
  match hBuiltins.classPayload? objectId with
  | some c =>
    hBuiltins.setClassPayload objectId
      { c with consts := classTable.map (fun (o, name, _) => (name, Value.ref o)) }
  | Option.none => hBuiltins

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

/-- The *real* class of a value — skips the eigenclass (what `Object#class` and
    `instance_of?` report, unlike dispatch's `classOf`). -/
def realClassOf (h : Heap) : Value → ObjId
  | .ref o => (h.get o).klass
  | v => classOf h v

/-- A module's own ancestor list: itself, then its `include`d modules
    (most-recent first), recursively.

    **Fuel-bounded rather than `partial`** (L73): a `partial def` is opaque to the
    kernel, so once *any* class in a chain has mixins — and `Object` now includes
    `Kernel` (L65), so every chain does — `ancestors` would no longer reduce and
    every `decide`/`rfl` in the metatheory over a dispatch would get stuck. -/
def modAncestors (h : Heap) (mo : ObjId) : List ObjId :=
  go mo (h.objs.size + 1)
where
  go (mo : ObjId) : Nat → List ObjId
    | 0 => [mo]
    | fuel + 1 =>
      mo :: (match h.classPayload? mo with
        | some c => c.includes.reverse.flatMap (fun i => go i fuel)
        | Option.none => [])

/-- Ancestor chain (MRO): the superclass walk, with each class's `include`d
    modules spliced in just above it (most-recent-first, modules-of-modules
    expanded), then de-duplicated keeping the first (highest-priority)
    occurrence. With no mixins this is exactly the old superclass walk, so it is
    behaviour-preserving on the mixin-free fragment. Fuel-bounded for totality. -/
def ancestors (h : Heap) (k : ObjId) : List ObjId :=
  (go k (h.objs.size + 1)).foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) []
where
  go (k : ObjId) : Nat → List ObjId
    | 0 => []
    | fuel + 1 =>
      match h.classPayload? k with
      | Option.none => [k]
      | some c =>
        c.prepends.reverse.flatMap (modAncestors h) ++
        (k :: c.includes.reverse.flatMap (modAncestors h)) ++
        (match c.superclass with
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

/-- Fake but deterministic "address" for default `Object#inspect` and for every
    message that renders an object by address — the difftest observation
    normalizes `0x…` on both sides by occurrence order, so only distinctness +
    ordering matter. Lives here, below `className`'s caller set, because an
    **anonymous** class is rendered by address in error messages too (L124). -/
def fakeAddr (o : ObjId) : String :=
  let hex := String.ofList (Nat.toDigits 16 o)
  "0x" ++ String.ofList (List.replicate (16 - hex.length) '0') ++ hex

/-- Class name (for error messages / inspect). An **anonymous** class or module
    (`Class.new`, `Module.new`) has an empty `name`, and CRuby renders it by
    address wherever a name is wanted — `0 + Class.new.new` says
    `#<Class:0x…> can't be coerced into Integer`, not `` `` can't be coerced``.
    Every message built from `className` inherits that, so the fallback belongs
    here and not at ~20 call sites (L124). `Module#name` still answers `nil`:
    it tests `c.name.isEmpty` itself rather than going through here. -/
def className (h : Heap) (k : ObjId) : String :=
  match h.classPayload? k with
  | some c =>
    if c.name.isEmpty then
      s!"#<{if c.isModule then "Module" else "Class"}:{fakeAddr k}>"
    else c.name
  | Option.none => "Object"

/-- CRuby's `rb_any_to_s`: how an object is named where a *class* would be named
    by `className` — `#<Foo:0x…>`, ignoring any user `to_s`/`inspect` and any
    ivars. The one caller is the **eigenclass**'s own name (`o.singleton_class`
    is `#<Class:#<Foo:0x…>>`), which is why this is not `Repr.inspect`: it must
    be a pure heap function, and CRuby does not dispatch here either [V]. -/
def anyToS (h : Heap) (o : ObjId) : String :=
  match h.classPayload? o with
  | some _ => className h o
  | Option.none => s!"#<{className h (h.get o).klass}:{fakeAddr o}>"

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

/-- A class/module's *own* constants (no ancestor walk) — the lexical phase of
    artifact 03's two-phase constant lookup. -/
def constOwn (h : Heap) (cls : ObjId) (name : String) : Option Value :=
  (h.classPayload? cls).bind fun c => (c.consts.find? (·.1 == name)).map (·.2)

/-- Constant lookup from cref `cls`: the *inheritance* phase of artifact 03's
    two-phase rule — walk `cls`'s ancestors (which bottoms out at Object, the
    toplevel namespace). The lexical phase (cref nesting) is not modeled at L0;
    `cls` is the innermost enclosing class (`defmod`). -/
def constLookupFrom (h : Heap) (cls : ObjId) (name : String) : Option Value :=
  (ancestors h cls).firstM fun k =>
    match h.classPayload? k with
    | some c => (c.consts.find? (·.1 == name)).map (·.2)
    | Option.none => Option.none

/-- `@@x` read from lexical scope `scope`: the first ancestor (class or included
    module) that defines it (artifact 03 §3). -/
def cvarLookupIn (h : Heap) (scope : ObjId) (name : String) : Option Value :=
  (ancestors h scope).firstM fun k =>
    (h.classPayload? k).bind fun c => (c.cvars.find? (·.1 == name)).map (·.2)

/-- `@@x = v` from lexical scope `scope`: writes to the **highest** ancestor that
    already defines `@@x` (so a subclass assignment updates the superclass's
    variable [V]), else creates it on `scope` itself. -/
def cvarSetIn (h : Heap) (scope : ObjId) (name : String) (v : Value) : Heap :=
  let chain := ancestors h scope
  let owners := chain.filter fun k =>
    match h.classPayload? k with
    | some c => c.cvars.any (·.1 == name)
    | Option.none => false
  let target := owners.getLast?.getD scope
  match h.classPayload? target with
  | some c =>
    h.setClassPayload target
      { c with cvars := (name, v) :: c.cvars.filter (·.1 != name) }
  | Option.none => h

/-- Install a method (def'). Returns the updated heap. -/
def defineMethod (h : Heap) (cls : ObjId) (name : String) (md : MethodDef) : Heap :=
  match h.classPayload? cls with
  | some c =>
    h.setClassPayload cls
      { c with methods := (name, md) :: c.methods.filter (·.1 != name) }
  | Option.none => h

/-- `undef name` on `cls`: install an `undefined` tombstone (artifact 02) so the
    ancestor walk stops here even if a superclass defines `name`. -/
def undefMethod (h : Heap) (cls : ObjId) (name : String) : Heap :=
  defineMethod h cls name { params := [], body := .nil, owner := cls, undefined := true }

end RubyCore
