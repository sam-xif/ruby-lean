/-
Values, objects and the heap, and the pure operations on them (Semantics 01–02).

* `Value` is an immediate (integer, float, symbol, boolean, nil) or a reference
  to a heap object. `ObjId` is a dense index into `Heap.objs`: ids are assigned
  in allocation order and never reused.
* `Object` carries its class, its instance variables, a frozen flag and a
  payload. A class is an object whose payload holds its superclass, its
  included and prepended modules, its method table and its constant table.
* `Boot.initHeap` is the initial heap: `BasicObject`, `Object`, `Module`,
  `Class`, `Kernel` and the other core classes, with the builtin methods
  registered in their method tables.
* `classOf`, `ancestors`, method lookup and constant lookup are pure functions
  of the heap.

The step function touches the heap only through the functions defined here, so
facts about them can be proved without mentioning the machine.
-/
import RubyCore.Syntax
import RubyCore.Numeric.MT

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
    immediates. This is `equal?`, not `==` (Semantics 01 §6). Type-strict:
    `1` and `1.0` are NOT `eql?`. -/
def Value.identEq : Value → Value → Bool
  | .ref a, .ref b => a == b
  | .int a, .int b => a == b
  | .flt a, .flt b => a == b || (a.isNaN && b.isNaN && false)  -- NaN never equal
  | .sym a, .sym b => a == b
  | .bool a, .bool b => a == b
  | .nil, .nil => true
  | _, _ => false

/-- Truthiness (Semantics 01 §6): exactly false and nil are falsey. -/
def Value.truthy : Value → Bool
  | .bool false => false
  | .nil => false
  | _ => true

/-- Method visibility (Semantics 02 §5). `protected` differs from `private`
    only in the dispatch check: an explicit receiver is allowed when the *caller's*
    `self` is a kind of the method's owner. -/
inductive Visibility where
  | pub | priv | prot
deriving Repr, DecidableEq, Inhabited

structure MethodDef where
  /-- A method installed from a captured for callback still shares its loop locals. -/
  fromBlock : Bool := false
  forTargets : Option (List (TargetKind × String)) := none
  forMultiple : Bool := false
  params : List Param
  body : Expr
  owner : ObjId
  /-- Lexical target of nested definitions; distinct from the dispatch owner. -/
  definee : Option ObjId := none
  /-- A define_method body shares the defining block's visibility context,
      independently of whether its local-variable capture can be erased. -/
  definitionFrame : Option Nat := none
  /-- Lexical constant scope captured at definition (innermost enclosing
      class/module first), threaded to the activation frame for cref-scoped
      constant lookup (Semantics 03 §4). Empty = toplevel/`[Object]`. -/
  cref : List ObjId := []
  /-- The name `super` searches for from inside this body. Normally the name the
      method is installed under, but an **alias** keeps the *original* name: in
      CRuby `alias_method :b, :a` then `super` inside `b` looks for `a` in the
      superclass, not `b` [V]. The sorbet-runtime shim depends on this —
      it aliases a method aside as `__t_unchecked_x` and a `super` in the body
      must still reach `x`'s parent. -/
  superName : Option String := none
  /-- A class-side alias retains the lookup context of its original body,
      including a repeated module occurrence below a subclass's occurrence. -/
  superScope : Option ObjId := none
  /-- `some bid` marks an axiomatized builtin (Semantics 01 §2); `body` is
      then ignored and Builtins.lean supplies the behavior keyed on `bid`. -/
  builtin : Option String := none
  visibility : Visibility := .pub
  /-- An inherited visibility override resolves its body again on each lookup. -/
  visibilityOnly : Bool := false
  /-- `define_method`: the frame this body **closes over** — free variables
      resolve up its `captured` chain, exactly as in the block it came from
. `none` for an ordinary `def`, whose body has no enclosing scope.
      `Nat` rather than `FrameId` to avoid the Machine import cycle (as
      `Closure` does). -/
  capturedFrame : Option Nat := none
  /-- Names the body binds **itself** rather than up the `capturedFrame` chain:
      the block-locals of the block a `define_method` was built from, explicit
      (`|;x|`) and parse-time-implicit (C35) alike. Empty for an ordinary `def`,
      whose frame has no enclosing scope to clobber. Pre-declared nil in the
      activation, next to the `localsB` formals that need the same treatment for
      the same reason. -/
  declared : List String := []
  /-- Defined by the **prelude** (the core library written in RubyCore itself,
      `prelude/prelude.rb`) rather than by the program under test. Such a method
      *is* the model of the CRuby builtin of the same name, so it suppresses the
      "unmodeled builtin would shadow" gate for its own name. -/
  fromPrelude : Bool := false
  /-- `undef name` tombstone (Semantics 02): the entry exists so the ancestor
      walk stops here (blocking any inherited definition), but dispatch treats
      it as a miss → `NoMethodError`/`method_missing`. -/
  undefined : Bool := false
deriving Inhabited

structure ClassPayload where
  superclass : Option ObjId
  /-- Canonical path used by model library code, independent of the object's
      Ruby name (a feature can reopen an aliased module). Inventories apply only
      to these objects, never to an unrelated user module with that name. -/
  libraryNamespace : Option String := none
  methods : List (String × MethodDef) := []
  consts : List (String × Value) := []
  /-- Constants declared `private_constant`: still visible to lexical lookup
      from inside the module, invisible to `A::B` from outside. -/
  privateConsts : List String := []
  name : String
  /-- A nonempty path can still contain an anonymous ancestor. Permanent paths
      survive later aliases; temporary paths are replaced when a namespace is
      bound under a permanent parent. Empty names are never permanent. -/
  namePermanent : Bool := true
  isModule : Bool := false
  /-- Class.allocate has no superclass and has not run Class#initialize. -/
  initialized : Bool := true
  /-- CRuby caches its superclass index. A named subclass of an uninitialized
      class has a superclass link but no completed index, even after its parent
      is later initialized. -/
  ancestryReady : Bool := true
  /-- Allocation is copied at class creation, independently of live ancestors. -/
  allocatorUnavailable : Bool := false
  /-- A singleton class renders its attached object using the current heap.
      Its constant name (if any) remains separate from that display name. -/
  attached : Option ObjId := none
  /-- Modules mixed in via `include` (most-recently-included **last**); inserted
      into the ancestor chain just above this class, most-recent first (MRO). -/
  includes : List ObjId := []
  /-- Class variables `@@x` (Semantics 03 §3): stored on the class/module, looked
      up along the ancestor chain, and *assigned* in the highest ancestor that
      already has one. -/
  cvars : List (String × Value) := []
  /-- Modules mixed in via `prepend` (most-recently-prepended **last**); inserted
      *below* this class in the chain, so their methods win over the class's own
      and `super` from them reaches the class (Semantics 02 §1). -/
  prepends : List ObjId := []
deriving Inhabited

/-- A block/proc/lambda closure (Semantics 04 §1). Frame identity supplies
    Essence's generative jump targets (sketch §1.1):
    - `captured` is the FrameId of the defining frame — free variables resolve
      up its chain and `self`/`defmod`/method-block are inherited from it.
      **`none` means the closure closes over nothing**, which is not the same as
      closing over frame `0`: the only such closures are the ones the model
      *invents* for `Symbol#to_proc` (`&:sym` and the builtin), and CRuby's
      answer there is a C-level Proc with no binding at all —
      `:upcase.to_proc.binding` raises and its `source_location` is `nil`
. Matches `Frame.captured`, which has been
      an `Option` all along (`Machine.lean`); before L266 this was a bare `Nat`
      and those two sites wrote `0`, a capture edge into the toplevel that the
      reference semantics does not have and that `books/Books/TypeSoundness/Conformance/`'s frame
      seal read as real.
    - `home` is the method activation that a non-lambda `return` unwinds to.
    - `lam` selects lambda semantics (strict arity, local `return`/`break`).
    FrameId = Nat (defined in Machine); kept as Nat here to avoid an import
    cycle — as `MethodDef.capturedFrame`, the other capture field, already does. -/
structure Closure where
  /-- The hidden for block assigns in the enclosing local environment. -/
  forTargets : Option (List (TargetKind × String)) := none
  forMultiple : Bool := false
  params : List Param
  locals : List String
  body : Expr
  captured : Option Nat
  home : Nat
  lam : Bool := false
  /-- The literal block's call boundary. Forwarding preserves this target;
      calling the Proc after that boundary exits makes break invalid. -/
  breakScope : Option Nat := none
  /-- Native external-iteration callback; it suspends instead of entering Ruby. -/
  enumYield : Option ObjId := none
  /-- The block was compiled as part of a modeled library. -/
  libraryOrigin : Bool := false
deriving Inhabited

inductive EnumSize where
  | unknown
  | fixed (v : Value)
  | callback (proc : Value)
  | receiverLength
  | receiverMethod
deriving Inhabited

structure EnumData where
  recv : Value
  method : String := "each"
  args : List Value := []
  kw : List (Value × Value) := []
  size : EnumSize := .unknown
deriving Inhabited

inductive Payload where
  | none
  | enumerator (data : Option EnumData)
  | chain (enums : List Value)
  | generator (proc : Option Value)
  | yielder (proc : Option Value) (brk : Option Nat)
  /-- Reduced exact fraction; denominator is positive, instances are frozen. -/
  | rational (num : Int) (den : Nat)
  | complex (real imag : Value)
  | str (s : String)
  | arr (elems : Array Value)
  | hsh (entries : Array (Value × Value))
  | cls (c : ClassPayload)
  /-- Exception message object; nil means the default class-name message. -/
  | exc (msg : Value)
  /-- A Proc (block/proc/lambda), Semantics 04 §1. -/
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
  /-- A **regular file** in the virtual filesystem (issue #7, step 1). `bytes`
      are the file's contents; a non-UTF-8 file reproduces CRuby's `inspect`
      through the same `binary` tag a String uses, or gates under the L118 net.
      Files are ordinary heap objects so `frozen`, `dup`, `inspect` and `is_a?`
      apply to them for free (artifact 01). Descriptors arrive in step 2; at
      step 1 the payload is pure data. -/
  | file (bytes : String)
  /-- A **directory** in the virtual filesystem (issue #7, step 1). `entries`
      maps a child's basename to its `ObjId`, in the boot-sorted order CRuby's
      `Dir.entries` reports; `parent` gives `..` one definition (the root's is
      `none`) rather than a textual collapse. A directory and a file are
      distinguished by payload, never by a string convention. -/
  | dir (entries : List (String × ObjId)) (parent : Option ObjId)
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
  /-- StopIteration's native result is not a Ruby instance variable. -/
  iterationResult : Value := .nil
  /-- Native UncaughtThrowError metadata is hidden from Ruby instance variables. -/
  throwTag : Value := .nil
  throwValue : Value := .nil
  /-- Internal write generation, used by suspended native iterators. -/
  revision : Nat := 0
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
      places and an encoding is a property of the object anyway. -/
  binary : Bool := false
deriving Inhabited

/-- ObjId = index; allocation appends (ids never reused, Semantics 01 §2). -/
structure Heap where
  objs : Array Object
  /-- Frozen native namespace-name Strings, shared by equal paths.
      Kept in the heap so prelude/runtime boundaries retain name identity.
      The Bool is the String's binary tag; general String interning is separate. -/
  nameStrings : List (String × Bool × ObjId) := []
deriving Inhabited

namespace Heap

def get? (h : Heap) (o : ObjId) : Option Object := h.objs[o]?

def get (h : Heap) (o : ObjId) : Object := h.objs.getD o default

def set (h : Heap) (o : ObjId) (obj : Object) : Heap :=
  { h with objs := h.objs.set! o { obj with revision := (h.get o).revision + 1 } }

def alloc (h : Heap) (obj : Object) : ObjId × Heap :=
  (h.objs.size, { h with objs := h.objs.push obj })

def classPayload? (h : Heap) (o : ObjId) : Option ClassPayload :=
  match (h.get o).payload with
  | .cls c => some c
  | _ => Option.none

def setClassPayload (h : Heap) (o : ObjId) (c : ClassPayload) : Heap :=
  h.set o { h.get o with payload := .cls c }

end Heap

/-! ## Bootstrap heap H₀ (Semantics 01 §4)

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
/-- `Kernel` — a real module in `Object`'s ancestor chain. Its *methods*
    still live directly on Object at L0, so the module itself is empty; what it
    buys is a faithful `ancestors` (`[Object, Kernel, BasicObject]`) and a
    reopened `Kernel` resolving through the ordinary MRO. -/
def kernelId : ObjId := 33
/-- `Numeric` — Integer's and Float's real superclass (and where `Comparable` is
    mixed in), so `1.is_a?(Numeric)` and `Integer.ancestors` are faithful.
    Carries no methods of its own at L0. -/
def numericId : ObjId := 34
/-- `UncaughtThrowError < ArgumentError` — a `throw` with no matching `catch`
. -/
def uncaughtThrowErrorId : ObjId := 35
/-- `Regexp`. -/
def regexpId : ObjId := 36
/-- `MatchData` — the object `Regexp#match` returns and `$~` holds. -/
def matchDataId : ObjId := 37
/-- `RegexpError < StandardError` — raised by `Regexp.new` on a bad pattern. -/
def regexpErrorId : ObjId := 38
def rationalId : ObjId := 39
def complexId : ObjId := 40
def enumeratorId : ObjId := 41
def generatorId : ObjId := 42
def yielderId : ObjId := 43
/-- `IO` — base class of file-like objects (issue #7 step 1). Registered so the
    lookup trichotomy stays accurate: a class that exists but whose descriptors
    are unmodeled must *gate* on the operation, not answer `NoMethodError`.
    (`File < IO`; descriptors themselves land in step 2.) -/
def ioId : ObjId := 44
/-- `File < IO` (issue #7 step 1) — where `File.read/write/exist?/file?/
    directory?/size` are installed. -/
def fileId : ObjId := 45
/-- `Dir` (issue #7 step 1) — the directory-listing class. `Dir.entries` is
    step 3; the class exists now so `Dir` in program text resolves to it. -/
def dirId : ObjId := 46
/-- Toplevel self (`main`), an ordinary Object instance. **Must stay last**:
    `initHeap` allocates every `classTable` entry densely and then `main`, so
    `mainId = classTable.length`. Adding a bootstrap class means bumping this. -/
def mainId : ObjId := 47

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
  (regexpErrorId, "RegexpError", some standardErrorId),
  (rationalId, "Rational", some numericId),
  (complexId, "Complex", some numericId),
  (enumeratorId, "Enumerator", some objectId),
  (generatorId, "Enumerator::Generator", some objectId),
  (yielderId, "Enumerator::Yielder", some objectId),
  (ioId, "IO", some objectId),
  (fileId, "File", some ioId),
  (dirId, "Dir", some objectId)
]

/-! ### The virtual filesystem fixture (issue #7 step 1)

The symbolic filesystem is **initial heap data H₀′**, not ambient OS state: a
small directory tree allocated at boot, exactly like the metaclass knot. The
interpreter never reaches outside the pure machine to read a file — it walks
this tree. Whether the tree would instead come from a directory snapshot is a
boot parameter (issue #7), not a runtime effect.

The fixture is allocated **after** main and the two realized eigenclasses, so
every fixed id (`classTable`, `mainId`) is unmoved. Its base is derived from the
class count rather than pinned: `classTable.length` classes, then `main`, then
the two eigenclasses of `BasicObject`/`Object` that `initHeap` realizes. A new
bootstrap class therefore shifts the fixture ids automatically and keeps
`resolve` pointing at the tree `initHeap` actually built. -/
def vfsBase : ObjId := classTable.length + 3
/-- `/tmp/readme.txt` — a regular file. -/
def vfsReadmeId : ObjId := vfsBase
/-- `/tmp/vfsdata/nums.txt` — a regular file in a subdirectory. -/
def vfsNumsId : ObjId := vfsBase + 1
/-- `/tmp/vfsdata` — a directory. -/
def vfsDataId : ObjId := vfsBase + 2
/-- `/tmp` — a directory under the root. A real, writable absolute path, so a
    differential harness can materialize the identical tree for CRuby. -/
def vfsTmpId : ObjId := vfsBase + 3
/-- `/` — the fixture root. Absolute paths resolve from here. -/
def vfsRootId : ObjId := vfsBase + 4

/-- Builtin method table: class id → method names given by primitive rules.
    Builtin bid = "ClassName#name". Registered into each class's `methods`
    so lookup (incl. inheritance) is uniform. -/
def builtinMethods : List (ObjId × List String) := [
  (enumeratorId, ["each", "next", "next_values", "peek", "peek_values", "feed", "rewind",
                  "size", "inspect", "dup", "clone", "initialize"]),
  (generatorId, ["each", "initialize"]),
  (yielderId, ["yield", "<<", "initialize"]),
  (stopIterationId, ["result"]),
  (basicObjectId, ["==", "!", "equal?", "initialize", "method_missing", "singleton_method_added",
                   "singleton_method_removed", "singleton_method_undefined"]),
  -- Kernel/Object layer (Kernel folded into Object at L0)
  (objectId, ["==", "===", "!", "equal?", "eql?", "class", "nil?", "itself", "inspect",
              "to_s", "freeze", "frozen?", "is_a?", "kind_of?", "instance_of?",
              "puts", "print", "p", "raise", "fail", "String", "block_given?", "rand",
              "require", "require_relative", "__unsupported__", "dup", "clone", "initialize_copy", "initialize_clone", "initialize_dup",
              "__user_defines?", "__default_inspect?", "__write", "__addr_str",
              "__any_to_s", "__match_to_caller", "respond_to_missing?", "instance_variables_to_inspect",
              "__coerce_failed", "__cmp_failed", "__coerce_defined?", "Rational", "Complex", "__complex_rect",
              "enum_for", "to_enum", "__enum_for", "__chain_init", "__chain_enums",
              "binding", "local_variables", "__forwardable_compile"]),
  (nilClassId, ["===", "to_s", "inspect", "nil?", "to_a", "&", "|", "dup", "clone"]),
  (trueClassId, ["===", "to_s", "inspect", "&", "|", "dup", "clone"]),
  (falseClassId, ["===", "to_s", "inspect", "&", "|", "dup", "clone"]),
  (integerId, ["+", "-", "*", "/", "%", "**", "-@", "==", "===", "<", ">", "[]",
               "<=", ">=", "<=>", "to_s", "inspect", "to_i", "to_f", "abs", "succ",
               "pred", "zero?", "positive?", "negative?", "even?", "odd?", "chr",
               "round", "ceil", "floor", "truncate", "divmod", "nonzero?",
               "eql?", "hash", "dup", "clone", "to_r", "to_c", "i", "times"]),
  (floatId, ["round", "ceil", "floor", "truncate", "divmod", "nonzero?",
             "+", "-", "*", "/", "%", "**", "-@", "==", "===", "<", ">", "<=", ">=", "<=>",
             "to_s", "inspect", "to_i", "to_f", "abs", "zero?", "nan?", "eql?",
             "dup", "clone", "to_r", "to_c", "i"]),
  (rationalId, ["numerator", "denominator", "to_s", "inspect", "to_i", "to_f", "to_r",
                "-@", "+@", "abs", "magnitude", "positive?", "negative?", "dup", "clone",
                "eql?", "==", "coerce", "+", "-", "*", "/", "quo", "<=>", "**",
                "floor", "ceil", "truncate", "to_c", "i"]),
  (complexId, ["real", "imag", "imaginary", "rect", "rectangular", "to_s", "inspect",
               "real?", "to_c", "dup", "clone", "coerce", "==", "eql?", "-@", "+@",
               "conj", "conjugate", "+", "-", "*", "/", "quo", "finite?", "infinite?"]),
  (stringId, ["+", "*", "==", "===", "<", ">", "<=", ">=", "<=>", "length",
              "size", "to_s", "to_str", "inspect", "<<", "concat", "empty?",
              "include?", "reverse", "upcase", "downcase", "strip", "chomp",
              "start_with?", "end_with?", "eql?", "freeze", "frozen?", "dup", "clone", "initialize_copy",
              "initialize", "+@", "-@",
              "to_sym", "[]"]),
  (symbolId, ["to_s", "inspect", "==", "===", "to_sym", "to_proc", "dup", "clone", "match?"]),
  (arrayId, ["==", "[]", "[]=", "<<", "push", "pop", "shift", "unshift",
             "length", "size", "first", "last", "empty?", "include?", "+",
             "-", "*", "&", "|", "inspect", "to_s", "to_a", "reverse", "join", "flatten",
             "compact", "uniq", "concat", "index", "eql?", "dup", "clone", "freeze", "initialize_copy",
             "initialize", "each", "each_index",
             "frozen?", "sort", "min", "max", "sum", "map", "collect"]),
  (hashId, ["==", "[]", "[]=", "length", "size", "empty?", "key?", "has_key?",
            "freeze", "frozen?", "each", "each_pair", "each_key", "each_value",
            "include?", "member?", "keys", "values", "delete", "fetch",
            "inspect", "to_s", "to_a", "dup", "clone", "merge", "initialize", "initialize_copy"]),
  -- `message` is deliberately absent: it is `to_s` in CRuby, so it must dispatch,
  -- and the prelude defines it.
  (exceptionId, ["to_s", "inspect", "dup", "clone", "initialize", "exception"]),
  (uncaughtThrowErrorId, ["to_s", "tag", "value", "__throw_metadata"]),
  (classId, ["superclass", "initialize", "inherited"]),
  (stringId, ["try_convert"]),
  (moduleId, ["===", "name", "to_s", "inspect", "==", "ancestors", "freeze", "initialize",
              "const_set", "const_added", "method_added", "method_removed", "method_undefined",
              "private_constant", "public_constant"]),
  (classId, ["new", "allocate", "__range_new_unchecked"]),
  -- Call markers resolve through ordinary lookup; the interpreter executes them
  -- by pushing a block frame, which a pure builtin cannot.
  (procId, ["lambda?", "to_proc", "call", "[]", "yield", "==="]),
  (randomId, ["rand"]),
  (rangeId, ["first", "last", "begin", "end", "exclude_end?", "inspect", "to_s"]),
  (stringId, ["=~", "match", "match?", "scan", "__sub_rep", "__gsub_rep", "split", "to_i",
              "__search_at",
              "ord", "chars", "to_f",
              "__binary?", "__bytes", "b", "__as_utf8",
              "__force_binary", "__force_utf8"]),
  (regexpId, ["escape", "quote", "union", "source", "options", "match", "match?", "=~", "===", "inspect",
              "to_s", "names", "==", "eql?", "hash"]),
  (matchDataId, ["[]", "captures", "named_captures", "names", "begin", "end",
                 "pre_match", "post_match", "to_a", "size", "length", "to_s",
                 "inspect", "values_at"]),
  (ioId, ["read", "write", "closed?", "close", "flush", "each_line", "gets"]),
  (fileId, ["read", "write", "exist?", "file?", "directory?", "size", "open"]),
  (dirId, ["exist?", "entries", "children", "mkdir"])
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
            visibility := if n == "method_missing" || n == "Rational" || n == "Complex" ||
                ["const_added", "inherited", "method_added", "method_removed", "method_undefined", "singleton_method_added",
                 "singleton_method_removed", "singleton_method_undefined"].contains n ||
                (["puts", "print", "p", "raise", "fail", "String", "block_given?", "rand",
                  "require", "require_relative", "respond_to_missing?", "instance_variables_to_inspect", "binding",
                  "local_variables"].contains n && cls == objectId) ||
                ["initialize", "initialize_copy", "initialize_clone", "initialize_dup"].contains n then .priv else .pub,
            builtin := some (if n == "===" then
              match cname with
              | "Proc" => "Proc#call"
              | "TrueClass" | "FalseClass" | "NilClass" => "Object#==="
              | "Integer" | "Float" | "String" | "Symbol" => s!"{cname}#=="
              | _ => s!"{cname}#{n}"
              else s!"{cname}#{n}") : MethodDef }) :: ms
    h.setClassPayload cls { c with methods }

/-- Reducible insertion sort by id (`.1`), replacing `Array.qsort` in `initHeap`.
    `qsort` is opaque to the kernel, so any `decide`/`rfl` over `initHeap` got
    stuck; a structural `def` reduces (metatheory needs concrete boot-heap facts). Ids are distinct, so this yields the same strictly-ascending order. -/
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
    ({ objs := #[] } : Heap)
  -- main object (allocated last, after all classes)
  let hMain := (hClasses.alloc { klass := objectId }).2
  -- install builtins
  let hBuiltins := builtinMethods.foldl (fun h (e : ObjId × List String) => install h e.1 e.2) hMain
  -- Kernel is a *module*, and `Object` includes it: allocated as an
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
  -- methods, so they belong in the boot heap rather than in a rule. Given as
  -- bit patterns, not as `0.0 / 0.0` and `1.0 / 0.0`: the sign of the NaN a
  -- division produces depends on the processor, and a bit pattern is a term the
  -- kernel can compare (`RubyCore/Generated/BootedHeap.lean`). CRuby's `NAN` is
  -- the positive quiet NaN.
  let hBuiltins := match hBuiltins.classPayload? floatId with
    | some c => hBuiltins.setClassPayload floatId
        { c with consts := c.consts ++
            [("NAN", Value.flt (Float.ofBits 0x7FF8000000000000)),
             ("INFINITY", Value.flt (Float.ofBits 0x7FF0000000000000))] }
    | Option.none => hBuiltins
  let hBuiltins := match hBuiltins.classPayload? enumeratorId with
    | some c => hBuiltins.setClassPayload enumeratorId
        { c with consts := [("Generator", .ref generatorId), ("Yielder", .ref yielderId)] }
    | none => hBuiltins
  -- Nested classes belong to their enclosing constant table.
  let hConsts : Heap := match hBuiltins.classPayload? objectId with
    | some c =>
      hBuiltins.setClassPayload objectId
        { c with consts := classTable.filterMap (fun (o, name, _) =>
            -- `toList.contains`, not `String.contains`: the latter is an iterator loop
            -- the kernel cannot unfold, which stopped every proof that evaluates a
            -- toplevel constant lookup on this heap (`books/`).
            if name.toList.contains ':' then none else some (name, Value.ref o)) }
    | Option.none => hBuiltins
  -- **J53: the eigenclasses of `BasicObject` and `Object`, realized at boot.**
  -- `enterClassBody` eagerly realizes a fresh class's metaclass chain, and at a
  -- heap where `Object.eigen` is `none` that walk *also* allocates the two
  -- ancestors' eigenclasses — a heap shape the invariant would otherwise have
  -- to case on. Realizing them here (exactly the objects `eigenclassOf.go`
  -- would create, same names, same superclasses, allocated in the same order)
  -- makes every fresh-class composite two allocations, like the module's.
  -- Appended after `main`, so every fixed id (`classTable`, `mainId`) is
  -- unmoved.
  let eB := hConsts.objs.size
  let hE := (hConsts.alloc
    { klass := classId,
      payload := .cls { superclass := some classId,
                        name := "", attached := some basicObjectId, isModule := false } }).2
  let hE := hE.set basicObjectId { hE.get basicObjectId with eigen := some eB }
  let eO := hE.objs.size
  let hE := (hE.alloc
    { klass := classId,
      payload := .cls { superclass := some eB,
                        name := "", attached := some objectId, isModule := false } }).2
  let hE := hE.set objectId { hE.get objectId with eigen := some eO }
  -- The VFS fixture, allocated in the order `vfsReadmeId`, `vfsNumsId`,
  -- `vfsDataId`, `vfsTmpId`, `vfsRootId` name, children before parents. Parents
  -- are patched in where the id is already known.
  let hV := (hE.alloc { klass := fileId, payload := .file "hello\n" }).2
  let hV := (hV.alloc
    { klass := fileId, payload := .file "1\n2\n3\n" }).2
  let hV := (hV.alloc
    { klass := dirId, payload := .dir [("nums.txt", vfsNumsId)] (some vfsTmpId) }).2
  let hV := (hV.alloc
    { klass := dirId,
      payload := .dir [("readme.txt", vfsReadmeId), ("vfsdata", vfsDataId)] (some vfsRootId) }).2
  (hV.alloc
    { klass := dirId, payload := .dir [("tmp", vfsTmpId)] none }).2

/- Drift guard: `vfsBase` is derived from `classTable.length`, so a new bootstrap
   class shifts the fixture ids automatically. The one remaining way to break
   resolution is to reorder the fixture allocations above without updating the
   `vfs*Id` names; `resolve` would then walk the wrong object. The differential
   fixtures exercise each path, so that shows up as a disagreement rather than
   silently. -/
end Boot

/-! ## Pure object-model operations (Semantics 01 §4, 02 §1–2) -/

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

/-! ## Virtual filesystem (issue #7 step 1)

One definition of path resolution, walked from a `cwd`. At step 1 the `cwd` is
fixed at the fixture root, so only absolute paths are resolved; relative paths
and `Dir.chdir` arrive with the per-execution `cwd` (issue #7 open question 2).
The walk splits on `/`, ignores empty components and `.`, and treats `..` by the
stored tree — so `.`/`..`/trailing slashes have exactly one rule.

Resolution is pure and total: it returns `Option ObjId`, and the builtins turn a
missing path into a named `Unsupported` (an unimplemented operation is never a
guessed answer or a fake `Errno`). -/

namespace VFS

/-- Normalize an absolute path into its non-empty components. `.` and `..` are
    kept and resolved during the walk (there is no textual collapse), so a
    symlink-free tree resolves them exactly, and a `.` after a non-directory
    component still fails the walk the way CRuby's does. -/
def components (s : String) : List String :=
  (s.splitOn "/").filter (fun c => c != "")

/-- Resolve `comps` from directory `dir`. A `dir` payload is the only thing that
    can hold children; anything else stops the walk (`none`). `.` stays put and
    `..` climbs to the stored parent (staying put at the root, whose parent is
    `none`) — both require the current object to be a directory, so
    `/tmp/readme.txt/.` fails the way CRuby's `ENOTDIR` does. -/
def walk (h : Heap) (dir : ObjId) : List String → Option ObjId
  | [] => some dir
  | c :: rest =>
    match (h.get dir).payload with
    | .dir entries parent =>
      if c == "." then walk h dir rest
      else if c == ".." then
        match parent with
        | some p => walk h p rest
        | none => walk h dir rest
      else match entries.find? (fun p => p.1 == c) with
        | some (_, child) => walk h child rest
        | none => none
    | _ => none

/-- Does `path` end in a `/` component (other than the root itself)? A trailing
    slash means the last component must name a **directory**: CRuby refuses
    `File.read("/tmp/readme.txt/")` with `Errno::ENOTDIR` and answers `false` to
    `File.exist?`/`file?`/`directory?` on it, while `"/tmp/"`, `"/"` and `"//"`
    are the fixture root (or a directory) and stay valid. `components` drops the
    empty trailing component, so this is the only thing that distinguishes
    `/tmp/readme.txt/` from `/tmp/readme.txt`. -/
def trailingSlash (path : String) : Bool :=
  path.length > 1 && path.endsWith "/"
/-- Resolve an absolute path from the fixture root. A path that is not absolute
    (`""` or not starting with `/`) resolves to `none`: relative paths are not
    in the step-1 fragment.

    A path with a trailing slash resolves only when its last component is a
    directory: `resolve h "/tmp/readme.txt/"` is `none`, matching CRuby's
    `ENOTDIR`, while `resolve h "/tmp/vfsdata/"` is the directory. This keeps a
    trailing slash from silently naming a regular file (a wrong answer) in
    every predicate, `File.read`/`write` and `File.open` that shares `lookup`. -/
def resolve (h : Heap) (path : String) : Option ObjId :=
  if path.startsWith "/" then
    match walk h Boot.vfsRootId (components path) with
    | some o =>
      if trailingSlash path then
        match (h.get o).payload with
        | .dir _ _ => some o
        | _ => none
      else some o
    | none => none
  else none

/-- The `ObjId` a path names, if it exists. -/
def lookup (h : Heap) (path : String) : Option ObjId := resolve h path

end VFS

/-- A module's own ancestor list: itself, then its `include`d modules
    (most-recent first), recursively.

    **Fuel-bounded rather than `partial`**: a `partial def` is opaque to the
    kernel, so once *any* class in a chain has mixins — and `Object` now includes
    `Kernel`, so every chain does — `ancestors` would no longer reduce and
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

/-- Reflection sees a visibility forwarding entry even if its eventual body
    has been removed or undefined. Calls and aliases resolve the body below. -/
def methodEntryInChain (h : Heap) (chain : List ObjId) (name : String) : Option (ObjId × MethodDef) :=
  chain.firstM fun k =>
    (h.classPayload? k).bind fun cp =>
      (cp.methods.find? (·.1 == name)).map fun (_, md) => (k, md)

/-- Method lookup with live inherited visibility overrides (Ruby's ZSUPER
    entries). A module's standalone reflection can use its Object fallback. -/
def lookupInChain (h : Heap) (chain : List ObjId) (name : String) : Option (ObjId × MethodDef) :=
  go (2 * h.objs.size + 2) chain false
where
  go : Nat → List ObjId → Bool → Option (ObjId × MethodDef)
    | 0, _, _ => none
    | _ + 1, [], _ => none
    | fuel + 1, k :: rest, fallbackUsed =>
      match h.classPayload? k with
      | none => go fuel rest fallbackUsed
      | some cp =>
        match cp.methods.find? (·.1 == name) with
        | none => go fuel rest fallbackUsed
        | some (_, md) =>
          if !md.visibilityOnly then some (k, md) else
          let body := (go fuel rest fallbackUsed).orElse fun _ =>
            if cp.isModule && !fallbackUsed then go fuel (ancestors h Boot.objectId) true else none
          body.map fun (owner, actual) => (owner, { actual with visibility := md.visibility })

/-- LOOKUP returns the defining entry, resolving visibility-only wrappers. -/
def lookup (h : Heap) (v : Value) (name : String) : Option (ObjId × MethodDef) :=
  lookupInChain h (ancestors h (classOf h v)) name

/-- `is_a?` test: does `v`'s ancestor chain include class `k`? -/
def isA (h : Heap) (v : Value) (k : ObjId) : Bool :=
  (ancestors h (classOf h v)).contains k

/-- Fake but deterministic "address" for default `Object#inspect` and for every
    message that renders an object by address — the difftest observation
    normalizes `0x…` on both sides by occurrence order, so only distinctness +
    ordering matter. Lives here, below `className`'s caller set, because an
    **anonymous** class is rendered by address in error messages too. -/
def fakeAddr (o : ObjId) : String :=
  let hex := String.ofList (Nat.toDigits 16 o)
  "0x" ++ String.ofList (List.replicate (16 - hex.length) '0') ++ hex

/-- CRuby's temporary class path, distinct from singleton-class `to_s`.
    An unnamed Module-subclass instance uses its direct class's path, including
    an eigenclass when present. That path names the eigenclass by address or its
    assigned constant name, without recursively rendering its attached object. -/
def classPath (h : Heap) (k : ObjId) : String :=
  go (h.objs.size + 1) k
where
  go : Nat → ObjId → String
    | 0, k => s!"#<Class:{fakeAddr k}>"
    | fuel + 1, k =>
      match h.classPayload? k with
      | some c =>
        if !c.name.isEmpty then c.name
        else
          let label := if !c.isModule then "Class"
            else if (h.get k).klass == Boot.moduleId then "Module"
            else go fuel (classOf h (.ref k))
          s!"#<{label}:{fakeAddr k}>"
      | none => "Object"

/-- Class name (for error messages / inspect). An **anonymous** class or module
    (`Class.new`, `Module.new`) has an empty `name`, and CRuby renders it by
    address wherever a name is wanted — `0 + Class.new.new` says
    `#<Class:0x…> can't be coerced into Integer`, not `` `` can't be coerced``.
    Every message built from `className` inherits that, so the fallback belongs
    here and not at ~20 call sites. Singleton classes render their attached
    object from the current heap. `Module#name` reads the separate constant
    name, so an unnamed singleton class still answers nil. The heap-sized fuel
    bounds the acyclic attachment/class walk of every runtime-allocated heap. -/
def className (h : Heap) (k : ObjId) : String :=
  go (h.objs.size + 1) k
where
  go : Nat → ObjId → String
    | 0, k => s!"#<Class:{fakeAddr k}>"
    | fuel + 1, k =>
      match h.classPayload? k with
      | some c =>
        match c.attached with
        | some o =>
          let attachedName := match h.classPayload? o with
            | some _ => go fuel o
            | none => s!"#<{go fuel (h.get o).klass}:{fakeAddr o}>"
          s!"#<Class:{attachedName}>"
        | none => classPath h k
      | none => "Object"

/-- CRuby's `rb_any_to_s`: how an object is named where a *class* would be named
    by `className` — `#<Foo:0x…>`, ignoring any user `to_s`/`inspect` and any
    ivars. Used for receiver descriptions; singleton-class rendering uses the
    same rule inside className's recursive walk. This is not Repr.inspect:
    CRuby does not dispatch user methods here [V]. -/
def anyToS (h : Heap) (o : ObjId) : String :=
  match h.classPayload? o with
  | some _ => className h o
  | Option.none => s!"#<{className h (h.get o).klass}:{fakeAddr o}>"

/-- How a NoMethodError describes its receiver [V]:
    main / nil / true / false literally; classes as "class C";
    everything else "an instance of C" — **except** an object that has an
    eigenclass, which CRuby renders as the object itself, by `rb_any_to_s`:
    `def o.hi; end; o.zz` says `undefined method 'zz' for #<Foo:0x…>`, not
    `… for an instance of Foo`. The test is only "does a singleton class
    exist" — `extend` and a bare `o.singleton_class` trigger it as much as a
    `def o.x` — and it ignores a user `inspect`/`to_s` and any ivars. A *class*
    receiver keeps "class C" even with singleton methods of its own [V]. -/
def receiverDesc (h : Heap) (v : Value) : String :=
  match v with
  | .nil => "nil"
  | .bool b => toString b
  | .ref o =>
    if o == Boot.mainId then "main"
    else match (h.get o).payload with
      | .cls c => (if c.isModule then "module " else "class ") ++ className h o
      | _ =>
        match (h.get o).eigen with
        | some _ => anyToS h o
        | Option.none => s!"an instance of {className h (h.get o).klass}"
  | _ => s!"an instance of {className h (classOf h v)}"

/-- Look up a constant on Object (L0: flat toplevel namespace,
    Semantics 03's two-phase lookup degenerates to this). -/
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

/-- Set constant `name` on class object `cls` (its own namespace, Semantics 03).
    A `casgn` inside `class C … end` writes to `C`, not the flat toplevel. -/
def constSetIn (h : Heap) (cls : ObjId) (name : String) (v : Value) : Heap :=
  match h.classPayload? cls with
  | some c =>
    h.setClassPayload cls
      { c with consts := (name, v) :: c.consts.filter (·.1 != name) }
  | Option.none => h

/-- A class/module's *own* constants (no ancestor walk) — the lexical phase of
    Semantics 03's two-phase constant lookup. -/
def constOwn (h : Heap) (cls : ObjId) (name : String) : Option Value :=
  (h.classPayload? cls).bind fun c => (c.consts.find? (·.1 == name)).map (·.2)

/-- Constant lookup from cref `cls`: the *inheritance* phase of Semantics 03's
    two-phase rule — walk `cls`'s ancestors (which bottoms out at Object, the
    toplevel namespace). The lexical phase (cref nesting) is not modeled at L0;
    `cls` is the innermost enclosing class (`defmod`). -/
def constLookupFrom (h : Heap) (cls : ObjId) (name : String) : Option Value :=
  (ancestors h cls).firstM fun k =>
    match h.classPayload? k with
    | some c => (c.consts.find? (·.1 == name)).map (·.2)
    | Option.none => Option.none

/-- `@@x` read from lexical scope `scope`: the first ancestor (class or included
    module) that defines it (Semantics 03 §3). -/
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

/-- Frozen method tables report the attached receiver for an eigenclass. -/
def frozenMethodReceiver? (h : Heap) (target : ObjId) : Option Value :=
  let attached := (h.classPayload? target).bind (·.attached)
  let receiver := attached.getD target
  if (h.get target).frozen || (h.get receiver).frozen then some (.ref receiver) else none

/-- Install a method after the interpreter has checked the frozen receiver. -/
def defineMethod (h : Heap) (cls : ObjId) (name : String) (md : MethodDef) : Heap :=
  match h.classPayload? cls with
  | some c =>
    h.setClassPayload cls
      { c with methods := (name, md) :: c.methods.filter (·.1 != name) }
  | Option.none => h

/-- `undef name` on `cls`: install an `undefined` tombstone (Semantics 02) so the
    ancestor walk stops here even if a superclass defines `name`. -/
def undefMethod (h : Heap) (cls : ObjId) (name : String) : Heap :=
  defineMethod h cls name { params := [], body := .nil, owner := cls, undefined := true }

end RubyCore
