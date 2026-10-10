import RubyCore.Machine
import RubyCore.Regex.Parse
import RubyCore.Repr

/-
Shared support for the builtin rules: value/payload accessors, allocation
helpers, the numeric and string-ordering primitives, the bid lists that the
dispatcher consults before matching, and the implementation helpers the rules
call (`binArg`, `putsImpl`, `raiseImpl`, `newImpl`, `sortImpl`, …).

The helpers are top-level definitions, ordered by use, so that every rule file
under `Builtins/` can call them.
-/


namespace RubyCore


/-- Sort keys for Array#sort/min/max: the L0 sortable universe (numerics
    sorted numerically incl. mixed int/float [V], strings lexically). -/
inductive SortKey where
  | num (x : Float)
  | str (s : String)
deriving Inhabited

inductive BRes where
  /-- Normal completion. -/
  | ok (v : Value) (m : Machine)
  /-- Raise a fresh exception of bootstrap class `cls` with message `msg`. -/
  | err (cls : ObjId) (msg : String) (m : Machine)
  /-- Raise an existing exception object. -/
  | throwV (v : Value) (m : Machine)
  /-- A rejected mutation still needs effectful inspect for its error message. -/
  | frozen (recv : Value) (m : Machine)
  | unsupported (reason : String)


namespace Builtins


/-- Methods whose user definition changes what **`inspect`** would print. `to_s`
    is deliberately absent: a user `to_s` does not change `Object#inspect`, which
    renders class and ivars [V].

    `message` used to be here, on the theory that `Exception#inspect` is built from
    it. It is not — `rb_exc_inspect` renders the *mesg* through `to_s`, and
    `Exception#message` is itself `to_s`, so a user `message` changes **nothing**
    about either [V]. Listing it only made the model refuse programs CRuby answers.
    The real sensitivity it was standing in for is `to_s`-on-an-Exception, and that
    is per-value rather than per-list, so it lives in `pureOk`'s `.exc` arm. -/
def inspectSensitive : List String := ["inspect"]

/-- The same, for **`to_s`**. Splitting the two lists is what keeps the check
    from being over-strict: before L103 a single global flag conflated them, so
    `class Integer; def to_s; "x"; end` made `p 1` inadmissible even though
    `p` uses `inspect` and is unaffected. -/
def toSSensitive : List String := ["to_s"]

/-- Does `k`'s ancestor chain carry a **non-builtin** definition of one of
    `sens`? This is the per-class replacement for the old global `reprPure` flag
: a `def to_s` on one class used to make pure repr refuse to speak for
    *every* object in the program — including unrelated ones, and including the
    prelude's own, which is why the prelude could not define `to_s`/`inspect`/
    `==` anywhere and why `Struct`/`T::Struct` were blocked on this. -/
def reprOverridden (h : Heap) (sens : List String) (k : ObjId) : Bool :=
  (ancestors h k).any fun a =>
    match h.classPayload? a with
    | some cp =>
      cp.methods.any fun (n, md) =>
        sens.contains n && md.builtin.isNone && !md.undefined
    | none => false

/-- As `reprOverridden`, but counting only definitions written by the **program**.
    `reprOverridden` deliberately counts the prelude's own — otherwise pure repr
    would *lie* about `Pathname` and `T::Struct`, whose prelude `inspect` it knows
    nothing about (see `reprDefer?`). The observation needs the opposite question,
    and asking the wrong one cost three ratchet cases: the prelude defines
    `Exception#message` (as `to_s`), so "does anything override `message`" is
    `true` for *every* exception, and a gate meant for a program's override fired on
    a plain `TypeError`. -/
def programOverridden (h : Heap) (sens : List String) (k : ObjId) : Bool :=
  (ancestors h k).any fun a =>
    match h.classPayload? a with
    | some cp =>
      cp.methods.any fun (n, md) =>
        sens.contains n && md.builtin.isNone && !md.undefined && !md.fromPrelude
    | none => false

/-- The native operation implemented by the payload renderer. A builtin alias
    is pure only when it still resolves to this operation. -/
def nativeReprOwner (h : Heap) (name : String) : Value → String
  | .nil => "NilClass"
  | .bool true => "TrueClass"
  | .bool false => "FalseClass"
  | .int _ => "Integer"
  | .flt _ => "Float"
  | .sym _ => "Symbol"
  | .ref o => match (h.get o).payload with
    | .none | .rng _ | .generator _ | .yielder .. => "Object"
    | .str _ => "String"
    | .arr _ => "Array"
    | .hsh _ => "Hash"
    | .cls _ => "Module"
    | .exc _ => "Exception"
    | .proc _ => "Proc"
    | .range .. => "Range"
    | .rational .. => "Rational"
    | .complex .. => "Complex"
    | .regexp .. => "Regexp"
    | .mdata .. => "MatchData"
    | .enumerator _ => if name == "to_s" then "Object" else "Enumerator"
    | .chain _ => if name == "to_s" then "Object" else "Enumerator::Chain"
    | .file _ => "File"
    | .dir _ _ => "Dir"
    | .io .. => "IO"

def reprUnchanged (h : Heap) (sens : List String) (value : Value) : Bool :=
  sens.all fun name =>
    if name == "inspect" || name == "to_s" then
      (lookup h value name).any fun (_, md) =>
        !md.undefined && md.builtin == some (nativeReprOwner h name value ++ "#" ++ name)
    else !reprOverridden h [name] (classOf h value)

/-- Native Object#inspect uses rb_check_funcall before reading ivars. A known
    default hook with no custom respond_to? is the only effect-free shortcut. -/
def objectInspectPure (h : Heap) (recv : Value) : Bool :=
  (lookup h recv "respond_to?").isNone &&
    ((lookup h recv "instance_variables_to_inspect").any fun (_, md) =>
      !md.undefined && md.builtin == some "Object#instance_variables_to_inspect")

/-- Can pure repr (Repr.lean) speak for this value? The resolved method must
    still be the native renderer for its payload, including aliases/tombstones;
    containers also check the values they render.

    `classOf`, not the object's `klass`: the chain starts at the **eigenclass**,
    so a `def obj.inspect` or an `o.extend(M)` makes the value impure exactly as a
    class-level definition does. Asking about `klass` was a **wrong answer** — the
    override was invisible and the pure path rendered the default `#<C:0x…>`, in
    `p`, inside an Array/Hash/Range, and as an ivar of another object. This is the
    same one-argument miss `__user_defines?` had before L115. -/
private def pureOkSeen (h : Heap) (sens : List String) : Nat → List ObjId → Value → Bool
  -- Out of fuel is "not pure": the caller then dispatches or gates, never guesses.
  | 0, _, _ => false
  | fuel + 1, seen, .ref o =>
    if seen.contains o then false else
    let seen := o :: seen
    let own := reprUnchanged h sens (.ref o)
    match (h.get o).payload with
    -- A container renders its elements with *their* renderer, so purity is
    -- recursive even when the container's own class is untouched — and it
    -- recurses with the **same** sensitivity it was asked about, since
    -- `[x].inspect` uses `x.inspect` while `[x].join` uses `x.to_s`.
    | .arr xs => own && xs.all (pureOkSeen h sens fuel seen)
    | .hsh xs => own && xs.all fun (k, v) => pureOkSeen h sens fuel seen k && pureOkSeen h sens fuel seen v
    | .none | .rng _ | .generator _ | .yielder .. =>
      own && (!sens.contains "inspect" || objectInspectPure h (.ref o)) && (h.get o).ivars.all (fun (_, v) => pureOkSeen h sens fuel seen v)
    -- A Range is a container of two: `(a..b).inspect` calls `a.inspect`, so an
    -- endpoint with a user `inspect` makes the range impure too. Missing this was
    -- a **wrong answer** — the pure path rendered the endpoint's default
    -- `#<C:0x…>` and ignored the override — found by the L122 range head, which
    -- gives its endpoints a fixed `inspect` precisely so no address is observed.
    | .range lo hi _ => own && pureOkSeen h sens fuel seen lo && pureOkSeen h sens fuel seen hi
    | .rational _ _ => own && reprUnchanged h sens (.int 0)
    | .complex r i => own && pureOkSeen h sens fuel seen r && pureOkSeen h sens fuel seen i &&
        (!sens.contains "to_s" || [r, i].all (fun v =>
          !reprOverridden h ["to_str"] (classOf h v)))
    | .enumerator (some data) => own && pureOkSeen h ["inspect"] fuel seen data.recv &&
        data.args.all (pureOkSeen h ["inspect"] fuel seen)
    -- An Exception renders **through `to_s`** whichever way it is asked:
    -- `rb_exc_inspect` is `#<Class: rb_obj_as_string(exc)>` and
    -- `Exception#message` *is* `to_s`. So `to_s` is repr-sensitive for an exception
    -- object no matter which list the caller asked about — which is why this is
    -- here and not in `inspectSensitive`. Getting it from the list instead
    -- was wrong in both directions: it refused a user `message`, which changes
    -- nothing, and admitted a user `to_s`, which changes everything.
    | .exc msg =>
      let direct := match msg with
        | .nil => true
        | .ref message => match (h.get message).payload with | .str _ => true | _ => false
        | _ => false
      own && !isA h (.ref o) Boot.uncaughtThrowErrorId &&
        reprUnchanged h ["to_s"] (.ref o) && direct
    | .proc _ => false   -- Proc repr is address-based → never pure
    | _ => own
  -- Immediates also resolve the exact native renderer, honoring class aliases.
  | _ + 1, _, v => reprUnchanged h sens v

def pureOk (h : Heap) (sens : List String) (value : Value) : Bool :=
  pureOkSeen h sens reprFuel [] value

/-- When pure repr cannot speak for a value, the *prelude twin* to dispatch
    instead. This is L63's "defer to the prelude" pattern: the twin has a
    **different name**, so it shadows nothing, changes no purity answer, and needs
    no new `Kont` — `invoke` simply dispatches it in place of the builtin.

    The alternative designs both fail on inspection. Excluding prelude
    definitions from `reprOverridden` would make pure repr *lie* about `Pathname`
    and `T::Struct`, whose prelude `inspect` it knows nothing about; and
    redefining `inspect` itself in the prelude would make every class impure and
    push `Obs`'s `result_repr` — computed after the program ends, where nothing
    can dispatch — off a cliff. -/
def reprDefer? (h : Heap) (bid : String) (recv : Value) (args : List Value) :
    Option String :=
  if bid == "Array#inspect" || bid == "Hash#inspect"
     || bid == "Exception#inspect" then
    if pureOk h inspectSensitive recv then none else some "__inspect_slow"
  else if bid == "Array#to_s" || bid == "Hash#to_s" then
    -- `Array#to_s` and `Hash#to_s` **are** `inspect` (`rb_ary_to_s` is
    -- `rb_ary_inspect`), so they render their contents with `inspect` and their
    -- sensitivity is *inspect*-sensitivity, not `to_s`-sensitivity. Asking the
    -- `to_s` list here refused `{ a: BadInspect.new }.to_s` outright: the
    -- element overrides `inspect` only, so the purity test said "pure", the Lean
    -- `Repr` ran, and *it* is the thing that cannot render an impure element.
    -- `Range#to_s` is deliberately not here — it really does use its endpoints'
    -- `to_s` [V].
    if pureOk h inspectSensitive recv then none else some "__to_s_slow"
  else if bid == "Range#to_s" then
    if pureOk h toSSensitive recv then none else some "__to_s_slow"
  else if bid == "Range#inspect" then
    if pureOk h inspectSensitive recv then none else some "__inspect_slow"
  else if bid == "Array#join" then
    -- `join` renders each element with **`to_s`**, recursively through nested
    -- arrays. `Version#major_minor` is `[major, minor].join(".")` over `Token`s
    -- that override `to_s`, which is four of the slice's examples.
    if pureOk h toSSensitive recv then none else some "__join_slow"
  else if bid == "Object#p" then
    if args.all (pureOk h inspectSensitive) then none else some "__p_slow"
  else if bid == "Object#puts" then
    if args.all (pureOk h toSSensitive) then none else some "__puts_slow"
  else if bid == "Object#print" then
    if args.all (pureOk h toSSensitive) then none else some "__print_slow"
  else none

def inspectP (m : Machine) (v : Value) : Except String String :=
  if pureOk m.heap inspectSensitive v then inspect m.heap v
  else .error "inspect after user override of inspect"

def toSP (m : Machine) (v : Value) : Except String String :=
  if pureOk m.heap toSSensitive v then toS m.heap v
  else .error "to_s after user override of to_s"

/-- Operand description in "no implicit conversion of X into Y" errors:
    class name, except nil/true/false literally [V]
    (`"a"+:k` → "…of Symbol into String", `"a"+nil` → "…of nil into…").

    `realClassOf`, not `classOf`: CRuby names the class through `rb_obj_class`,
    which skips the eigenclass, so an operand carrying a singleton method is
    still "of Foo into String" and not "of #<Class:#<Foo:0x…>> into String"
    (L124 — invisible while every eigenclass was misnamed `#<Class:Object>`). -/
def coerceName (h : Heap) : Value → String
  | .nil => "nil"
  | .bool b => toString b
  | v => className h (realClassOf h v)

/-- Operand description in "X can't be coerced into C" and "comparison of C
    with X failed" errors: special constants show their *inspect*
    (`1+:k` → ":k can't be coerced…"), other objects their class name [V].

    A **Float** shows its inspect too — `rb_cmperr` and `coerce_failed` both test
    `RB_FLOAT_TYPE_P` alongside `SPECIAL_CONST_P`. Unreachable from `numBin`,
    where a Float argument always coerces, and so missing here until `Comparable`
    started routing its own `comparison of … failed` through this rule:
    `Tok.new < 1.5` said "comparison of Tok with Float failed" for CRuby's
    "…with 1.5 failed". -/
def coerceDesc (h : Heap) : Value → String
  | .nil => "nil"
  | .bool b => toString b
  | .sym s => symInspect s
  | .int n => toString n
  | .flt x => rubyFloatRepr x
  | v => className h (realClassOf h v)   -- as `coerceName` above

def strPayload? (h : Heap) : Value → Option String
  | .ref o => match (h.get o).payload with
    | .str s => some s
    | _ => none
  | _ => none

def arrPayload? (h : Heap) : Value → Option (Array Value)
  | .ref o => match (h.get o).payload with
    | .arr xs => some xs
    | _ => none
  | _ => none

/-- Core classes whose instances carry a non-`.none` payload (String, Array,
    Hash, Proc, and the immediates). A user subclass of one inherits an
    allocator we don't model, so `Class#new` for such a subclass gates rather
    than build a wrong-payload object. Exception is handled separately (it has
    its own `allocExc` path in `newImpl`). -/
def payloadCoreClasses : List ObjId :=
  [Boot.stringId, Boot.arrayId, Boot.hashId, Boot.procId, Boot.integerId,
   Boot.floatId, Boot.symbolId, Boot.rationalId, Boot.complexId,
   Boot.enumeratorId, Boot.generatorId, Boot.yielderId]

/-- The payload-carrying core class `k` inherits from, if any — `String`, `Array`,
    `Hash` and `Exception` are *allocatable* for a subclass (L70: allocate the
    empty payload with `klass := k`, then let `initialize` fill it), the rest are
    not (a `Proc` needs a closure, a `Range`/`Random` needs its own arguments). -/
def allocatableCore (h : Heap) (k : ObjId) : Option ObjId :=
  (ancestors h k).find? fun a =>
    a == Boot.stringId || a == Boot.arrayId || a == Boot.hashId || a == Boot.exceptionId

/-- The empty payload an instance of core class `core` starts with. -/
def emptyCorePayload (core : ObjId) : Payload :=
  if core == Boot.stringId then .str ""
  else if core == Boot.arrayId then .arr #[]
  else if core == Boot.hashId then .hsh #[]
  else .exc .nil

/-- Does `v`'s class resolve `==` to a *user* (non-builtin) method? Builtins
    that lean on default value-equality (`Array#include?`/`index`, …) must gate
    when an operand overrides `==`, since a pure comparison can't dispatch it. -/
def hasUserEq (h : Heap) (v : Value) : Bool :=
  match lookup h v "==" with
  | some (_, md) => md.builtin.isNone
  | none => false

/-- Pure equality can reach Complex values through collection operations, or
    through the reverse numeric comparison. Those leaves must not hide a user
    equality method on the Complex or either component. -/
def complexEqualityImpure (h : Heap) : Nat → Value → Bool
  | 0, _ => true
  | fuel + 1, .ref o =>
    match (h.get o).payload with
    | .complex r i =>
      ["==", "eql?", "hash"].any (fun name => match lookup h (.ref o) name with
        | some (_, md) => md.builtin.isNone || md.undefined
        | none => false) || [r, i].any (hasUserEq h)
    | .arr xs => xs.any (complexEqualityImpure h fuel)
    | .hsh xs => xs.any (fun (k, v) => complexEqualityImpure h fuel k || complexEqualityImpure h fuel v)
    | _ => false
  | _, _ => false

def pureEqualityBids : List String :=
  ["Array#include?", "Array#index", "Array#-", "Array#&", "Array#|", "Array#uniq",
   "Hash#[]", "Hash#[]=", "Hash#key?", "Hash#has_key?", "Hash#include?", "Hash#member?",
   "Hash#fetch", "Hash#delete", "Hash#merge", "Hash#merge!"]

/-- Would CRuby dispatch `to_ary` on this value? Every implicit Array conversion
    goes through `rb_check_array_type`, which **dispatches** — so a *user*
    `to_ary`, or a user `method_missing` that could intercept it, decides the
    answer, runs its side effects, and gets the `conversion_mismatch` message
    (`can't convert C to Array (C#to_ary gives String)`) when it answers the
    wrong type.

    A builtin cannot run a dispatch, so a site that reaches this either defers to
    a prelude twin (`toAryDefer?`) or gates. Deliberately *not* excluding
    `fromPrelude`, unlike `mayCoerce`: the prelude's only `method_missing`s
    (`Pathname`, `File`, `URI`) exist to refuse by name, and refusing here is
    what they already do today — routing through them changes no answer. -/
def mayDispatchToAry (h : Heap) (v : Value) : Bool :=
  (match lookup h v "to_ary" with | some (_, md) => md.builtin.isNone | none => false)
  || (match lookup h v "method_missing" with | some (_, md) => md.builtin.isNone | none => false)

/-! ### `NUM2LONG` over an index operand

Every indexing builtin converts its subscript with `rb_num2long`, and the model
gated on anything that was not already an `Int` — which is how R1's advisory
corpus lost 23 of its 106 programs to `Array#[] non-int index` and
`unmodeled method Integer#[]`. CRuby *answers* on all of those: it is a family of
messages rather than a refusal.

The one arm that still refuses is the one that would have to dispatch — a
`to_int`, or the `begin`/`end`/`exclude_end?` a non-Integer subscript is asked
for **first** (`rb_ary_aref1` tries `rb_range_beg_len` before `NUM2LONG`, so
`A[obj_with_method_missing]` answers `[]`, not an element). That was a gate
before and stays one; nothing here turns an answer into a refusal. -/

/-- The outcome of converting a subscript. `gate` carries its own reason when it
    has one more specific than the caller's. -/
inductive IdxRes where
  | ok (n : Int)
  | gate (why : Option String)
  | err (cls : ObjId) (msg : String)

/-- Could a non-Integer subscript answer one of the four methods CRuby asks it
    for — `begin`/`end`/`exclude_end?` (the Range protocol, tried first) or
    `to_int`? Prelude definitions count: `Range` itself has real ones, and the
    Range arm is handled by the caller before this is reached. -/
def mayDispatchIndex (h : Heap) (v : Value) : Bool :=
  ["to_int", "begin", "end", "exclude_end?", "method_missing"].any fun n =>
    match lookup h v n with
    | some (_, md) => md.builtin.isNone && !md.undefined
    | none => false

/-- `rb_num2long` / `rb_to_int` over a subscript [V]. A finite Float
    **truncates toward zero**, so `[10,20,30][1.7]` is `20`.

    `numMsg` selects between the two conversions, which differ **only for nil**
    and only in wording: `rb_num2long` (the array/string subscript path) says
    `no implicit conversion from nil to integer` — lowercase, and different
    prepositions from every other operand, the same oddity L132 found in
    `Integer#to_s` — while `rb_to_int` (`Integer#[]`) says the ordinary
    `no implicit conversion of nil into Integer`. Getting that backwards is a
    wrong answer rather than a gate, which is why it is a parameter and not a
    constant.

    A Float outside `long` **gates**: the message is a `RangeError` carrying the
    float rendered by CRuby's `%g`, which is not `Float#to_s` (`1e+30`, not
    `1.0e+30`), and inventing a second float formatter for one message is worse
    than refusing. NaN is exact and so is answered. -/
def numIndex (h : Heap) (numMsg : Bool) : Value → IdxRes
  | .int n => .ok n
  | .flt x =>
    if x.isNaN then .err Boot.rangeErrorId "float NaN out of range of integer"
    else if x ≥ 9223372036854775808.0 || x ≤ -9223372036854775809.0 then
      .gate (some "index: a Float out of long range (RangeError renders %g)")
    else .ok (Int.ofNat x.abs.toUInt64.toNat * (if x < 0 then -1 else 1))
  | .nil => .err Boot.typeErrorId
      (if numMsg then "no implicit conversion from nil to integer"
       else "no implicit conversion of nil into Integer")
  | v =>
    if mayDispatchIndex h v then .gate none
    else .err Boot.typeErrorId
      s!"no implicit conversion of {coerceName h v} into Integer"

/-- `numIndex`, wired into a builtin: answer, raise, or gate with `why`. -/
def withIndex (m : Machine) (v : Value) (why : String) (k : Int → BRes)
    (numMsg : Bool := true) : BRes :=
  match numIndex m.heap numMsg v with
  | .ok n => k n
  | .gate w => .unsupported (w.getD why)
  | .err c msg => .err c msg m

/-- Allocate a String with an explicit encoding tag. -/
def allocStrEnc (m : Machine) (s : String) (binary : Bool) : Value × Machine :=
  let (o, h) := m.heap.alloc { klass := Boot.stringId, payload := .str s, binary }
  (.ref o, { m with heap := h })

/-- Is this value a binary (ASCII-8BIT) String? -/
def isBinaryStr (h : Heap) : Value → Bool
  | .ref o => (h.get o).binary
  | _ => false

def allocStr (m : Machine) (s : String) : Value × Machine :=
  let (o, h) := m.heap.alloc { klass := Boot.stringId, payload := .str s }
  (.ref o, { m with heap := h })

def allocArr (m : Machine) (xs : Array Value) : Value × Machine :=
  let (o, h) := m.heap.alloc { klass := Boot.arrayId, payload := .arr xs }
  (.ref o, { m with heap := h })

def allocHsh (m : Machine) (xs : Array (Value × Value)) : Value × Machine :=
  let (o, h) := m.heap.alloc { klass := Boot.hashId, payload := .hsh xs }
  (.ref o, { m with heap := h })

def allocExc (m : Machine) (cls : ObjId) (msg : String) : Value × Machine :=
  let (msg, m) := allocStr m msg
  let (o, h) := m.heap.alloc { klass := cls, payload := .exc msg }
  (.ref o, { m with heap := h })

/-- `dup`: a fresh object with the same class, payload and **instance variables**
    (`str.dup` keeps `@ivar` [V]), but *not* the frozen bit and *not* the
    singleton class. `keepFrozen` gives `clone`, which does preserve it. -/
def dupObj (m : Machine) (o : ObjId) (keepFrozen : Bool) : Value × Machine :=
  let src := m.heap.get o
  let (o2, h) := m.heap.alloc
    { klass := src.klass, ivars := src.ivars, payload := src.payload,
      hashDflt := src.hashDflt, frozen := keepFrozen && src.frozen, iterationResult := src.iterationResult,
      throwTag := src.throwTag, throwValue := src.throwValue,
      -- the encoding tag is part of the copy: `"café".b.dup.encoding` is
      -- ASCII-8BIT [V]
      binary := src.binary }
  (.ref o2, { m with heap := h })

def okStr (m : Machine) (s : String) : BRes :=
  let (v, m) := allocStr m s
  .ok v m

/-- Allocate a String result with an explicit encoding tag. -/
def okStrEnc (m : Machine) (binary : Bool) (s : String) : BRes :=
  let (v, m) := allocStrEnc m s binary
  .ok v m

/-- Allocate a String result that **inherits `src`'s encoding tag**.
    `src` is normally the receiver: every byte-derived String result in CRuby
    carries the encoding of the String it was derived from, and for a MatchData
    receiver the tag on the object records its *subject*'s encoding, so the same
    helper serves `MatchData#[]`/`pre_match`/… -/
def okStrFrom (m : Machine) (src : Value) (s : String) : BRes :=
  okStrEnc m (isBinaryStr m.heap src) s

/-- Is this a binary String holding a byte the model cannot let a tag-blind rule
    touch — one at or above 0x80? An *ASCII-only* binary String is
    excluded on purpose: every content answer over it is identical to the UTF-8
    one, so only its tag is at stake, and the String rules propagate that. -/
def unrepresentableByteStr (h : Heap) (v : Value) : Bool :=
  match strPayload? h v with
  | some s => isBinaryStr h v && hasHighByte s
  | none => false

/-- The rules admitted to run with such an operand — each either handles
    the tag or refuses on its own with a better reason. Everything absent is
    refused by `Builtins.run` before dispatch.

    `<=>`/`<`/`>`/`include?`/`start_with?`/`end_with?` are **deliberately absent**:
    CRuby raises `Encoding::CompatibilityError` for a cross-encoding comparison
    with a non-ASCII byte, and orders same-byte different-encoding strings by an
    internal encoding index (`"\xC3".b <=> "Ã"` is `-1` [V]) — neither of which
    this model has. So are `puts`/`print`/`__write`/`Array#join`/`format`, which
    would have to write the raw byte into an output `String` that cannot hold it. -/
def byteStrAwareBids : List String :=
  -- String: byte-wise by construction, or tag-propagating (`okStrFrom`)
  ["Class#inherited", "Module#const_added", "Module#method_added", "Module#method_removed", "Module#method_undefined",
   "BasicObject#singleton_method_added", "BasicObject#singleton_method_removed",
   "BasicObject#singleton_method_undefined",
   "String#+", "String#*", "String#<<", "String#concat", "String#==", "String#eql?",
   "String#!=", "String#length", "String#size", "String#empty?", "String#ord",
   "String#to_i", "String#to_f", "String#to_s", "String#to_str", "String#to_sym",
   "String#inspect", "String#chars", "String#reverse", "String#upcase",
   "String#b", "String#downcase", "String#strip", "String#chomp", "String#[]", "String#+@",
   "String#-@", "String#freeze", "String#frozen?", "String#hash",
   "String#__binary?", "String#__bytes", "String#__as_utf8",
   "String#__force_binary", "String#__force_utf8",
   -- pattern methods: the subject's tag rides on the MatchData and its slices
   "String#=~", "String#match", "String#match?", "String#scan", "String#split",
   "String#__search_at",
   "String#__split_never", "String#__sub_rep", "String#__gsub_rep",
   "Regexp#match", "Regexp#match?", "Regexp#=~", "Regexp#===",
   "MatchData#[]", "MatchData#to_s", "MatchData#pre_match", "MatchData#post_match",
   "MatchData#begin", "MatchData#end", "MatchData#size", "MatchData#length",
   "MatchData#captures", "MatchData#to_a", "MatchData#names",
   "MatchData#named_captures",
   -- Object: identity, class and equality are tag-blind for a reason, and
   -- `inspect`/`p` render through the binary-aware `Repr`
   "BasicObject#==", "BasicObject#!=", "BasicObject#!", "BasicObject#equal?",
   "Object#==", "Object#!=", "Object#!", "Object#equal?", "Object#eql?",
   "Object#hash", "Object#class", "Object#nil?", "Object#itself", "Object#is_a?", "Object#kind_of?",
   "Object#instance_of?", "Object#respond_to?", "Object#freeze", "Object#frozen?",
   "Object#inspect", "Object#to_s", "Object#p", "Object#__user_defines?", "Object#instance_variables_to_inspect",
   -- reads the method table, never the value
   "Object#__default_inspect?",
   -- renders the receiver's *class name* and address, never its payload
   "Object#__any_to_s",
   -- reads and writes neither operand, only the frame's `$~` routing
   "Object#__match_to_caller",
   -- render nothing of the operand but its *class name*
   "Object#__coerce_failed", "Object#__cmp_failed"]

/-- The encoding tag of `a ++ b`, CRuby's compatibility rule [V]: the
    result takes the **receiver's** encoding, *unless* only the argument holds a
    non-ASCII byte, in which case it takes the argument's — so `"a".b + "b"` is
    ASCII-8BIT, `"a" + "b".b` is UTF-8, and `"" .b + "café"` is UTF-8. Two
    non-ASCII operands in *different* encodings raise
    `Encoding::CompatibilityError`, a class the model does not have, so that
    refuses rather than answering (the `Except` error is an Unsupported reason). -/
def concatEnc (h : Heap) (a : Value) (s : String) (b : Value) (t : String) :
    Except String Bool :=
  let ab := isBinaryStr h a
  let bb := isBinaryStr h b
  if ab == bb then .ok ab
  else if hasHighByte s && hasHighByte t then
    .error "Encoding::CompatibilityError from concatenating a byte string with UTF-8"
  else if hasHighByte t then .ok bb
  else .ok ab

/-! ### Numerics -/

inductive Num where
  | i (n : Int)
  | f (x : Float)

def num? : Value → Option Num
  | .int n => some (.i n)
  | .flt x => some (.f x)
  | _ => none

def Num.value : Num → Value
  | .i n => .int n
  | .f x => .flt x

/-- `coerce_failed`: what a numeric operator raises once nothing has answered
    `coerce` — the end of the road for `coerceDefer?` and the answer
    directly for an operand whose class chain offers no `coerce` at all. Shared so
    that the operators which do *not* route through `numBin` (`**`, `divmod`)
    cannot drift from the ones that do. -/
def coerceFailed (recvCls : String) (m : Machine) (b : Value) : BRes :=
  .err Boot.typeErrorId
    s!"{coerceDesc m.heap b} can't be coerced into {recvCls}" m

def numBin (recvCls : String) (m : Machine) (a : Value) (b : Value)
    (fi : Int → Int → BRes) (ff : Float → Float → BRes) : BRes :=
  match num? a, num? b with
  | some (.i x), some (.i y) => fi x y
  | some (.i x), some (.f y) => ff (Float.ofInt x) y
  | some (.f x), some (.i y) => ff x (Float.ofInt y)
  | some (.f x), some (.f y) => ff x y
  | _, _ => coerceFailed recvCls m b

/-- `1 < "a"` → ArgumentError "comparison of Integer with String failed" [V].
    nil shows as "nil". -/
def numCmp (recvCls : String) (m : Machine) (a b : Value)
    (k : Ordering → BRes) : BRes :=
  match num? a, num? b with
  | some (.i x), some (.i y) => k (compare x y)
  | some x, some y =>
    let fx := match x with | .i n => Float.ofInt n | .f v => v
    let fy := match y with | .i n => Float.ofInt n | .f v => v
    if fx < fy then k .lt else if fx == fy then k .eq else
    if fx > fy then k .gt else .unsupported "NaN comparison"
  | _, _ => .err Boot.argumentErrorId
      s!"comparison of {recvCls} with {coerceDesc m.heap b} failed" m

def ordValue : Ordering → Value
  | .lt => .int (-1) | .eq => .int 0 | .gt => .int 1

/-! ### The coerce protocol

`numBin`/`numCmp` above answer for two numbers and raise for anything else. That
second half is wrong, and not by a message: CRuby's numeric operators run
`rb_num_coerce_bin`, which **asks the argument to `coerce` itself** and then
re-dispatches the operator on the pair it returns. So `3 + Money.new(4)` is `7`,
the `coerce` body's side effects happen, and the error — when there is one —
says *why* ("coerce must return [x, y]" for a wrong shape, "X can't be coerced
into Integer" only when nothing answered at all).

A builtin cannot dispatch, so the failure path defers to a prelude twin, exactly
as the repr builtins defer to theirs (`reprDefer?`). Deferral is keyed on
"could a `coerce` possibly run", so every operand that *is* a number, and every
operand whose class chain offers nothing, keeps the Lean fast path untouched. -/

/-- Could an ordinary send of `coerce` reach a method on `v`? Native Rational
    conversion and methods from the prelude count alongside program methods;
    a `method_missing` does **not** if it came from the prelude, because the only
    one there is `Pathname`'s, which exists to *refuse* — routing through it
    would turn today's correct `TypeError` into a gate. -/
def mayCoerce (h : Heap) (v : Value) : Bool :=
  (match lookup h v "coerce" with
   | some (_, md) => !md.undefined
   | none => false)
  || (match lookup h v "method_missing" with
      | some (_, md) => md.builtin.isNone && !md.undefined && !md.fromPrelude
      | none => false)

/-- Does `v` carry an `==` written by the **program**? `Integer#==` hands the
    comparison to its argument (`rb_equal(y, x)`) rather than coercing, so a
    user `==` decides `0 == obj` — and a truthy non-boolean answer becomes
    `true` [V].

    Prelude definitions are deliberately excluded, unlike in `hasUserEq`. The
    prelude's `==`s are `Comparable#==`, `Pathname#==` and `Struct#==`; reversing
    into the first *recurses* (`Comparable#==` calls `<=>`, and the default `<=>`
    calls `==`) where CRuby's paired-recursion guard answers `false`, and the
    other two answer `false` for a numeric argument anyway. So for those the
    model's own `false` is already CRuby's answer, and the reversal buys a
    fuel-exhaustion gate instead. -/
def hasProgramEq (h : Heap) (v : Value) : Bool :=
  match lookup h v "==" with
  | some (_, md) => md.builtin.isNone && !md.undefined && !md.fromPrelude
  | none => false

/-- The prelude twin for each coercing operator. One name per operator because
    the twin is entered with the builtin's own arguments — there is nowhere to
    pass "which operator" — and each is a one-liner over `__coerce_bin`. -/
def coerceTwin? : String → Option String
  | "Integer#+"  | "Float#+" | "Rational#+" | "Complex#+" => some "__coerce_add"
  | "Integer#-"  | "Float#-" | "Rational#-" | "Complex#-" => some "__coerce_sub"
  | "Integer#*"  | "Float#*" | "Rational#*" | "Complex#*" => some "__coerce_mul"
  | "Integer#/"  | "Float#/" | "Rational#/" | "Rational#quo" => some "__coerce_div"
  | "Complex#/" | "Complex#quo" => some "__coerce_quo"
  | "Integer#%"  | "Float#%"  => some "__coerce_mod"
  | "Integer#**" | "Float#**" | "Rational#**" => some "__coerce_pow"
  | "Integer#divmod" | "Float#divmod" => some "__coerce_divmod"
  | "Integer#<"  | "Float#<"  => some "__coerce_lt"
  | "Integer#>"  | "Float#>"  => some "__coerce_gt"
  | "Integer#<=" | "Float#<=" => some "__coerce_le"
  | "Integer#>=" | "Float#>=" => some "__coerce_ge"
  | "Integer#<=>" | "Float#<=>" | "Rational#<=>" => some "__coerce_cmp"
  | _ => none

/-- When a numeric builtin must dispatch rather than answer, the prelude twin to
    dispatch instead. Numeric receiver, non-numeric argument, and one of
    the two hooks that can make the difference observable — nothing else pays
    for the check, and `Integer#+` of two Integers cannot reach it. -/
def coerceDefer? (h : Heap) (bid : String) (recv : Value) (args : List Value) :
    Option String :=
  match args with
  | [b] =>
    if !nativeReal h recv && (complexPayload? h recv).isNone then none
    -- The argument is tested first: for an Integer argument the answer is then
    -- independent of the receiver, so `x / 2` reduces for a *variable* `x`.
    else if (rationalPayload? h b).isSome && bid == "Integer#/" && recv.identEq (.int 1) then none
    else if (num? b).isSome then none
    else if (complexPayload? h recv).isSome && (nativeReal h b || (complexPayload? h b).isSome) then none
    else if (rationalPayload? h recv).isSome && (rationalPayload? h b).isSome then none
    else if bid == "Integer#==" || bid == "Float#==" || bid == "Rational#==" || bid == "Complex#==" then
      if hasProgramEq h b then some "__eq_reverse" else none
    else if mayCoerce h b then coerceTwin? bid
    else none
  | _ => none

/-! ### The implicit Array conversion

The same shape as the coerce protocol one section up, and for the same reason.
Every implicit Array-conversion site in CRuby is `rb_check_array_type`, which is
`rb_check_funcall(:to_ary)` — it **dispatches**. So a `to_ary`, or a
`method_missing` that serves one, *runs*: its side effects happen, an Array
answer is used, and a non-Array answer raises `conversion_mismatch`
(`can't convert C to Array (C#to_ary gives String)` — "to", not "into", and it
names the method). The model's builtins tested the payload and raised
`no implicit conversion of C into Array` without calling anything, which is a
wrong message *and* a lost side effect.

A builtin cannot dispatch, so the sites defer to prelude twins over
`__to_array_type`. Deferral is keyed on "could a `to_ary` possibly run", so two
real Arrays — and every argument whose class chain offers nothing — keep the Lean
fast path untouched. `Array#-`/`&`/`|`/`*` convert too and are *not* here: they
gate on a non-Array argument today, and a gate is not a wrong answer. -/

/-- Is any value reachable from `v` through nested Arrays one that `to_ary`
    could speak for? `Array#flatten` converts **each element** with
    `rb_check_array_type`, so its deferral question is about the receiver's
    contents rather than its argument. Fuel-bounded like `flattenAll`, and a
    cyclic array runs out and answers `false` — which keeps the Lean path, whose
    own fuel then produces the honest gate rather than a Ruby-side non-termination. -/
def anyToAryDeep (h : Heap) : Nat → Value → Bool
  | 0, _ => false
  | fuel + 1, v =>
    match arrPayload? h v with
    | some xs => xs.any (anyToAryDeep h fuel)
    | none => mayDispatchToAry h v

/-- When an Array-conversion builtin must dispatch rather than answer, the
    prelude twin to dispatch instead. -/
def toAryDefer? (h : Heap) (bid : String) (recv : Value) (args : List Value) :
    Option String :=
  if bid == "Array#+" || bid == "Array#concat" then
    match args with
    | [b] =>
      if (arrPayload? h b).isSome || !mayDispatchToAry h b then none
      else if bid == "Array#+" then some "__ary_plus_slow" else some "__ary_concat_slow"
    | _ => none
  else if bid == "Array#flatten" then
    -- only the no-argument form; `flatten(n)` gates in the builtin either way
    match args, arrPayload? h recv with
    | [], some xs =>
      if xs.any (anyToAryDeep h 100) then some "__ary_flatten_slow" else none
    | _, _ => none
  else if bid == "Array#join" then
    -- `ary_join_one` recurses into a nested Array, and asks `rb_check_array_type`
    -- what "nested" means — so an element answering `to_ary` is joined rather
    -- than rendered. The same question as `flatten`, one builtin over.
    match arrPayload? h recv with
    | some xs => if xs.any (anyToAryDeep h 100) then some "__join_slow" else none
    | none => none
  else if bid == "Object#puts" then
    -- `rb_io_puts` tries `rb_check_array_type` on every argument before
    -- rendering it, which is why `puts` has gated on this question since L66.
    -- With a twin that can dispatch, the gate becomes an answer.
    if args.any (mayDispatchToAry h) then some "__puts_slow" else none
  else none

/-! ### String ordering against a non-String (`rb_str_cmp_m`)

`String#<=>` over a non-String does not answer nil outright: it asks
`rb_check_string_type` (a checked `to_str`, which a user `method_missing`
serves) and compares the converted String, and only when nothing converts does
it hand over to `rb_invcmp` — the operand's own `<=>`, sign flipped. The
operators are `Comparable`'s over that `<=>`. The builtins answered nil /
`comparison of String with C failed` without calling anything, which is right
exactly when nothing on the operand could speak up; otherwise they defer to
prelude twins over `__str_cmp_slow`. -/

/-- Could anything on `v` change what `rb_str_cmp_m` answers for it? A `to_str`
    (prelude ones included, as in `mayDispatchToAry`), or a program-written
    `method_missing` / `respond_to?` / `respond_to_missing?` (the checked call's
    hooks), `<=>` (`rb_invcmp`) or `==` (the default `<=>` is `rb_equal`) — or
    no `<=>` at all, which `rb_invcmp`'s plain call turns into `NoMethodError`. -/
def mayDispatchStrCmp (h : Heap) (v : Value) : Bool :=
  let program : String → Bool := fun n => match lookup h v n with
    | some (_, md) => md.builtin.isNone && !md.undefined && !md.fromPrelude
    | none => false
  (match lookup h v "to_str" with | some (_, md) => md.builtin.isNone && !md.undefined | none => false)
  || (match lookup h v "<=>" with | some (_, md) => md.undefined | none => true)
  || ["method_missing", "respond_to?", "respond_to_missing?", "<=>", "=="].any program

def strCmpTwin? : String → Option String
  | "String#<=>" => some "__str_cmp_slow"
  | "String#<" => some "__str_lt_slow"
  | "String#>" => some "__str_gt_slow"
  | "String#<=" => some "__str_le_slow"
  | "String#>=" => some "__str_ge_slow"
  | _ => none

/-- String receiver, non-String operand that could dispatch: the twin. An
    operand outside `Object` gates instead (`__str_cmp_basic`): the twin's
    conversion helpers ask it `is_a?`, which a `BasicObject` does not answer. -/
def strCmpDefer? (h : Heap) (bid : String) (recv : Value) (args : List Value) :
    Option String :=
  match strCmpTwin? bid, args with
  | some twin, [b] =>
    if (strPayload? h recv).isNone || (strPayload? h b).isSome then none
    else if !isA h b Boot.objectId then some "__str_cmp_basic"
    else if mayDispatchStrCmp h b then some twin else none
  | _, _ => none

/-- Every reason a builtin defers to a prelude twin instead of running: repr
    purity, the coerce protocol, the implicit Array conversion
 and String ordering against a non-String. One hook, so `invoke` has
    one place to consult and the dispatch metatheorems one hypothesis to carry. -/
def deferTwin? (h : Heap) (bid : String) (recv : Value) (args : List Value) :
    Option String :=
  if bid == "Object#===" then
    match args with
    | [other] => if recv.identEq other then none else some "__case_equal"
    | _ => none
  else if bid == "Rational#eql?" then
    match args with
    | [other] =>
      if !recv.identEq other && (rationalPayload? h other).isSome && hasUserEq h recv
      then some "__case_equal" else none
    | _ => none
  else if bid == "Complex#eql?" then
    match args, complexPayload? h recv with
    | [other], some (r, i) =>
      match complexPayload? h other with
      | some (a, b) =>
        if !recv.identEq other && realClassOf h r == realClassOf h a &&
            realClassOf h i == realClassOf h b && hasUserEq h recv
        then some "__case_equal" else none
      | none => none
    | _, _ => none
  else
  reprDefer? h bid recv args <|> coerceDefer? h bid recv args
    <|> toAryDefer? h bid recv args <|> strCmpDefer? h bid recv args

/-- Pure numeric comparison of two values (Int/Float, mixed promoted to Float);
    `none` if either is non-numeric — the caller then gates (a full `<=>` dispatch
    over arbitrary objects is not modeled, cf. `sort`/`min`/`max`). Used by the
    `max_by`/`min_by` iterator to compare block values. -/
def numOrd? (a b : Value) : Option Ordering :=
  match num? a, num? b with
  | some (.i x), some (.i y) => some (compare x y)
  | some x, some y =>
    let fx := match x with | .i n => Float.ofInt n | .f v => v
    let fy := match y with | .i n => Float.ofInt n | .f v => v
    some (if fx < fy then .lt else if fx == fy then .eq else .gt)
  | _, _ => none

/-! ### String ordering (byte order over UTF-8, which Lean's String compare
    matches for the ASCII-ish corpus; non-ASCII edge cases ride on Lean's
    lexicographic Char order = codepoint order = UTF-8 byte order). -/

def strCompare (a b : String) : Ordering := compare a b

/-- Normalize a `(start, len)` slice against a collection of size `n`:
    `none` = the CRuby nil result (start out of range, or a negative length),
    `some (offset, count)` otherwise. `start == n` yields an empty slice, and a
    count is clamped to what remains [V]. -/
def sliceRange (n : Nat) (start len : Int) : Option (Nat × Nat) :=
  let st := if start < 0 then start + n else start
  if st < 0 || st > n || len < 0 then Option.none
  else
    let stN := st.toNat
    Option.some (stN, min len.toNat (n - stN))

/-! ### Main dispatch -/

/-- Builtins that take exactly zero arguments in CRuby — extra args must be
    `ArgumentError (given N, expected 0)` [V], not silently ignored.
    Methods with optional args (Integer#to_s(base), Array#pop(n), …) are NOT
    here; their with-arg forms gate as Unsupported inside their own arms. -/
def zeroArgBids : List String :=
  ["Object#class", "Object#inspect", "Object#instance_variables_to_inspect", "Object#to_s", "Object#nil?", "Object#itself",
   "Integer#i", "Float#i", "Rational#i", "Integer#to_c", "Float#to_c", "Rational#to_c",
   "Complex#real", "Complex#imag", "Complex#imaginary", "Complex#rect", "Complex#rectangular",
   "Complex#to_s", "Complex#inspect", "Complex#real?", "Complex#to_c", "Complex#dup",
   "Complex#-@", "Complex#+@", "Complex#conj", "Complex#conjugate", "Complex#finite?", "Complex#infinite?",
   "Object#__coerce_defined?", "Integer#to_r", "Float#to_r",
   "Rational#numerator", "Rational#denominator", "Rational#to_s", "Rational#inspect",
   "Rational#to_i", "Rational#to_f", "Rational#to_r", "Rational#-@", "Rational#+@",
   "Rational#abs", "Rational#magnitude", "Rational#positive?", "Rational#negative?",
   "Rational#dup",
   "Object#frozen?", "Object#freeze", "Module#freeze", "Object#block_given?",
   "NilClass#nil?", "NilClass#to_s", "NilClass#inspect", "NilClass#to_a",
   "TrueClass#to_s", "TrueClass#inspect", "FalseClass#to_s", "FalseClass#inspect",
   -- `Integer#inspect` is deliberately absent: it is `to_s`, base argument and
   -- all.
   "Integer#to_i", "Integer#to_f", "Integer#abs", "Integer#succ",
   "Integer#pred", "Integer#zero?", "Integer#positive?", "Integer#negative?",
   "Integer#even?", "Integer#odd?", "Integer#-@",
   "Float#to_s", "Float#inspect", "Float#to_f", "Float#-@", "Float#abs", "Float#zero?",
   "Float#nan?", "Float#to_i",
   "String#to_s", "String#to_str", "String#inspect", "String#length",
   "String#size", "String#empty?", "String#reverse", "String#upcase",
   "String#b", "String#downcase", "String#strip", "String#frozen?", "String#dup",
   "String#to_sym", "String#freeze",
   "Symbol#to_s", "Symbol#inspect", "Symbol#to_sym", "Symbol#to_proc",
   "Array#length", "Array#size", "Array#empty?", "Array#inspect",
   "Array#to_s", "Array#to_a", "Array#reverse", "Array#compact",
   "Array#dup", "Array#clone", "Object#dup", "Object#clone",
   "String#clone", "Hash#clone", "Array#frozen?", "Array#freeze", "Array#sort", "Array#uniq",
   "Hash#length", "Hash#size", "Hash#empty?", "Hash#keys", "Hash#values",
   "Hash#inspect", "Hash#to_s", "Hash#to_a", "Hash#dup",
   "Exception#to_s", "Exception#inspect",
   "Module#name", "Module#to_s", "Module#inspect", "Module#ancestors",
   "Proc#lambda?", "Proc#to_proc", "Object#initialize",
   "Range#inspect", "Range#to_s", "Range#first", "Range#last", "Range#begin",
   "Range#end", "Range#exclude_end?"]

/-- The `dup`/`clone` bids, listed rather than matched with `String.endsWith`
: `endsWith` is **not kernel-reducible**, so having it at the top of
    `run` stopped every `rfl`/`decide` in the metatheory that steps through a
    builtin. `List.contains` over literals reduces fine. -/
def dupBids : List String :=
  ["Object#dup", "String#dup", "Array#dup", "Hash#dup", "Integer#dup",
   "Float#dup", "Symbol#dup", "NilClass#dup", "TrueClass#dup", "FalseClass#dup",
   "Exception#dup"]

def cloneBids : List String :=
  ["Object#clone", "String#clone", "Array#clone", "Hash#clone", "Integer#clone",
   "Float#clone", "Symbol#clone", "NilClass#clone", "TrueClass#clone",
   "FalseClass#clone", "Exception#clone"]

/-- Builtins whose CRuby behavior *changes* when a block is passed (`sort` sorts
    by the block, `min`/`max` compare with it, `fetch` computes the default with
    it, …). Our builtin arms are all blockless, so a block here must not be
    silently ignored: dispatch instead falls through to a prelude definition of
    the same name if one exists (`Enumerable#sort`), else gates.
    Builtins CRuby *also* ignores a block for (`length`, `to_s`, …) are
    deliberately absent — gating those would be over-strict. -/
def blockSensitiveBids : List String :=
  ["Array#sort", "Array#min", "Array#max", "Array#sum", "Array#index",
   "Array#uniq", "Hash#fetch", "Hash#delete", "Hash#merge", "Class#new"]


/-! ### Rule implementation helpers (promoted from `run`'s `where` block) -/

def owner (bid : String) : String :=
  (bid.splitOn "#").headD "Object"
def binArg (m : Machine) (args : List Value) (k : Value → BRes) : BRes :=
  match args with
  | [b] => k b
  | _ => .err Boot.argumentErrorId
      s!"wrong number of arguments (given {args.length}, expected 1)" m
def hshPayload? (h : Heap) : Value → Option (Array (Value × Value))
  | .ref o => match (h.get o).payload with
    | .hsh xs => some xs
    | _ => none
  | _ => none
/-- The legacy class hint is superseded by effectful real-class.to_s rendering. -/
def frozenErr (m : Machine) (recv : Value) (_cls : String) : BRes :=
  .frozen recv m
/-- puts: no args → newline; array → recursive per element; string keeps
    an existing trailing newline; nil → blank line; else to_s [V]. -/
def putsGo (m : Machine) (args : List Value) : Nat → Option Machine
  | 0 => none
  | fuel + 1 =>
    args.foldlM (init := m) fun m a =>
      match a with
      | .nil => some (m.emit "\n")
      | .ref o =>
        match (m.heap.get o).payload with
        | .arr xs => putsGo m xs.toList fuel
        | .str s =>
          -- this path writes the payload without going through `toS`, so it
          -- repeats `toS`'s byte-string refusal: CRuby would emit the
          -- raw byte and `m.out` is a Lean `String`
          if (m.heap.get o).binary && hasHighByte s then none
          else some (m.emit (if s.endsWith "\n" then s else s ++ "\n"))
        | _ =>
          -- CRuby tries `to_ary` on a non-Array, non-String argument
          if mayDispatchToAry m.heap a then none
          else match toSP m a with
          | .ok s => some (m.emit (if s.endsWith "\n" then s else s ++ "\n"))
          | .error _ => none
      | _ =>
        if mayDispatchToAry m.heap a then none
        else match toSP m a with
        | .ok s => some (m.emit (s ++ "\n"))
        | .error _ => none
/-- Kernel#raise: [] → re-raise $! or fresh RuntimeError "" [V];
    String → RuntimeError; Class [, msg]; exception object. -/
def putsImpl (m : Machine) (args : List Value) : BRes :=
  match putsGo m args 100 with
  | some m => .ok .nil { m with out := if args.isEmpty then m.out ++ "\n" else m.out }
  | none => .unsupported "puts: impure to_s, to_ary dispatch, or deep nesting"
def raiseClass (m : Machine) (cls : ObjId) (msg : Option Value) : BRes :=
  if !(ancestors m.heap cls).contains Boot.exceptionId then
    .err Boot.typeErrorId "exception class/object expected" m
  else
    match msg with
    | none =>
      let (v, m) := allocExc m cls (className m.heap cls)
      .throwV v m
    | some msgV =>
      match toSP m msgV with
      | .ok s => let (v, m) := allocExc m cls s; .throwV v m
      | .error e => .unsupported e
/-- Class#new: exception classes and plain Object-descendant classes
    (payload-none instances). Builtin-payload classes support only the
    zero-arg empty constructors. -/
def raiseImpl (m : Machine) (args : List Value) : BRes :=
  match args with
  | [] =>
    match m.currentExc with
    | some e => .throwV e m
    | none => .err Boot.runtimeErrorId "" m
  | [a] =>
    match a with
    | .ref o =>
      match (m.heap.get o).payload with
      | .exc _ => .throwV a m
      | .str s => .err Boot.runtimeErrorId s m
      | .cls _ => raiseClass m o none
      | _ => .err Boot.typeErrorId "exception class/object expected" m
    | _ => .err Boot.typeErrorId "exception class/object expected" m
  | [a, msg] =>
    match a with
    | .ref o =>
      match (m.heap.get o).payload with
      | .cls _ => raiseClass m o (some msg)
      | _ => .err Boot.typeErrorId "exception class/object expected" m
    | _ => .err Boot.typeErrorId "exception class/object expected" m
  | _ => .unsupported "raise arity > 2"
def newImpl (m : Machine) (recv : Value) (args : List Value) : BRes :=
  match recv with
  | .ref k =>
    match m.heap.classPayload? k with
    | none => .unsupported "new on non-class"
    | some c =>
      if c.isModule then .unsupported "Module#new"
      else if (ancestors m.heap k).contains Boot.exceptionId then
        match args with
        | [] => let (v, m) := allocExc m k (className m.heap k); .ok v m
        | [msgV] =>
          match toSP m msgV with
          | .ok s => let (v, m) := allocExc m k s; .ok v m
          | .error e => .unsupported e
        | _ => .unsupported "Exception.new arity"
      else if (ancestors m.heap k).contains Boot.stringId then
        -- `String.new` / `MyString.new(str)`: klass is `k`, so a subclass keeps
        -- its own class while carrying a String payload.
        match args with
        | [] => let (o, h) := m.heap.alloc { klass := k, payload := .str "" }
                .ok (.ref o) { m with heap := h }
        | [sv] =>
          match strPayload? m.heap sv with
          | some str => let (o, h) := m.heap.alloc { klass := k, payload := .str str }
                        .ok (.ref o) { m with heap := h }
          | none => .unsupported "String.new with a non-String argument"
        | _ => .unsupported "String.new arity"
      else if (ancestors m.heap k).contains Boot.arrayId then
        match args with
        | [] => let (o, h) := m.heap.alloc { klass := k, payload := .arr #[] }
                .ok (.ref o) { m with heap := h }
        | [.int n] =>
          if n < 0 then .err Boot.argumentErrorId "negative array size" m
          else
            let (o, h) := m.heap.alloc
              { klass := k, payload := .arr (Array.replicate n.toNat .nil) }
            .ok (.ref o) { m with heap := h }
        | [.int n, dflt] =>
          -- Array.new(n, default): n references to the *same* default object
          -- (Ruby semantics; matters only for mutable defaults, unused here).
          if n < 0 then .err Boot.argumentErrorId "negative array size" m
          else
            let (o, h) := m.heap.alloc
              { klass := k, payload := .arr (Array.replicate n.toNat dflt) }
            .ok (.ref o) { m with heap := h }
        | _ => .unsupported "Array.new (block form / non-int size)"
      else if (ancestors m.heap k).contains Boot.hashId then
        match args with
        | [] => let (o, h) := m.heap.alloc { klass := k, payload := .hsh #[] }
                .ok (.ref o) { m with heap := h }
        | [dflt] =>
          -- `Hash.new(default)`: a static default value for missing keys.
          -- (The `Hash.new { |h,k| … }` default_proc form carries a block, so it
          -- is intercepted in `invoke` before this pure builtin — see L42.)
          let (o, h) := m.heap.alloc
            { klass := k, payload := .hsh #[], hashDflt := some (.val dflt) }
          .ok (.ref o) { m with heap := h }
        | _ => .unsupported "Hash.new arity > 1"
      else if k == Boot.randomId then
        -- `Random.new(seed)`: seed a CRuby-compatible MT19937. An *unseeded*
        -- `Random.new` is nondeterministic (like `Kernel#rand`), so it gates.
        match args with
        | [.int seed] =>
          if seed < 0 then .unsupported "Random.new negative seed"
          else
            let (o, h) := m.heap.alloc
              { klass := Boot.randomId, payload := .rng (MT.seeded seed.toNat) }
            .ok (.ref o) { m with heap := h }
        | [] => .unsupported "Random.new (unseeded — nondeterministic)"
        | _ => .unsupported "Random.new arity"
      else if k == Boot.regexpId then
        -- `Regexp.new(src[, opts])`; regex *literals* desugar to exactly this
        -- (desugar C33), so this is the only way a Regexp is built. The pattern
        -- is checked here so a bad one gates at construction rather than at
        -- first use, matching where CRuby raises `RegexpError`.
        let mk (src : String) (opts : Nat) : BRes :=
          match Rx.parse src opts with
          | .error e => .unsupported e
          | .ok _ =>
            let (o, h) := m.heap.alloc
              { klass := Boot.regexpId, payload := .regexp src opts }
            .ok (.ref o) { m with heap := h }
        match args with
        | [s] =>
          match strPayload? m.heap s with
          | some src => mk src 0
          | none =>
            -- `Regexp.new(/x/)` copies the pattern *and its options* [V]
            match s with
            | .ref o => match (m.heap.get o).payload with
              | .regexp src opts => mk src opts
              | _ => .unsupported "Regexp.new of a non-String"
            | _ => .unsupported "Regexp.new of a non-String"
        | [s, o] =>
          match strPayload? m.heap s with
          | none => .unsupported "Regexp.new of a non-String"
          | some src =>
            match o with
            | .int n => if n < 0 then .unsupported "Regexp.new negative options" else mk src n.toNat
            | .nil | .bool false => mk src 0
            -- any other truthy second argument means IGNORECASE [V]
            | _ => mk src 1
        | _ => .unsupported "Regexp.new arity"
      -- `Range.new` is **not** here: it validates its endpoints by dispatching
      -- `<=>`, which a builtin cannot do, so it is prelude Ruby over
      -- `__range_new_unchecked` below (L122, the L115 shape). Range literals
      -- `a..b`/`a...b` desugar to that same `Range.new` send and are validated
      -- with it.
      else if k == Boot.classId || k == Boot.moduleId then
        .unsupported "Class/Module construction requires initializer dispatch"
      else if [Boot.integerId, Boot.floatId,
               Boot.symbolId, Boot.nilClassId, Boot.trueClassId,
               Boot.falseClassId].contains k then
        .unsupported s!"{className m.heap k}.new"
      else if (ancestors m.heap k).any payloadCoreClasses.contains then
        -- a subclass of Proc/Integer/… whose allocator we cannot model
        .unsupported s!"{className m.heap k}.new (payload-core subclass)"
      else
        -- Plain object. A user `initialize` is intercepted in `invoke`
        -- (it must push a frame), so any class reaching here has none —
        -- extra args hit the default `BasicObject#initialize` arity [V].
        match args with
        | [] =>
          let (o, h) := m.heap.alloc { klass := k }
          .ok (.ref o) { m with heap := h }
        | _ => .err Boot.argumentErrorId
            s!"wrong number of arguments (given {args.length}, expected 0)" m
  | _ => .unsupported "new"
def flattenAll (m : Machine) (v : Value) : Nat → Option (List Value)
  | 0 => none
  | fuel + 1 =>
    match arrPayload? m.heap v with
    | some xs => xs.toList.foldlM (init := []) fun acc x =>
        match arrPayload? m.heap x with
        | some _ => do pure (acc ++ (← flattenAll m x fuel))
        | none => some (acc ++ [x])
    | none => some [v]
/-- Sort key: all-numeric or all-string arrays only (general sort needs
    `<=>` dispatch, deferred). -/
def joinImpl (m : Machine) (recv : Value) (args : List Value) : BRes :=
  let sep := match args with
    | [] => some ""
    | [s] => strPayload? m.heap s
    | _ => none
  match sep, flattenAll m recv 100 with
  | some sep, some flat =>
    let parts := flat.mapM fun v =>
      match v with
      | .nil => Except.ok ""
      | _ => toSP m v
    match parts with
    | .ok ps => okStr m (String.intercalate sep ps)
    | .error e => .unsupported e
  | _, _ => .unsupported "join"
/-- Recursively flatten nested arrays (fuel against cycles). -/
def sortKey? (h : Heap) (xs : Array Value) : Option (Array (SortKey × Value)) :=
  xs.mapM fun v =>
    match v with
    | .int n => some (SortKey.num (Float.ofInt n), v)   -- mixed int/float sorts numerically [V]
    | .flt x => some (SortKey.num x, v)
    | _ => match strPayload? h v with
      | some s => some (SortKey.str s, v)
      | none => none
def leKey : SortKey → SortKey → Bool
  | .num a, .num b => a ≤ b
  | .str a, .str b => a ≤ b
  | .num _, .str _ => true
  | .str _, .num _ => false
def sortImpl (m : Machine) (recv : Value) : BRes :=
  match arrPayload? m.heap recv with
  | some xs =>
    match sortKey? m.heap xs with
    | some keyed =>
      -- refuse genuinely mixed str/num arrays (CRuby raises from <=>)
      let allNum := keyed.all (fun (k, _) => match k with | .num _ => true | _ => false)
      let allStr := keyed.all (fun (k, _) => match k with | .str _ => true | _ => false)
      if allNum || allStr then
        let sorted := keyed.toList.mergeSort (fun a b => leKey a.1 b.1)
        let (v, m) := allocArr m (sorted.map (·.2)).toArray
        .ok v m
      else .unsupported "sort of mixed element types"
    | none => .unsupported "sort needs <=> dispatch"
  | none => .unsupported "sort"


end Builtins

end RubyCore
