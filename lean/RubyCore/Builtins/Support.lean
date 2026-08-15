import RubyCore.Machine
import RubyCore.Regex.Parse
import RubyCore.Repr

/-
Shared support for the builtin rules: value/payload accessors, allocation
helpers, the numeric and string-ordering primitives, the bid lists that the
dispatcher consults before matching, and the implementation helpers the rules
call (`binArg`, `putsImpl`, `raiseImpl`, `newImpl`, `sortImpl`, …).

Split out of `RubyCore/Builtins.lean` (L98) with no behaviour change: these were
the file's leading definitions plus the `where` block of the single 1,290-line
`run`. Promoting the `where` helpers to top level is what makes the per-class
rule files possible, since a `where` binding is not visible outside its own
definition; the only other change is ordering them by use (`putsGo` before
`putsImpl`, `raiseClass` before `raiseImpl`, `flattenAll` before `joinImpl`).
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
  | unsupported (reason : String)


namespace Builtins


/-- Methods whose user definition changes what **`inspect`** would print. `to_s`
    is deliberately absent: a user `to_s` does not change `Object#inspect`, which
    renders class and ivars [V]. `message` is present because `Exception#inspect`
    is built from it. -/
def inspectSensitive : List String := ["inspect", "message"]

/-- The same, for **`to_s`**. Splitting the two lists is what keeps the check
    from being over-strict: before L103 a single global flag conflated them, so
    `class Integer; def to_s; "x"; end` made `p 1` inadmissible even though
    `p` uses `inspect` and is unaffected. -/
def toSSensitive : List String := ["to_s", "message"]

/-- Does `k`'s ancestor chain carry a **non-builtin** definition of one of
    `sens`? This is the per-class replacement for the old global `reprPure` flag
    (L103): a `def to_s` on one class used to make pure repr refuse to speak for
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

/-- Can pure repr (Repr.lean) speak for this value? Only if nothing in its
    class's ancestor chain overrides a repr-sensitive method — and, for
    containers, recursively for what they hold. -/
partial def pureOk (h : Heap) (sens : List String) : Value → Bool
  | .ref o =>
    let own := !reprOverridden h sens (h.get o).klass
    match (h.get o).payload with
    -- A container renders its elements with *their* renderer, so purity is
    -- recursive even when the container's own class is untouched — and it
    -- recurses with the **same** sensitivity it was asked about, since
    -- `[x].inspect` uses `x.inspect` while `[x].join` uses `x.to_s`.
    | .arr xs => own && xs.all (pureOk h sens)
    | .hsh xs => own && xs.all fun (k, v) => pureOk h sens k && pureOk h sens v
    | .none => own && (h.get o).ivars.all (fun (_, v) => pureOk h sens v)
    -- A Range is a container of two: `(a..b).inspect` calls `a.inspect`, so an
    -- endpoint with a user `inspect` makes the range impure too. Missing this was
    -- a **wrong answer** — the pure path rendered the endpoint's default
    -- `#<C:0x…>` and ignored the override — found by the L122 range head, which
    -- gives its endpoints a fixed `inspect` precisely so no address is observed.
    | .range lo hi _ => own && pureOk h sens lo && pureOk h sens hi
    | .proc _ => false   -- Proc repr is address-based → never pure
    | _ => own
  | v => !reprOverridden h sens (realClassOf h v)

/-- When pure repr cannot speak for a value, the *prelude twin* to dispatch
    instead (L116). This is L63's "defer to the prelude" pattern: the twin has a
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
  if bid == "Object#inspect" || bid == "Array#inspect" || bid == "Hash#inspect" then
    if pureOk h inspectSensitive recv then none else some "__inspect_slow"
  else if bid == "Object#to_s" || bid == "Array#to_s" || bid == "Hash#to_s"
       || bid == "Range#to_s" then
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
    (`"a"+:k` → "…of Symbol into String", `"a"+nil` → "…of nil into…"). -/
def coerceName (h : Heap) : Value → String
  | .nil => "nil"
  | .bool b => toString b
  | v => className h (classOf h v)

/-- Operand description in "X can't be coerced into C" and "comparison of C
    with X failed" errors: special constants show their *inspect*
    (`1+:k` → ":k can't be coerced…"), other objects their class name [V].

    A **Float** shows its inspect too — `rb_cmperr` and `coerce_failed` both test
    `RB_FLOAT_TYPE_P` alongside `SPECIAL_CONST_P`. Unreachable from `numBin`,
    where a Float argument always coerces, and so missing here until `Comparable`
    started routing its own `comparison of … failed` through this rule (L123):
    `Tok.new < 1.5` said "comparison of Tok with Float failed" for CRuby's
    "…with 1.5 failed". -/
def coerceDesc (h : Heap) : Value → String
  | .nil => "nil"
  | .bool b => toString b
  | .sym s => symInspect s
  | .int n => toString n
  | .flt x => rubyFloatRepr x
  | v => className h (classOf h v)

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
   Boot.floatId, Boot.symbolId]

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
  else .exc ""

/-- Does `v`'s class resolve `==` to a *user* (non-builtin) method? Builtins
    that lean on default value-equality (`Array#include?`/`index`, …) must gate
    when an operand overrides `==`, since a pure comparison can't dispatch it. -/
def hasUserEq (h : Heap) (v : Value) : Bool :=
  match lookup h v "==" with
  | some (_, md) => md.builtin.isNone
  | none => false

/-- Would CRuby dispatch `to_ary` on this value? `Kernel#puts` does, to flatten
    its arguments — so a *user* `to_ary`, or a user `method_missing` that could
    intercept it, means a pure `puts` would silently print where CRuby raises
    (`can't convert C to Array (C#to_ary gives String)`). A builtin cannot run a
    dispatch, so `puts` gates instead (L66). -/
def mayDispatchToAry (h : Heap) (v : Value) : Bool :=
  (match lookup h v "to_ary" with | some (_, md) => md.builtin.isNone | none => false)
  || (match lookup h v "method_missing" with | some (_, md) => md.builtin.isNone | none => false)

/-- Allocate a String with an explicit encoding tag (L117). -/
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
  let (o, h) := m.heap.alloc { klass := cls, payload := .exc msg }
  (.ref o, { m with heap := h })

/-- `dup`: a fresh object with the same class, payload and **instance variables**
    (`str.dup` keeps `@ivar` [V]), but *not* the frozen bit and *not* the
    singleton class. `keepFrozen` gives `clone`, which does preserve it. -/
def dupObj (m : Machine) (o : ObjId) (keepFrozen : Bool) : Value × Machine :=
  let src := m.heap.get o
  let (o2, h) := m.heap.alloc
    { klass := src.klass, ivars := src.ivars, payload := src.payload,
      hashDflt := src.hashDflt, frozen := keepFrozen && src.frozen,
      -- the encoding tag is part of the copy: `"café".b.dup.encoding` is
      -- ASCII-8BIT [V] (L118)
      binary := src.binary }
  (.ref o2, { m with heap := h })

def okStr (m : Machine) (s : String) : BRes :=
  let (v, m) := allocStr m s
  .ok v m

/-- Allocate a String result with an explicit encoding tag (L118). -/
def okStrEnc (m : Machine) (binary : Bool) (s : String) : BRes :=
  let (v, m) := allocStrEnc m s binary
  .ok v m

/-- Allocate a String result that **inherits `src`'s encoding tag** (L118).
    `src` is normally the receiver: every byte-derived String result in CRuby
    carries the encoding of the String it was derived from, and for a MatchData
    receiver the tag on the object records its *subject*'s encoding, so the same
    helper serves `MatchData#[]`/`pre_match`/… -/
def okStrFrom (m : Machine) (src : Value) (s : String) : BRes :=
  okStrEnc m (isBinaryStr m.heap src) s

/-- Is this a binary String holding a byte the model cannot let a tag-blind rule
    touch — one at or above 0x80 (L118)? An *ASCII-only* binary String is
    excluded on purpose: every content answer over it is identical to the UTF-8
    one, so only its tag is at stake, and the String rules propagate that. -/
def unrepresentableByteStr (h : Heap) (v : Value) : Bool :=
  match strPayload? h v with
  | some s => isBinaryStr h v && hasHighByte s
  | none => false

/-- The rules admitted to run with such an operand (L118) — each either handles
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
  ["String#+", "String#*", "String#<<", "String#concat", "String#==", "String#eql?",
   "String#!=", "String#length", "String#size", "String#empty?", "String#ord",
   "String#to_i", "String#to_f", "String#to_s", "String#to_str", "String#to_sym",
   "String#inspect", "String#chars", "String#reverse", "String#upcase",
   "String#downcase", "String#strip", "String#chomp", "String#[]", "String#+@",
   "String#-@", "String#freeze", "String#frozen?", "String#hash",
   "String#__binary?", "String#__bytes", "String#__as_binary", "String#__as_utf8",
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
   "Object#hash", "Object#class", "Object#nil?", "Object#is_a?", "Object#kind_of?",
   "Object#instance_of?", "Object#respond_to?", "Object#freeze", "Object#frozen?",
   "Object#inspect", "Object#p", "Object#__user_defines?",
   -- reads and writes neither operand, only the frame's `$~` routing (L121)
   "Object#__match_to_caller",
   -- render nothing of the operand but its *class name* (L123)
   "Object#__coerce_failed", "Object#__cmp_failed"]

/-- The encoding tag of `a ++ b` (L118), CRuby's compatibility rule [V]: the
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
    .error "Encoding::CompatibilityError from concatenating a byte string with UTF-8 (L118)"
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
    `coerce` — the end of the road for `coerceDefer?` (L123) and the answer
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

/-! ### The coerce protocol (L123)

`numBin`/`numCmp` above answer for two numbers and raise for anything else. That
second half is wrong, and not by a message: CRuby's numeric operators run
`rb_num_coerce_bin`, which **asks the argument to `coerce` itself** and then
re-dispatches the operator on the pair it returns. So `3 + Money.new(4)` is `7`,
the `coerce` body's side effects happen, and the error — when there is one —
says *why* ("coerce must return [x, y]" for a wrong shape, "X can't be coerced
into Integer" only when nothing answered at all).

A builtin cannot dispatch, so the failure path defers to a prelude twin, exactly
as the repr builtins defer to theirs (`reprDefer?`, L116). Deferral is keyed on
"could a `coerce` possibly run", so every operand that *is* a number, and every
operand whose class chain offers nothing, keeps the Lean fast path untouched. -/

/-- Could an ordinary send of `coerce` reach a Ruby body on `v`? A `coerce`
    from the prelude counts (a future prelude `Rational` will have a real one);
    a `method_missing` does **not** if it came from the prelude, because the only
    one there is `Pathname`'s, which exists to *refuse* — routing through it
    would turn today's correct `TypeError` into a gate. -/
def mayCoerce (h : Heap) (v : Value) : Bool :=
  (match lookup h v "coerce" with
   | some (_, md) => md.builtin.isNone && !md.undefined
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
  | "Integer#+"  | "Float#+"  => some "__coerce_add"
  | "Integer#-"  | "Float#-"  => some "__coerce_sub"
  | "Integer#*"  | "Float#*"  => some "__coerce_mul"
  | "Integer#/"  | "Float#/"  => some "__coerce_div"
  | "Integer#%"  | "Float#%"  => some "__coerce_mod"
  | "Integer#**" | "Float#**" => some "__coerce_pow"
  | "Integer#divmod" | "Float#divmod" => some "__coerce_divmod"
  | "Integer#<"  | "Float#<"  => some "__coerce_lt"
  | "Integer#>"  | "Float#>"  => some "__coerce_gt"
  | "Integer#<=" | "Float#<=" => some "__coerce_le"
  | "Integer#>=" | "Float#>=" => some "__coerce_ge"
  | "Integer#<=>" | "Float#<=>" => some "__coerce_cmp"
  | _ => none

/-- When a numeric builtin must dispatch rather than answer, the prelude twin to
    dispatch instead (L123). Numeric receiver, non-numeric argument, and one of
    the two hooks that can make the difference observable — nothing else pays
    for the check, and `Integer#+` of two Integers cannot reach it. -/
def coerceDefer? (h : Heap) (bid : String) (recv : Value) (args : List Value) :
    Option String :=
  match args with
  | [b] =>
    if (num? recv).isNone || (num? b).isSome then none
    else if bid == "Integer#==" || bid == "Float#==" then
      if hasProgramEq h b then some "__eq_reverse" else none
    else if mayCoerce h b then coerceTwin? bid
    else none
  | _ => none

/-- Every reason a builtin defers to a prelude twin instead of running: repr
    purity (L116) and the coerce protocol (L123). One hook, so `invoke` has one
    place to consult and the dispatch metatheorems one hypothesis to carry. -/
def deferTwin? (h : Heap) (bid : String) (recv : Value) (args : List Value) :
    Option String :=
  reprDefer? h bid recv args <|> coerceDefer? h bid recv args

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

/-- Normalize a `(start, len)` slice against a collection of size `n` (L68):
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
  ["Object#class", "Object#inspect", "Object#to_s", "Object#nil?",
   "Object#frozen?", "Object#freeze", "Object#block_given?",
   "NilClass#nil?", "NilClass#to_s", "NilClass#inspect", "NilClass#to_a",
   "TrueClass#to_s", "TrueClass#inspect", "FalseClass#to_s", "FalseClass#inspect",
   "Integer#inspect", "Integer#to_i", "Integer#to_f", "Integer#abs", "Integer#succ",
   "Integer#pred", "Integer#zero?", "Integer#positive?", "Integer#negative?",
   "Integer#even?", "Integer#odd?", "Integer#-@",
   "Float#to_s", "Float#inspect", "Float#to_f", "Float#-@", "Float#abs", "Float#zero?",
   "Float#nan?", "Float#to_i",
   "String#to_s", "String#to_str", "String#inspect", "String#length",
   "String#size", "String#empty?", "String#reverse", "String#upcase",
   "String#downcase", "String#strip", "String#frozen?", "String#dup",
   "String#to_sym", "String#freeze",
   "Symbol#to_s", "Symbol#inspect", "Symbol#to_sym", "Symbol#to_proc",
   "Array#length", "Array#size", "Array#empty?", "Array#inspect",
   "Array#to_s", "Array#to_a", "Array#reverse", "Array#compact",
   "Array#dup", "Array#clone", "Object#dup", "Object#clone",
   "String#clone", "Hash#clone", "Array#frozen?", "Array#freeze", "Array#sort", "Array#uniq",
   "Hash#length", "Hash#size", "Hash#empty?", "Hash#keys", "Hash#values",
   "Hash#inspect", "Hash#to_s", "Hash#dup",
   "Exception#message", "Exception#to_s", "Exception#inspect",
   "Module#name", "Module#to_s", "Module#inspect", "Module#ancestors",
   "Proc#lambda?", "Proc#to_proc", "Object#initialize",
   "Range#inspect", "Range#to_s", "Range#first", "Range#last", "Range#begin",
   "Range#end", "Range#exclude_end?"]

/-- The `dup`/`clone` bids, listed rather than matched with `String.endsWith`
    (L73): `endsWith` is **not kernel-reducible**, so having it at the top of
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
    the same name if one exists (`Enumerable#sort`), else gates (L63).
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
def frozenErr (m : Machine) (recv : Value) (cls : String) : BRes :=
  match inspectP m recv with
  | .ok r => .err Boot.frozenErrorId s!"can't modify frozen {cls}: {r}" m
  | .error e => .unsupported e
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
          -- repeats `toS`'s byte-string refusal (L118): CRuby would emit the
          -- raw byte and `m.out` is a Lean `String`
          if (m.heap.get o).binary && hasHighByte s then none
          else some (m.emit (if s.endsWith "\n" then s else s ++ "\n"))
        | _ =>
          -- CRuby tries `to_ary` on a non-Array, non-String argument (L66)
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
        -- its own class while carrying a String payload (L70).
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
        -- `Random.new` is nondeterministic (like `Kernel#rand`, L43), so it gates.
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
        -- first use, matching where CRuby raises `RegexpError` (L101).
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
      else if k == Boot.classId then
        -- `Class.new(superclass = Object)`: an **anonymous** class (empty name,
        -- rendered `#<Class:0x…>`; a later constant assignment names it, L72).
        -- The block form carries a block, so it is intercepted in `invoke`.
        match args with
        | [] =>
          let (o, h) := m.heap.alloc
            { klass := Boot.classId,
              payload := .cls { superclass := some Boot.objectId, name := "" } }
          .ok (.ref o) { m with heap := h }
        | [.ref sup] =>
          match m.heap.classPayload? sup with
          | some sc =>
            if sc.isModule then
              .err Boot.typeErrorId "superclass must be an instance of Class (given a Module)" m
            else
              let (o, h) := m.heap.alloc
                { klass := Boot.classId,
                  payload := .cls { superclass := some sup, name := "" } }
              .ok (.ref o) { m with heap := h }
          | none =>
            .err Boot.typeErrorId
              s!"superclass must be an instance of Class (given an instance of {className m.heap (classOf m.heap (.ref sup))})" m
        | _ => .unsupported "Class.new arity"
      else if k == Boot.moduleId then
        match args with
        | [] =>
          let (o, h) := m.heap.alloc
            { klass := Boot.moduleId,
              payload := .cls { superclass := Option.none, name := "", isModule := true } }
          .ok (.ref o) { m with heap := h }
        | _ => .unsupported "Module.new arity"
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
