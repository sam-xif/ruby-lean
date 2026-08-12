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


/-- Can pure repr (Repr.lean) speak for this value? Always for immediates
    and builtin payloads; for plain objects (and main) only while no user
    def has shadowed a repr-sensitive method. -/
partial def pureOk (h : Heap) (reprPure : Bool) : Value → Bool
  | .ref o =>
    match (h.get o).payload with
    | .arr xs => xs.all (pureOk h reprPure)
    | .hsh xs => xs.all fun (k, v) => pureOk h reprPure k && pureOk h reprPure v
    | .none => reprPure && (h.get o).ivars.all (fun (_, v) => pureOk h reprPure v)
    | .proc _ => false   -- Proc repr is address-based → never pure
    | _ => true
  | _ => true

def inspectP (m : Machine) (v : Value) : Except String String :=
  if pureOk m.heap m.reprPure v then inspect m.heap v
  else .error "inspect after user override of repr-sensitive method"

def toSP (m : Machine) (v : Value) : Except String String :=
  if pureOk m.heap m.reprPure v then toS m.heap v
  else .error "to_s after user override of repr-sensitive method"

/-- Operand description in "no implicit conversion of X into Y" errors:
    class name, except nil/true/false literally [V]
    (`"a"+:k` → "…of Symbol into String", `"a"+nil` → "…of nil into…"). -/
def coerceName (h : Heap) : Value → String
  | .nil => "nil"
  | .bool b => toString b
  | v => className h (classOf h v)

/-- Operand description in "X can't be coerced into C" and "comparison of C
    with X failed" errors: special constants show their *inspect*
    (`1+:k` → ":k can't be coerced…"), other objects their class name [V]. -/
def coerceDesc (h : Heap) : Value → String
  | .nil => "nil"
  | .bool b => toString b
  | .sym s => symInspect s
  | .int n => toString n
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
      hashDflt := src.hashDflt, frozen := keepFrozen && src.frozen }
  (.ref o2, { m with heap := h })

def okStr (m : Machine) (s : String) : BRes :=
  let (v, m) := allocStr m s
  .ok v m

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

def numBin (recvCls : String) (m : Machine) (a : Value) (b : Value)
    (fi : Int → Int → BRes) (ff : Float → Float → BRes) : BRes :=
  match num? a, num? b with
  | some (.i x), some (.i y) => fi x y
  | some (.i x), some (.f y) => ff (Float.ofInt x) y
  | some (.f x), some (.i y) => ff x (Float.ofInt y)
  | some (.f x), some (.f y) => ff x y
  | _, _ => .err Boot.typeErrorId
      s!"{coerceDesc m.heap b} can't be coerced into {recvCls}" m

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
        | .str s => some (m.emit (if s.endsWith "\n" then s else s ++ "\n"))
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
      else if k == Boot.rangeId then
        -- `Range.new(lo, hi[, excl])` (range literals `a..b`/`a...b` desugar here).
        let mk (lo hi : Value) (excl : Bool) : BRes :=
          let (o, h) := m.heap.alloc { klass := Boot.rangeId, payload := .range lo hi excl }
          .ok (.ref o) { m with heap := h }
        match args with
        | [lo, hi] => mk lo hi false
        | [lo, hi, .bool e] => mk lo hi e
        | [lo, hi, .nil] => mk lo hi false
        | _ => .unsupported "Range.new arity"
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
