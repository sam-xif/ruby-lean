/-
The axiomatized builtin methods (artifact 01 §2 `origin = builtin`): primitive
rules keyed by bid = "Owner#name", registered into H₀'s method tables by
Boot.builtinMethods so that lookup/inheritance/shadowing are uniform — a user
`def to_s` on Object shadows the builtin through the ordinary dispatch rule.

Error messages are byte-for-byte from CRuby 4.0.5 probes (2026-07-07); the
difftest engine is the enforcement mechanism.

Anything not modeled answers `unsupported` (never a guessed value) — the
fragment gate, not an error.
-/
import RubyCore.Machine
import RubyCore.Repr

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

/-- Run builtin `bid` ("Owner#name"). `implicitSelf` is whether the send had
    no explicit receiver (needed by nothing yet; visibility is deferred). -/
def run (bid : String) (recv : Value) (args : List Value) (m : Machine) : BRes :=
  let h := m.heap
  if zeroArgBids.contains bid && !args.isEmpty then
    .err Boot.argumentErrorId
      s!"wrong number of arguments (given {args.length}, expected 0)" m
  else if dupBids.contains bid || cloneBids.contains bid then
    -- One rule for every class (L66): copies the payload *and* the instance
    -- variables (`str.dup` keeps `@ivar` [V]); `dup` drops the frozen bit,
    -- `clone` keeps it. Gates where a copy would need more than the object:
    -- a singleton class (clone copies it) or a class/module payload (a duped
    -- class is anonymous, which our `name` field cannot express).
    match recv with
    | .ref o =>
      if (h.get o).eigen.isSome then
        .unsupported "dup/clone of an object with a singleton class"
      else match (h.get o).payload with
        | .cls _ => .unsupported "dup/clone of a class/module"
        | .rng _ => .unsupported "dup/clone of a Random (state identity)"
        | _ => let (v, m) := dupObj m o (cloneBids.contains bid); .ok v m
    | _ => .ok recv m   -- immediates dup/clone to themselves [V]
  else
  match bid with
  /- ─── BasicObject / Object core ─── -/
  | "BasicObject#==" | "Object#==" =>
    match args with
    | [b] =>
      -- default == is identity — except Exception, which compares
      -- class + message [V]
      match recv, b with
      | .ref x, .ref y =>
        match (h.get x).payload, (h.get y).payload with
        | .exc ma, .exc mb =>
          .ok (.bool ((h.get x).klass == (h.get y).klass && ma == mb)) m
        | _, _ => .ok (.bool (recv.identEq b)) m
      | _, _ => .ok (.bool (recv.identEq b)) m
    | _ => .unsupported "==/arity"
  | "BasicObject#equal?" | "Object#equal?" =>
    match args with
    | [b] => .ok (.bool (recv.identEq b)) m
    | _ => .unsupported "equal?/arity"
  | "Object#eql?" =>
    match args with
    | [b] => .ok (.bool (valueEql h recv b)) m
    | _ => .unsupported "eql?/arity"
  | "BasicObject#!" | "Object#!" => .ok (.bool (!recv.truthy)) m
  | "BasicObject#!=" | "Object#!=" =>
    match args with
    | [b] => .ok (.bool (!(valueEq h recv b))) m
    | _ => .unsupported "!=/arity"
  | "Object#nil?" | "NilClass#nil?" =>
    .ok (.bool (match recv with | .nil => true | _ => false)) m
  | "Object#class" => .ok (.ref (realClassOf h recv)) m
  | "Object#inspect" =>
    match inspectP m recv with
    | .ok s => okStr m s
    | .error e => .unsupported e
  | "Object#to_s" =>
    match toSP m recv with
    | .ok s => okStr m s
    | .error e => .unsupported e
  | "Object#frozen?" =>
    match recv with
    | .ref o => .ok (.bool (h.get o).frozen) m
    | _ => .ok (.bool true) m
  | "Object#freeze" | "String#freeze" | "Array#freeze" =>
    match recv with
    | .ref o => .ok recv { m with heap := h.set o { h.get o with frozen := true } }
    | _ => .ok recv m
  | "Object#is_a?" | "Object#kind_of?" =>
    match args with
    | [.ref k] =>
      if (h.classPayload? k).isSome then .ok (.bool (isA h recv k)) m
      else .err Boot.typeErrorId "class or module required" m
    | [_] => .err Boot.typeErrorId "class or module required" m
    | _ => .unsupported "is_a?/arity"
  | "Object#instance_of?" =>
    match args with
    | [.ref k] =>
      if (h.classPayload? k).isSome then .ok (.bool (realClassOf h recv == k)) m
      else .err Boot.typeErrorId "class or module required" m
    | [_] => .err Boot.typeErrorId "class or module required" m
    | _ => .unsupported "instance_of?/arity"
  | "Object#block_given?" =>
    -- true iff the enclosing method activation received a block (the block
    -- is propagated onto block frames, so the current frame's blk answers) [V]
    .ok (.bool m.currentFrame.blk.isSome) m
  | "Object#__unsupported__" =>
    -- The prelude's fragment gate (L62): RubyCore-level core-library code cannot
    -- return `.unsupported` on its own, so it calls this to declare a form it
    -- does not model (`Enumerator`, a `<=>`-less comparison, …). Keeps the
    -- "declare, never guess" discipline available to prelude authors.
    match args with
    | [a] => match strPayload? h a with
      | some s => .unsupported s
      | none => .unsupported "prelude gate (non-String reason)"
    | _ => .unsupported "prelude gate"
  | "Object#require" | "Object#require_relative" =>
    -- Linked programs have their internal deps inlined; a residual `require` of a
    -- stdlib (e.g. `benchmark`/`yaml`) is a no-op that returns true (as CRuby's
    -- first load does). The result is essentially never observed.
    .ok (.bool true) m
  -- Registered on Range (not inherited from Object) so the L6 shadow check sees
  -- the right owner; `Repr` already renders `.range` payloads [V].
  | "Range#inspect" =>
    match inspectP m recv with
    | .ok s => okStr m s
    | .error e => .unsupported e
  | "Range#to_s" =>
    match toSP m recv with
    | .ok s => okStr m s
    | .error e => .unsupported e
  | "Range#first" | "Range#begin" =>
    match recv with
    | .ref o => match (h.get o).payload with
      | .range lo _ _ => .ok lo m
      | _ => .unsupported "Range#first"
    | _ => .unsupported "Range#first"
  | "Range#last" | "Range#end" =>
    match recv with
    | .ref o => match (h.get o).payload with
      | .range _ hi _ => .ok hi m
      | _ => .unsupported "Range#last"
    | _ => .unsupported "Range#last"
  | "Range#exclude_end?" =>
    match recv with
    | .ref o => match (h.get o).payload with
      | .range _ _ e => .ok (.bool e) m
      | _ => .unsupported "Range#exclude_end?"
    | _ => .unsupported "Range#exclude_end?"
  | "Random#rand" =>
    match recv with
    | .ref o =>
      match (h.get o).payload with
      | .rng st =>
        match args with
        | [] =>   -- Random#rand → Float in [0,1); mutate the object's MT state
          let (r, st') := MT.nextReal st
          .ok (.flt r) { m with heap := h.set o { h.get o with payload := .rng st' } }
        | _ => .unsupported "Random#rand(n) (bounded draw not modeled)"
      | _ => .unsupported "rand on non-Random receiver"
    | _ => .unsupported "Random#rand"
  | "Object#rand" =>
    -- Deterministic placeholder for CRuby's *unseeded* Kernel#rand. Its value is
    -- observationally irrelevant to any program CRuby runs deterministically: an
    -- output that depends on unseeded `rand` is nondeterministic under CRuby's
    -- double-run and excluded as `control_invalid`, so a fixed value here can
    -- never cause a recorded disagreement — while output-*independent* uses run
    -- (q_learning's `rand < exploration` with exploration 0 always takes the
    -- exploit branch since 0.0 < 0.0 is false, matching CRuby's rand ∈ [0,1)).
    -- Seeded RNG (`srand`, `Random.new(seed)`) stays UNMODELED (gates), so a
    -- deterministic seeded program cannot silently diverge here. See notes L43.
    match args with
    | [] => .ok (.flt 0.0) m                           -- rand → Float in [0,1)
    | [.int n] =>
      if n > 0 then .ok (.int 0) m                     -- rand(n) → Integer in [0,n)
      else .unsupported "rand(n <= 0)"                  -- rand(0) is Float [0,1): rare, gate
    | _ => .unsupported "rand (float/range arg)"
  /- ─── Kernel I/O ─── -/
  | "Object#puts" => putsImpl m args
  | "Object#print" =>
    args.foldlM (fun m a => do
      match toSP m a with
      | .ok s => pure (m.emit s)
      | .error e => none) m
    |> fun
      | some m => .ok .nil m
      | none => .unsupported "print: impure to_s"
  | "Object#p" =>
    let rec go (m : Machine) : List Value → Option Machine
      | [] => some m
      | a :: rest =>
        match inspectP m a with
        | .ok s => go (m.emit (s ++ "\n")) rest
        | .error _ => none
    match go m args with
    | none => .unsupported "p: impure inspect"
    | some m =>
      match args with
      | [] => .ok .nil m
      | [a] => .ok a m
      | _ => let (v, m) := allocArr m args.toArray; .ok v m
  | "Object#String" =>
    match args with
    | [a] =>
      match toSP m a with
      | .ok s => okStr m s
      | .error e => .unsupported e
    | _ => .unsupported "String()/arity"
  | "Object#raise" => raiseImpl m args
  /- ─── nil / booleans ─── -/
  | "NilClass#to_s" => okStr m ""
  | "NilClass#inspect" => okStr m "nil"
  | "NilClass#to_a" => let (v, m) := allocArr m #[]; .ok v m
  | "NilClass#&" | "FalseClass#&" => .ok (.bool false) m
  | "NilClass#|" | "FalseClass#|" =>
    match args with
    | [b] => .ok (.bool b.truthy) m
    | _ => .unsupported "|/arity"
  | "TrueClass#&" =>
    match args with
    | [b] => .ok (.bool b.truthy) m
    | _ => .unsupported "&/arity"
  | "TrueClass#|" => .ok (.bool true) m
  | "TrueClass#to_s" | "TrueClass#inspect" => okStr m "true"
  | "FalseClass#to_s" | "FalseClass#inspect" => okStr m "false"
  /- ─── Integer / Float ─── -/
  | "Integer#+" | "Float#+" =>
    binArg m args fun b =>
      numBin (owner bid) m recv b
        (fun x y => .ok (.int (x + y)) m) (fun x y => .ok (.flt (x + y)) m)
  | "Integer#-" | "Float#-" =>
    binArg m args fun b =>
      numBin (owner bid) m recv b
        (fun x y => .ok (.int (x - y)) m) (fun x y => .ok (.flt (x - y)) m)
  | "Integer#*" | "Float#*" =>
    binArg m args fun b =>
      numBin (owner bid) m recv b
        (fun x y => .ok (.int (x * y)) m) (fun x y => .ok (.flt (x * y)) m)
  | "Integer#/" | "Float#/" =>
    binArg m args fun b =>
      numBin (owner bid) m recv b
        (fun x y =>
          if y == 0 then .err Boot.zeroDivisionErrorId "divided by 0" m
          else .ok (.int (Int.fdiv x y)) m)  -- Ruby / is floor division [V]
        (fun x y => .ok (.flt (x / y)) m)
  | "Integer#%" | "Float#%" =>
    binArg m args fun b =>
      numBin (owner bid) m recv b
        (fun x y =>
          if y == 0 then .err Boot.zeroDivisionErrorId "divided by 0" m
          else .ok (.int (Int.fmod x y)) m)  -- sign follows divisor [V]
        (fun x y =>
          -- Float modulo: `x - y * (x/y).floor`, sign follows the divisor (Ruby).
          if y == 0 then .unsupported "Float modulo by zero"
          else .ok (.flt (x - y * (x / y).floor)) m)
  | "Integer#**" =>
    binArg m args fun b =>
      match recv, b with
      | .int x, .int y =>
        if y ≥ 0 then .ok (.int (x ^ y.toNat)) m
        else .unsupported "Integer ** negative (Rational result)"
      | _, _ => .unsupported "** with non-integer"
  | "Float#**" =>
    binArg m args fun b =>
      match recv, num? b with
      | .flt x, some nb =>
        let y := match nb with | .i n => Float.ofInt n | .f v => v
        .ok (.flt (Float.pow x y)) m
      | _, _ => .unsupported "Float#** non-numeric"
  | "Integer#-@" =>
    match recv with
    | .int n => .ok (.int (-n)) m
    | _ => .unsupported "-@"
  | "Float#-@" =>
    match recv with
    | .flt x => .ok (.flt (-x)) m
    | _ => .unsupported "-@"
  | "Integer#==" | "Float#==" =>
    binArg m args fun b =>
      match num? b with
      | some _ => .ok (.bool (valueEq h recv b)) m
      | none => .ok (.bool false) m
  | "Integer#!=" =>
    binArg m args fun b => .ok (.bool (!(valueEq h recv b))) m
  | "Integer#<" | "Float#<" =>
    binArg m args fun b => numCmp (owner bid) m recv b fun o => .ok (.bool (o == .lt)) m
  | "Integer#>" | "Float#>" =>
    binArg m args fun b => numCmp (owner bid) m recv b fun o => .ok (.bool (o == .gt)) m
  | "Integer#<=" | "Float#<=" =>
    binArg m args fun b => numCmp (owner bid) m recv b fun o => .ok (.bool (o != .gt)) m
  | "Integer#>=" | "Float#>=" =>
    binArg m args fun b => numCmp (owner bid) m recv b fun o => .ok (.bool (o != .lt)) m
  | "Integer#<=>" | "Float#<=>" =>
    binArg m args fun b =>
      match num? b with
      | some _ => numCmp (owner bid) m recv b fun o => .ok (ordValue o) m
      | none => .ok .nil m  -- <=> with incomparable → nil [V]
  | "Integer#to_s" | "Integer#inspect" =>
    match recv, args with
    | .int n, [] => okStr m (toString n)
    | _, _ => .unsupported "Integer#to_s with base"
  | "Integer#to_i" => .ok recv m
  | "Integer#to_f" =>
    match recv with | .int n => .ok (.flt (Float.ofInt n)) m | _ => .unsupported "to_f"
  | "Float#to_f" => .ok recv m
  | "Integer#abs" =>
    match recv with
    | .int n => .ok (.int n.natAbs) m
    | _ => .unsupported "abs"
  | "Integer#succ" =>
    match recv with | .int n => .ok (.int (n + 1)) m | _ => .unsupported "succ"
  | "Integer#pred" =>
    match recv with | .int n => .ok (.int (n - 1)) m | _ => .unsupported "pred"
  | "Integer#zero?" =>
    match recv with | .int n => .ok (.bool (n == 0)) m | _ => .unsupported "zero?"
  | "Integer#positive?" =>
    match recv with | .int n => .ok (.bool (n > 0)) m | _ => .unsupported "positive?"
  | "Integer#negative?" =>
    match recv with | .int n => .ok (.bool (n < 0)) m | _ => .unsupported "negative?"
  | "Integer#even?" =>
    match recv with | .int n => .ok (.bool (n % 2 == 0)) m | _ => .unsupported "even?"
  | "Integer#odd?" =>
    match recv with | .int n => .ok (.bool (n % 2 != 0)) m | _ => .unsupported "odd?"
  | "Integer#eql?" | "Float#eql?" =>
    binArg m args fun b => .ok (.bool (valueEql h recv b)) m
  | "Integer#hash" => .unsupported "Integer#hash (seeded)"
  | "Float#to_s" | "Float#inspect" =>
    match recv with
    | .flt x => okStr m (rubyFloatRepr x)     -- L45 shortest round-trip
    | _ => .unsupported "Float#to_s"
  | "Float#to_i" | "Float#to_int" | "Float#truncate" =>
    match recv with
    | .flt x =>
      if x.isNaN || x.isInf then .unsupported "Float#to_i of Infinity/NaN (FloatDomainError)"
      else
        -- Exact truncation toward zero via the IEEE bits (no lossy Float→Int).
        let bits := x.toBits
        let neg := (bits >>> 63) == 1
        let expo := ((bits >>> 52) &&& 0x7FF).toNat
        let frac := (bits &&& 0xFFFFFFFFFFFFF).toNat
        let (mant, e) := if expo == 0 then (frac, (-1074 : Int))
                         else (frac + 0x10000000000000, (expo : Int) - 1075)
        let intAbs : Nat := if e ≥ 0 then mant <<< e.toNat else mant >>> (-e).toNat
        .ok (.int (if neg then -(Int.ofNat intAbs) else Int.ofNat intAbs)) m
    | _ => .unsupported "to_i"
  | "Float#abs" =>
    match recv with | .flt x => .ok (.flt x.abs) m | _ => .unsupported "abs"
  | "Float#zero?" =>
    match recv with | .flt x => .ok (.bool (x == 0.0)) m | _ => .unsupported "zero?"
  | "Float#nan?" =>
    match recv with | .flt x => .ok (.bool x.isNaN) m | _ => .unsupported "nan?"
  /- ─── String ─── -/
  | "String#+" =>
    binArg m args fun b =>
      match strPayload? h recv, strPayload? h b with
      | some s, some t => okStr m (s ++ t)
      | some _, none => .err Boot.typeErrorId
          s!"no implicit conversion of {coerceName h b} into String" m
      | _, _ => .unsupported "String#+"
  | "String#*" =>
    binArg m args fun b =>
      match strPayload? h recv, b with
      | some s, .int n =>
        if n < 0 then .err Boot.argumentErrorId "negative argument" m
        else okStr m (String.join (List.replicate n.toNat s))
      | _, _ => .unsupported "String#*"
  | "String#==" | "String#eql?" =>
    binArg m args fun b =>
      match strPayload? h recv, strPayload? h b with
      | some s, some t => .ok (.bool (s == t)) m
      | _, _ => .ok (.bool false) m
  | "String#!=" =>
    binArg m args fun b => .ok (.bool (!(valueEq h recv b))) m
  | "String#<" | "String#>" | "String#<=" | "String#>=" =>
    binArg m args fun b =>
      match strPayload? h recv, strPayload? h b with
      | some s, some t =>
        let o := strCompare s t
        let r := match bid with
          | "String#<" => o == .lt
          | "String#>" => o == .gt
          | "String#<=" => o != .gt
          | _ => o != .lt
        .ok (.bool r) m
      | some _, none =>
        -- Comparable message follows the coerceDesc rule [V]: special
        -- constants by inspect ("with 1", "with :k"), else class name
        -- ("with Array")
        .err Boot.argumentErrorId
          s!"comparison of String with {coerceDesc h b} failed" m
      | _, _ => .unsupported "String comparison"
  | "String#<=>" =>
    binArg m args fun b =>
      match strPayload? h recv, strPayload? h b with
      | some s, some t => .ok (ordValue (strCompare s t)) m
      | _, _ => .ok .nil m
  | "String#length" | "String#size" =>
    match strPayload? h recv with
    | some s => .ok (.int s.length) m  -- character count (UTF-8-aware) [D]
    | none => .unsupported "length"
  | "String#to_s" | "String#to_str" => .ok recv m
  | "String#inspect" =>
    match strPayload? h recv with
    | some s => okStr m (escapeString s)
    | none => .unsupported "inspect"
  | "String#<<" | "String#concat" =>
    binArg m args fun b =>
      match recv, strPayload? h recv, strPayload? h b with
      | .ref o, some s, some t =>
        if (h.get o).frozen then
          match inspectP m recv with
          | .ok r => .err Boot.frozenErrorId s!"can't modify frozen String: {r}" m
          | .error e => .unsupported e
        else
          .ok recv { m with heap := h.set o { h.get o with payload := .str (s ++ t) } }
      | _, some _, none => .unsupported "String#<< non-string (codepoint append)"
      | _, _, _ => .unsupported "<<"
  | "String#empty?" =>
    match strPayload? h recv with
    | some s => .ok (.bool s.isEmpty) m
    | none => .unsupported "empty?"
  | "String#include?" =>
    binArg m args fun b =>
      match strPayload? h recv, strPayload? h b with
      | some s, some t => .ok (.bool (t.isEmpty || (s.splitOn t).length > 1)) m
      | some _, none => .err Boot.typeErrorId
          s!"no implicit conversion of {coerceName h b} into String" m
      | _, _ => .unsupported "include?"
  | "String#reverse" =>
    match strPayload? h recv with
    | some s => okStr m (String.ofList s.toList.reverse)
    | none => .unsupported "reverse"
  | "String#upcase" =>
    match strPayload? h recv with
    | some s => okStr m s.toUpper
    | none => .unsupported "upcase"
  | "String#downcase" =>
    match strPayload? h recv with
    | some s => okStr m s.toLower
    | none => .unsupported "downcase"
  | "String#strip" =>
    match strPayload? h recv with
    | some s => okStr m s.trimAscii.toString
    | none => .unsupported "strip"
  | "String#chomp" =>
    match strPayload? h recv, args with
    | some s, [] =>
      let s := if s.endsWith "\r\n" then (s.dropEnd 2).toString
               else if s.endsWith "\n" || s.endsWith "\r" then (s.dropEnd 1).toString
               else s
      okStr m s
    | _, _ => .unsupported "chomp with arg"
  | "String#start_with?" =>
    binArg m args fun b =>
      match strPayload? h recv, strPayload? h b with
      | some s, some t => .ok (.bool (s.startsWith t)) m
      | _, _ => .unsupported "start_with?"
  | "String#end_with?" =>
    binArg m args fun b =>
      match strPayload? h recv, strPayload? h b with
      | some s, some t => .ok (.bool (s.endsWith t)) m
      | _, _ => .unsupported "end_with?"
  | "String#frozen?" =>
    match recv with
    | .ref o => .ok (.bool (h.get o).frozen) m
    | _ => .unsupported "frozen?"
  | "String#+@" =>
    -- `+str`: an unfrozen String. CRuby 4.0.5 returns a *fresh* object even when
    -- the receiver is already unfrozen (`(+a).equal?(a)` is false [V], unlike what
    -- the 3.x docs describe), so always copy.
    match recv with
    | .ref o => let (v, m) := dupObj m o false; .ok v m
    | _ => .unsupported "+@ on a non-String"
  | "String#-@" =>
    -- `-str`: a frozen (deduplicated) string; sharing is unobservable here [V]
    match recv with
    | .ref o =>
      if (h.get o).frozen then .ok recv m
      else
        let (v, m) := dupObj m o false
        match v with
        | .ref o2 =>
          .ok v { m with heap := m.heap.set o2 { m.heap.get o2 with frozen := true } }
        | _ => .unsupported "-@"
    | _ => .unsupported "-@ on a non-String"
  | "String#to_sym" =>
    match strPayload? h recv with
    | some s => .ok (.sym s) m
    | none => .unsupported "to_sym"
  | "String#[]" =>
    match strPayload? h recv, args with
    | some s, [.int i] =>
      let cs := s.toList
      let idx := if i < 0 then i + cs.length else i
      if idx < 0 || idx ≥ cs.length then .ok .nil m
      else okStr m (String.singleton cs[idx.toNat]!)
    | some str, [.int start, .int len] =>
      let cs := str.toList
      match sliceRange cs.length start len with
      | none => .ok .nil m
      | some (off, count) => okStr m (String.ofList ((cs.drop off).take count))
    | some str, [.ref ro] =>
      match (h.get ro).payload with
      | .range lo hi excl =>
        let cs := str.toList
        let n : Int := cs.length
        let st? : Option Int := match lo with
          | .nil => some 0
          | .int i => some (if i < 0 then i + n else i)
          | _ => none
        let last? : Option Int := match hi with
          | .nil => some (n - 1)
          | .int i => let e := if i < 0 then i + n else i; some (if excl then e - 1 else e)
          | _ => none
        match st?, last? with
        | some st, some lastRaw =>
          if st < 0 || st > n then .ok .nil m
          else
            let lastI := min lastRaw (n - 1)
            let count := if lastI < st then 0 else (lastI - st + 1).toNat
            okStr m (String.ofList ((cs.drop st.toNat).take count))
        | _, _ => .unsupported "String#[] non-Integer range endpoint"
      -- `s["sub"]` → the substring if present, else nil [V]
      | .str sub =>
        if sub.isEmpty || (str.splitOn sub).length > 1 then okStr m sub else .ok .nil m
      | _ => .unsupported "String#[] non-index argument"
    | some _, _ => .unsupported "String#[] index form"
    | _, _ => .unsupported "[]"
  /- ─── Symbol ─── -/
  | "Symbol#to_s" =>
    match recv with | .sym s => okStr m s | _ => .unsupported "to_s"
  | "Symbol#inspect" =>
    match recv with | .sym s => okStr m (symInspect s) | _ => .unsupported "inspect"
  | "Symbol#==" =>
    binArg m args fun b => .ok (.bool (recv.identEq b)) m
  | "Symbol#to_sym" => .ok recv m
  | "Symbol#to_proc" =>
    match recv with
    | .sym s =>
      -- `:m.to_proc` ≈ `->(x, *a){ x.m(*a) }` — lambda-like (no auto-splat).
      let cl : Closure :=
        { params := [.req "__recv", .rest (some "__rest")], locals := [],
          body := .send (some (.var .lvar "__recv")) s
                    [.splat (some (.var .lvar "__rest"))] none,
          captured := 0, home := 0, lam := true }
      let (o, h) := m.heap.alloc { klass := Boot.procId, payload := .proc cl }
      .ok (.ref o) { m with heap := h }
    | _ => .unsupported "to_proc"
  /- ─── Proc ─── -/
  | "Proc#lambda?" =>
    match recv with
    | .ref o => match (h.get o).payload with
      | .proc c => .ok (.bool c.lam) m
      | _ => .unsupported "lambda?"
    | _ => .unsupported "lambda?"
  | "Proc#to_proc" => .ok recv m
  /- ─── Array ─── -/
  | "Array#==" | "Array#eql?" =>
    binArg m args fun b =>
      match arrPayload? h recv, arrPayload? h b with
      | some _, some _ =>
        .ok (.bool (if bid == "Array#eql?" then valueEql h recv b else valueEq h recv b)) m
      | _, _ => .ok (.bool false) m
  | "Array#!=" =>
    binArg m args fun b => .ok (.bool (!(valueEq h recv b))) m
  | "Array#[]" =>
    match arrPayload? h recv, args with
    | some xs, [.int i] =>
      let idx := if i < 0 then i + xs.size else i
      if idx < 0 || idx ≥ xs.size then .ok .nil m
      else .ok xs[idx.toNat]! m
    | some xs, [.ref ro] =>
      match (h.get ro).payload with
      | .range lo hi excl =>
        -- Array slice by Range: normalize endpoints (nil begin → 0, nil end → to
        -- last; negative → +size), then take start..(excl ? end-1 : end).
        let n : Int := xs.size
        let startI? : Option Int := match lo with
          | .nil => some 0
          | .int i => some (if i < 0 then i + n else i)
          | _ => none
        match startI? with
        | none => .unsupported "Array#[] range non-int begin"
        | some s =>
          if s < 0 || s > n then .ok .nil m
          else
            let lastI? : Option Int := match hi with
              | .nil => some (n - 1)
              | .int i => let e := if i < 0 then i + n else i; some (if excl then e - 1 else e)
              | _ => none
            match lastI? with
            | none => .unsupported "Array#[] range non-int end"
            | some lastRaw =>
              let lastI := min lastRaw (n - 1)
              if lastI < s then let (v, m) := allocArr m #[]; .ok v m
              else
                let sub := ((xs.toList.drop s.toNat).take (lastI.toNat - s.toNat + 1)).toArray
                let (v, m) := allocArr m sub; .ok v m
      | _ => .unsupported "Array#[] non-int index"
    | some xs, [.int start, .int len] =>
      match sliceRange xs.size start len with
      | none => .ok .nil m
      | some (off, count) =>
        let (v, m) := allocArr m ((xs.toList.drop off).take count).toArray
        .ok v m
    | some _, _ => .unsupported "Array#[] index form"
    | _, _ => .unsupported "[]"
  | "Array#[]=" =>
    match recv, arrPayload? h recv, args with
    | .ref o, some xs, [.int i, v] =>
      if (h.get o).frozen then frozenErr m recv "Array"
      else
        let idx := if i < 0 then i + xs.size else i
        if idx < 0 then
          .err Boot.indexErrorId
            s!"index {i} too small for array; minimum: -{xs.size}" m
        else
          let xs := if idx.toNat ≥ xs.size
            then (xs ++ Array.replicate (idx.toNat - xs.size + 1) Value.nil).set! idx.toNat v
            else xs.set! idx.toNat v
          .ok v { m with heap := h.set o { h.get o with payload := .arr xs } }
    | _, some _, _ => .unsupported "Array#[]= non-int index"
    | _, _, _ => .unsupported "[]="
  | "Array#<<" | "Array#push" =>
    match recv, arrPayload? h recv with
    | .ref o, some xs =>
      if (h.get o).frozen then frozenErr m recv "Array"
      else
        match bid, args with
        | "Array#<<", [v] =>
          .ok recv { m with heap := h.set o { h.get o with payload := .arr (xs.push v) } }
        | "Array#push", _ =>
          .ok recv { m with heap := h.set o { h.get o with payload := .arr (xs ++ args.toArray) } }
        | _, _ => .unsupported "<</arity"
    | _, _ => .unsupported "<<"
  | "Array#pop" =>
    match recv, arrPayload? h recv, args with
    | .ref o, some xs, [] =>
      if (h.get o).frozen then frozenErr m recv "Array"
      else if xs.isEmpty then .ok .nil m
      else .ok xs.back! { m with heap := h.set o { h.get o with payload := .arr xs.pop } }
    | _, _, _ => .unsupported "pop with arg"
  | "Array#shift" =>
    match recv, arrPayload? h recv, args with
    | .ref o, some xs, [] =>
      if (h.get o).frozen then frozenErr m recv "Array"
      else if xs.isEmpty then .ok .nil m
      else .ok xs[0]! { m with heap := h.set o { h.get o with payload := .arr (xs.extract 1 xs.size) } }
    | _, _, _ => .unsupported "shift with arg"
  | "Array#unshift" =>
    match recv, arrPayload? h recv with
    | .ref o, some xs =>
      if (h.get o).frozen then frozenErr m recv "Array"
      else .ok recv { m with heap := h.set o { h.get o with payload := .arr (args.toArray ++ xs) } }
    | _, _ => .unsupported "unshift"
  | "Array#length" | "Array#size" =>
    match arrPayload? h recv with
    | some xs => .ok (.int xs.size) m
    | none => .unsupported "length"
  | "Array#first" =>
    match arrPayload? h recv, args with
    | some xs, [] => .ok (xs[0]?.getD .nil) m
    | _, _ => .unsupported "first(n)"
  | "Array#last" =>
    match arrPayload? h recv, args with
    | some xs, [] => .ok (xs.back?.getD .nil) m
    | _, _ => .unsupported "last(n)"
  | "Array#empty?" =>
    match arrPayload? h recv with
    | some xs => .ok (.bool xs.isEmpty) m
    | none => .unsupported "empty?"
  | "Array#include?" =>
    binArg m args fun b =>
      match arrPayload? h recv with
      | some xs =>
        if hasUserEq h b || xs.any (hasUserEq h) then
          .unsupported "Array#include? with a user-defined =="
        else .ok (.bool (xs.any (valueEq h · b))) m
      | none => .unsupported "include?"
  | "Array#index" =>
    binArg m args fun b =>
      match arrPayload? h recv with
      | some xs =>
        if hasUserEq h b || xs.any (hasUserEq h) then
          .unsupported "Array#index with a user-defined =="
        else match xs.toList.findIdx? (valueEq h · b) with
        | some i => .ok (.int i) m
        | none => .ok .nil m
      | none => .unsupported "index"
  | "Array#+" =>
    binArg m args fun b =>
      match arrPayload? h recv, arrPayload? h b with
      | some xs, some ys => let (v, m) := allocArr m (xs ++ ys); .ok v m
      | some _, none => .err Boot.typeErrorId
          s!"no implicit conversion of {coerceName h b} into Array" m
      | _, _ => .unsupported "+"
  | "Array#-" =>
    binArg m args fun b =>
      match arrPayload? h recv, arrPayload? h b with
      | some xs, some ys =>
        let (v, m) := allocArr m (xs.filter (fun x => !(ys.any (valueEql h x ·))))
        .ok v m
      | _, _ => .unsupported "-"
  | "Array#*" =>
    binArg m args fun b =>
      match arrPayload? h recv, b with
      | some xs, .int n =>
        if n < 0 then .err Boot.argumentErrorId "negative argument" m
        else
          let (v, m) := allocArr m ((List.replicate n.toNat xs).foldl (· ++ ·) #[])
          .ok v m
      | some _, _ => .unsupported "Array#* join form"
      | _, _ => .unsupported "*"
  | "Array#concat" =>
    match recv, arrPayload? h recv, args with
    | .ref o, some xs, [b] =>
      match arrPayload? h b with
      | some ys =>
        if (h.get o).frozen then frozenErr m recv "Array"
        else .ok recv { m with heap := h.set o { h.get o with payload := .arr (xs ++ ys) } }
      | none => .err Boot.typeErrorId
          s!"no implicit conversion of {coerceName h b} into Array" m
    | _, _, _ => .unsupported "concat"
  | "Array#inspect" | "Array#to_s" =>
    match inspectP m recv with
    | .ok s => okStr m s
    | .error e => .unsupported e
  | "Array#to_a" => .ok recv m
  | "Array#reverse" =>
    match arrPayload? h recv with
    | some xs => let (v, m) := allocArr m xs.reverse; .ok v m
    | none => .unsupported "reverse"
  | "Array#join" => joinImpl m recv args
  | "Array#flatten" =>
    match arrPayload? h recv, args with
    | some _, [] =>
      match flattenAll m recv 100 with
      | some vs => let (v, m) := allocArr m vs.toArray; .ok v m
      | none => .unsupported "flatten depth"
    | _, _ => .unsupported "flatten(n)"
  | "Array#compact" =>
    match arrPayload? h recv with
    | some xs =>
      let (v, m) := allocArr m (xs.filter (fun x => match x with | .nil => false | _ => true))
      .ok v m
    | none => .unsupported "compact"
  | "Array#uniq" =>
    match arrPayload? h recv, args with
    | some xs, [] =>
      let ys := xs.foldl (init := #[]) fun acc x =>
        if acc.any (valueEql h x ·) then acc else acc.push x
      let (v, m) := allocArr m ys
      .ok v m
    | _, _ => .unsupported "uniq"
  | "Array#frozen?" =>
    match recv with
    | .ref o => .ok (.bool (h.get o).frozen) m
    | _ => .unsupported "frozen?"
  | "Array#sort" => sortImpl m recv
  | "Array#min" | "Array#max" =>
    match arrPayload? h recv, args with
    | some xs, [] =>
      if xs.isEmpty then .ok .nil m
      else
        match sortKey? h xs with
        | some keyed =>
          let sorted := keyed.toList.mergeSort (fun a b => leKey a.1 b.1)
          .ok (if bid == "Array#min" then sorted.head!.2 else sorted.getLast!.2) m
        | none => .unsupported "min/max needs <=> dispatch"
    | _, _ => .unsupported "min/max with arg"
  | "Array#sum" =>
    match arrPayload? h recv, args with
    | some xs, [] =>
      let step := fun (acc : Option Num) (x : Value) =>
        match acc, num? x with
        | some (.i a), some (.i b) => some (Num.i (a + b))
        | some (.i a), some (.f b) => some (Num.f (Float.ofInt a + b))
        | some (.f a), some (.i b) => some (Num.f (a + Float.ofInt b))
        | some (.f a), some (.f b) => some (Num.f (a + b))
        | _, _ => none
      match xs.foldl step (some (Num.i 0)) with
      | some n => .ok n.value m
      | none => .unsupported "sum of non-numerics"
    | _, _ => .unsupported "sum with arg"
  /- ─── Hash ─── -/
  | "Hash#==" =>
    binArg m args fun b =>
      match recv, b with
      | .ref _, .ref _ => .ok (.bool (valueEq h recv b)) m
      | _, _ => .ok (.bool false) m
  | "Hash#[]" =>
    binArg m args fun b =>
      match recv with
      | .ref o =>
        match (h.get o).payload with
        | .hsh xs =>
          match xs.find? (fun (k, _) => valueEql h k b) with
          | some (_, v) => .ok v m
          | none =>
            -- Miss: consult the hash's default. A static `val` is returned as-is;
            -- a `prc` default_proc must call a closure (push a frame), which a pure
            -- builtin cannot do — it is intercepted in `invoke` (L42), so reaching
            -- it here means the interception missed → gate rather than answer wrong.
            match (h.get o).hashDflt with
            | some (.val d) => .ok d m
            | some (.prc _) => .unsupported "Hash#[] default_proc"
            | none => .ok .nil m
        | _ => .unsupported "[]"
      | _ => .unsupported "[]"
  | "Hash#[]=" =>
    match recv, args with
    | .ref o, [k, v] =>
      match (h.get o).payload with
      | .hsh xs =>
        if (h.get o).frozen then frozenErr m recv "Hash"
        else
          let xs := match xs.toList.findIdx? (fun (k', _) => valueEql h k' k) with
            | some i => xs.set! i (xs[i]!.1, v)
            | none => xs.push (k, v)
          .ok v { m with heap := h.set o { h.get o with payload := .hsh xs } }
      | _ => .unsupported "[]="
    -- Arity is checked before the receiver's payload (CRuby's `[]=` is a C
    -- function of arity 2, so the check precedes any element handling). Dispatch
    -- has already resolved `Hash#[]=`, so the receiver is a Hash: a wrong arity
    -- is an `ArgumentError`, not an unmodeled case. This matters beyond fidelity
    -- — ArgumentError is in `typeErrorFamily`, so gating here made a *reachable
    -- type-stuck outcome* invisible to the checker (druby-reproduction-plan.md
    -- §4; the hashslice call site `h['a','b'] = 3, 4` is exactly this shape).
    | _, _ => .err Boot.argumentErrorId
        s!"wrong number of arguments (given {args.length}, expected 2)" m
  | "Hash#length" | "Hash#size" =>
    match hshPayload? h recv with
    | some xs => .ok (.int xs.size) m
    | none => .unsupported "size"
  | "Hash#empty?" =>
    match hshPayload? h recv with
    | some xs => .ok (.bool xs.isEmpty) m
    | none => .unsupported "empty?"
  | "Hash#key?" | "Hash#has_key?" | "Hash#include?" | "Hash#member?" =>
    binArg m args fun b =>
      match hshPayload? h recv with
      | some xs => .ok (.bool (xs.any (fun (k, _) => valueEql h k b))) m
      | none => .unsupported "key?"
  | "Hash#keys" =>
    match hshPayload? h recv with
    | some xs => let (v, m) := allocArr m (xs.map (·.1)); .ok v m
    | none => .unsupported "keys"
  | "Hash#values" =>
    match hshPayload? h recv with
    | some xs => let (v, m) := allocArr m (xs.map (·.2)); .ok v m
    | none => .unsupported "values"
  | "Hash#delete" =>
    match recv, args with
    | .ref o, [k] =>
      match (h.get o).payload with
      | .hsh xs =>
        if (h.get o).frozen then frozenErr m recv "Hash"
        else
          match xs.find? (fun (k', _) => valueEql h k' k) with
          | some (_, v) =>
            let xs := xs.filter (fun (k', _) => !(valueEql h k' k))
            .ok v { m with heap := h.set o { h.get o with payload := .hsh xs } }
          | none => .ok .nil m
      | _ => .unsupported "delete"
    | _, _ => .unsupported "delete/arity"
  | "Hash#fetch" =>
    match hshPayload? h recv, args with
    | some xs, [k] =>
      match xs.find? (fun (k', _) => valueEql h k' k) with
      | some (_, v) => .ok v m
      | none =>
        match inspectP m k with
        | .ok ki => .err Boot.keyErrorId s!"key not found: {ki}" m
        | .error e => .unsupported e
    | some xs, [k, dflt] =>
      match xs.find? (fun (k', _) => valueEql h k' k) with
      | some (_, v) => .ok v m
      | none => .ok dflt m
    | _, _ => .unsupported "fetch"
  | "Hash#inspect" | "Hash#to_s" =>
    match inspectP m recv with
    | .ok s => okStr m s
    | .error e => .unsupported e
  | "Hash#merge" =>
    -- Non-mutating merge: start from self's entries, fold each Hash arg in with
    -- later keys overriding — an existing key keeps its position but takes the
    -- new value, a new key is appended (CRuby's order semantics, mirroring the
    -- `Hash#[]=` update-or-append above). The conflict-resolution *block* form is
    -- not modeled (a pure builtin sees no block; cf. `Hash#fetch`), and a non-Hash
    -- argument gates rather than risk a wrong `TypeError` message.
    match hshPayload? h recv with
    | none => .unsupported "merge"
    | some base =>
      if args.all (fun a => (hshPayload? h a).isSome) then
        let acc := args.foldl (init := base) fun cur a =>
          match hshPayload? h a with
          | none => cur                       -- unreachable given the `all` guard
          | some other =>
            other.foldl (init := cur) fun cur (k, v) =>
              match cur.toList.findIdx? (fun (k', _) => valueEql h k' k) with
              | some i => cur.set! i (k, v)
              | none => cur.push (k, v)
        let (v, m) := allocHsh m acc; .ok v m
      else .unsupported "merge: non-Hash arg"
  /- ─── Exception ─── -/
  | "Exception#message" | "Exception#to_s" =>
    match recv with
    | .ref o => match (h.get o).payload with
      | .exc msg => okStr m msg
      | _ => .unsupported "message"
    | _ => .unsupported "message"
  | "Exception#inspect" =>
    match inspectP m recv with
    | .ok s => okStr m s
    | .error e => .unsupported e
  /- ─── Module / Class ─── -/
  | "Module#===" =>
    binArg m args fun b =>
      match recv with
      | .ref k =>
        if (h.classPayload? k).isSome then .ok (.bool (isA h b k)) m
        else .unsupported "==="
      | _ => .unsupported "==="
  | "Module#name" | "Module#to_s" | "Module#inspect" =>
    match recv with
    | .ref k =>
      match h.classPayload? k with
      | some c =>
        if c.name.isEmpty then
          -- anonymous (`Class.new`): `name` is nil, `to_s`/`inspect` show the
          -- address form (L72)
          if bid == "Module#name" then .ok .nil m
          else match inspectP m recv with
            | .ok r => okStr m r
            | .error e => .unsupported e
        else okStr m c.name
      | none => .unsupported "name"
    | _ => .unsupported "name"
  | "Module#==" =>
    binArg m args fun b => .ok (.bool (recv.identEq b)) m
  | "Module#ancestors" =>
    match recv with
    | .ref k =>
      if (h.classPayload? k).isSome then
        let (v, m) := allocArr m ((ancestors h k).map Value.ref).toArray
        .ok v m
      else .unsupported "ancestors"
    | _ => .unsupported "ancestors"
  | "Object#initialize" => .ok .nil m
  | "String#initialize" | "Array#initialize" | "Hash#initialize"
  | "Exception#initialize" =>
    -- Core initializers *mutate* the (already allocated) receiver, so a subclass's
    -- `initialize` can `super` into them (L70). Reached only via `super` or the
    -- allocate-then-initialize path; a plain `String.new` goes through `newImpl`.
    match recv with
    | .ref o =>
      let setP := fun (pl : Payload) =>
        BRes.ok .nil { m with heap := m.heap.set o { m.heap.get o with payload := pl } }
      if bid == "String#initialize" then
        match args with
        | [] => setP (.str "")
        | [sv] => match strPayload? h sv with
          | some str => setP (.str str)
          | none => .unsupported "String#initialize with a non-String argument"
        | _ => .unsupported "String#initialize arity"
      else if bid == "Array#initialize" then
        match args with
        | [] => setP (.arr #[])
        | [.int n] =>
          if n < 0 then .err Boot.argumentErrorId "negative array size" m
          else setP (.arr (Array.replicate n.toNat .nil))
        | [.int n, dflt] =>
          if n < 0 then .err Boot.argumentErrorId "negative array size" m
          else setP (.arr (Array.replicate n.toNat dflt))
        | _ => .unsupported "Array#initialize arity"
      else if bid == "Hash#initialize" then
        match args with
        | [] => setP (.hsh #[])
        | [dflt] =>
          let obj := { m.heap.get o with payload := .hsh #[], hashDflt := some (.val dflt) }
          .ok .nil { m with heap := m.heap.set o obj }
        | _ => .unsupported "Hash#initialize arity"
      else
        match args with
        | [] => setP (.exc (className h (h.get o).klass))
        | [msgV] => match toSP m msgV with
          | .ok str => setP (.exc str)
          | .error e => .unsupported e
        | _ => .unsupported "Exception#initialize arity"
    | _ => .unsupported "initialize on a non-object"
  | "Class#new" => newImpl m recv args
  | _ => .unsupported s!"builtin {bid}"
where
  owner (bid : String) : String :=
    (bid.splitOn "#").headD "Object"
  binArg (m : Machine) (args : List Value) (k : Value → BRes) : BRes :=
    match args with
    | [b] => k b
    | _ => .err Boot.argumentErrorId
        s!"wrong number of arguments (given {args.length}, expected 1)" m
  hshPayload? (h : Heap) : Value → Option (Array (Value × Value))
    | .ref o => match (h.get o).payload with
      | .hsh xs => some xs
      | _ => none
    | _ => none
  frozenErr (m : Machine) (recv : Value) (cls : String) : BRes :=
    match inspectP m recv with
    | .ok r => .err Boot.frozenErrorId s!"can't modify frozen {cls}: {r}" m
    | .error e => .unsupported e
  /-- puts: no args → newline; array → recursive per element; string keeps
      an existing trailing newline; nil → blank line; else to_s [V]. -/
  putsImpl (m : Machine) (args : List Value) : BRes :=
    match putsGo m args 100 with
    | some m => .ok .nil { m with out := if args.isEmpty then m.out ++ "\n" else m.out }
    | none => .unsupported "puts: impure to_s, to_ary dispatch, or deep nesting"
  putsGo (m : Machine) (args : List Value) : Nat → Option Machine
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
  raiseImpl (m : Machine) (args : List Value) : BRes :=
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
  raiseClass (m : Machine) (cls : ObjId) (msg : Option Value) : BRes :=
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
  newImpl (m : Machine) (recv : Value) (args : List Value) : BRes :=
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
  joinImpl (m : Machine) (recv : Value) (args : List Value) : BRes :=
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
  flattenAll (m : Machine) (v : Value) : Nat → Option (List Value)
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
  sortKey? (h : Heap) (xs : Array Value) : Option (Array (SortKey × Value)) :=
    xs.mapM fun v =>
      match v with
      | .int n => some (SortKey.num (Float.ofInt n), v)   -- mixed int/float sorts numerically [V]
      | .flt x => some (SortKey.num x, v)
      | _ => match strPayload? h v with
        | some s => some (SortKey.str s, v)
        | none => none
  leKey : SortKey → SortKey → Bool
    | .num a, .num b => a ≤ b
    | .str a, .str b => a ≤ b
    | .num _, .str _ => true
    | .str _, .num _ => false
  sortImpl (m : Machine) (recv : Value) : BRes :=
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
