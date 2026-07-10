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

/-! ### String ordering (byte order over UTF-8, which Lean's String compare
    matches for the ASCII-ish corpus; non-ASCII edge cases ride on Lean's
    lexicographic Char order = codepoint order = UTF-8 byte order). -/

def strCompare (a b : String) : Ordering := compare a b

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
   "Integer#inspect", "Integer#to_i", "Integer#abs", "Integer#succ",
   "Integer#pred", "Integer#zero?", "Integer#positive?", "Integer#negative?",
   "Integer#even?", "Integer#odd?", "Integer#-@",
   "Float#to_s", "Float#inspect", "Float#-@", "Float#abs", "Float#zero?",
   "Float#nan?", "Float#to_i",
   "String#to_s", "String#to_str", "String#inspect", "String#length",
   "String#size", "String#empty?", "String#reverse", "String#upcase",
   "String#downcase", "String#strip", "String#frozen?", "String#dup",
   "String#to_sym", "String#freeze",
   "Symbol#to_s", "Symbol#inspect", "Symbol#to_sym", "Symbol#to_proc",
   "Array#length", "Array#size", "Array#empty?", "Array#inspect",
   "Array#to_s", "Array#to_a", "Array#reverse", "Array#compact",
   "Array#dup", "Array#frozen?", "Array#freeze", "Array#sort", "Array#uniq",
   "Hash#length", "Hash#size", "Hash#empty?", "Hash#keys", "Hash#values",
   "Hash#inspect", "Hash#to_s", "Hash#dup",
   "Exception#message", "Exception#to_s", "Exception#inspect",
   "Module#name", "Module#to_s", "Module#inspect", "Module#ancestors"]

/-- Run builtin `bid` ("Owner#name"). `implicitSelf` is whether the send had
    no explicit receiver (needed by nothing yet; visibility is deferred). -/
def run (bid : String) (recv : Value) (args : List Value) (m : Machine) : BRes :=
  let h := m.heap
  if zeroArgBids.contains bid && !args.isEmpty then
    .err Boot.argumentErrorId
      s!"wrong number of arguments (given {args.length}, expected 0)" m
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
  | "Object#class" => .ok (.ref (classOf h recv)) m
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
      if (h.classPayload? k).isSome then .ok (.bool (classOf h recv == k)) m
      else .err Boot.typeErrorId "class or module required" m
    | [_] => .err Boot.typeErrorId "class or module required" m
    | _ => .unsupported "instance_of?/arity"
  | "Object#block_given?" => .ok (.bool false) m  -- no blocks in L0
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
  | "Integer#%" =>
    binArg m args fun b =>
      numBin "Integer" m recv b
        (fun x y =>
          if y == 0 then .err Boot.zeroDivisionErrorId "divided by 0" m
          else .ok (.int (Int.fmod x y)) m)  -- sign follows divisor [V]
        (fun _ _ => .unsupported "Float modulo")
  | "Integer#**" =>
    binArg m args fun b =>
      match recv, b with
      | .int x, .int y =>
        if y ≥ 0 then .ok (.int (x ^ y.toNat)) m
        else .unsupported "Integer ** negative (Rational result)"
      | _, _ => .unsupported "** with non-integer"
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
    .unsupported "Float formatting (shortest-roundtrip unimplemented)"
  | "Float#to_i" =>
    match recv with
    | .flt x =>
      if x.isNaN || x.isInf then
        .err Boot.rangeErrorId "float out of range of integer" m  -- FloatDomainError actually; unsupported instead
      else .unsupported "Float#to_i"  -- needs exact trunc; defer
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
  | "String#dup" =>
    match strPayload? h recv with
    | some s => okStr m s
    | none => .unsupported "dup"
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
    | some _, _ => .unsupported "String#[] non-int-index"
    | _, _ => .unsupported "[]"
  /- ─── Symbol ─── -/
  | "Symbol#to_s" =>
    match recv with | .sym s => okStr m s | _ => .unsupported "to_s"
  | "Symbol#inspect" =>
    match recv with | .sym s => okStr m (symInspect s) | _ => .unsupported "inspect"
  | "Symbol#==" =>
    binArg m args fun b => .ok (.bool (recv.identEq b)) m
  | "Symbol#to_sym" => .ok recv m
  | "Symbol#to_proc" => .unsupported "Symbol#to_proc (blocks are L1)"
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
    | some _, [_] => .unsupported "Array#[] non-int index"
    | some _, _ => .unsupported "Array#[] slice"
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
      | some xs => .ok (.bool (xs.any (valueEq h · b))) m
      | none => .unsupported "include?"
  | "Array#index" =>
    binArg m args fun b =>
      match arrPayload? h recv with
      | some xs =>
        match xs.toList.findIdx? (valueEq h · b) with
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
  | "Array#dup" =>
    match arrPayload? h recv with
    | some xs => let (v, m) := allocArr m xs; .ok v m
    | none => .unsupported "dup"
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
    | _, _ => .unsupported "[]=/arity"
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
  | "Hash#dup" =>
    match hshPayload? h recv with
    | some xs => let (v, m) := allocHsh m xs; .ok v m
    | none => .unsupported "dup"
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
      | some c => okStr m c.name
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
    | none => .unsupported "puts: impure to_s or deep nesting"
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
          | _ => match toSP m a with
            | .ok s => some (m.emit (if s.endsWith "\n" then s else s ++ "\n"))
            | .error _ => none
        | _ => match toSP m a with
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
        else if k == Boot.stringId then
          match args with
          | [] => okStr m ""
          | _ => .unsupported "String.new with args"
        else if k == Boot.arrayId then
          match args with
          | [] => let (v, m) := allocArr m #[]; .ok v m
          | _ => .unsupported "Array.new with args"
        else if k == Boot.hashId then
          match args with
          | [] => let (v, m) := allocHsh m #[]; .ok v m
          | _ => .unsupported "Hash.new with args"
        else if [Boot.classId, Boot.moduleId, Boot.integerId, Boot.floatId,
                 Boot.symbolId, Boot.nilClassId, Boot.trueClassId,
                 Boot.falseClassId].contains k then
          .unsupported s!"{className m.heap k}.new"
        else
          -- plain object; `initialize` is a user method → but user classes
          -- are out of the L0 fragment, so only argless Object.new arrives
          match args with
          | [] =>
            let (o, h) := m.heap.alloc { klass := k }
            .ok (.ref o) { m with heap := h }
          | _ => .unsupported "new with args (initialize dispatch is L2)"
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
