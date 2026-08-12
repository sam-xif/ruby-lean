import RubyCore.Builtins.Strings

/-!
Integer and Float rules.

Split out of the single `Builtins.run` match (L98), one class group per file, no
behaviour change: each rule file matches its own bids and hands anything it does
not recognise to the next file in the chain.
-/

namespace RubyCore

namespace Builtins

/-- Integer and Float rules. -/
def runNumerics (bid : String) (recv : Value) (args : List Value) (m : Machine) : BRes :=
  let h := m.heap
  match bid with
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
  | "Integer#chr" =>
    -- ASCII only: CRuby raises RangeError above 255, and 128..255 produces an
    -- ASCII-8BIT string whose rendering depends on an encoding the model does
    -- not carry, so that half gates rather than guessing [V].
    match recv with
    | .int n =>
      if n < 0 || n > 255 then .err Boot.rangeErrorId s!"{n} out of char range" m
      else if n > 127 then .unsupported "Integer#chr above 127 (encoding)"
      else okStr m (String.singleton (Char.ofNat n.toNat))
    | _ => .unsupported "Integer#chr"
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
  | _ => runStrings bid recv args m

end Builtins

end RubyCore
