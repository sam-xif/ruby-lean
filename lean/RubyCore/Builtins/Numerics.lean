import RubyCore.Builtins.Strings

/-!
Integer and Float rules.

Split out of the single `Builtins.run` match (L98), one class group per file, no
behaviour change: each rule file matches its own bids and hands anything it does
not recognise to the next file in the chain.
-/

namespace RubyCore

namespace Builtins

/-- Exact truncation toward zero via the IEEE bits (no lossy Float→Int). -/
def floatTruncBits (x : Float) : Int :=
  let bits := x.toBits
  let neg := (bits >>> 63) == 1
  let expo := ((bits >>> 52) &&& 0x7FF).toNat
  let frac := (bits &&& 0xFFFFFFFFFFFFF).toNat
  let (mant, e) := if expo == 0 then (frac, (-1074 : Int))
                   else (frac + 0x10000000000000, (expo : Int) - 1075)
  let intAbs : Nat := if e ≥ 0 then mant <<< e.toNat else mant >>> (-e).toNat
  if neg then -(Int.ofNat intAbs) else Int.ofNat intAbs

/-- `.ok (.int ⌊y⌋)` for an already-integral Float. -/
def floatToInt (m : Machine) (y : Float) : BRes :=
  if y.isNaN || y.isInf then .unsupported "Float→Integer of Infinity/NaN"
  else .ok (.int (floatTruncBits y)) m

/-- `Float#round`/`ceil`/`floor`/`truncate` at `nd` digits, following CRuby's
    `flo_round`. The `round` case is CRuby's `round_half_up`, correction and all:

    ```c
    f = round(x * s);                              // half away from zero
    if (x > 0 && (double)((f + 0.5) / s) <= x) f += 1;
    if (x < 0 && (double)((f - 0.5) / s) >= x) f -= 1;
    ```

    That correction is not decoration — it is why `2.675.round(2)` is `2.68` even
    though `2.675` is really `2.67499999999999982…` in binary, and why
    `1.005.round(2)` is `1.01`. Scaling and rounding without it gives `2.67`
    and `1.0`, which is what a plausible implementation produces and what the
    oracle immediately catches. [V] -/
def roundToDigits (kind : String) (x : Float) (nd : Int) : Float :=
  let s : Float :=
    if nd ≥ 0 then Float.ofNat (10 ^ nd.toNat)
    else 1.0 / Float.ofNat (10 ^ (-nd).toNat)
  let xs := x * s
  let f :=
    if kind == "round" then
      let r := xs.round
      if s == 1.0 then r
      else if x > 0 then (if (r + 0.5) / s ≤ x then r + 1 else r)
      else if x < 0 then (if (r - 0.5) / s ≥ x then r - 1 else r)
      else r
    else if kind == "ceil" then xs.ceil
    else if kind == "floor" then xs.floor
    else Float.ofInt (floatTruncBits xs)      -- truncate
  f / s

/-- One digit of a base-≤36 numeral. Computed rather than indexed out of a digit
    string, so nothing here can panic or block kernel reduction (L73). -/
def baseDigit (d : Nat) : Char :=
  if d < 10 then Char.ofNat ('0'.toNat + d) else Char.ofNat ('a'.toNat + d - 10)

/-- `Integer#to_s(base)` for 2 ≤ base ≤ 36 [V]: `255.to_s(16)` is `"ff"` and
    `-255.to_s(16)` is `"-ff"`. Fuel-bounded rather than `termination_by` (L73): a
    `WellFounded.fix` would not reduce in the kernel, and `mag + 1` is ample since
    every step at least halves the magnitude. -/
def intToBase (n : Int) (base : Nat) : String :=
  let mag := n.natAbs
  let body := if mag == 0 then "0" else String.ofList (go mag (mag + 1)).reverse
  if n < 0 then "-" ++ body else body
where
  go (k : Nat) : Nat → List Char
    | 0 => []
    | fuel + 1 => if k == 0 then [] else baseDigit (k % base) :: go (k / base) fuel

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
    -- `**` coerces like the rest (L123), so a non-numeric argument that answered
    -- nothing gets the coercion TypeError rather than a gate — only a *numeric*
    -- exponent this rule cannot compute (a Float, or a negative giving a
    -- Rational) is unsupported.
    binArg m args fun b =>
      match recv, b with
      | .int x, .int y =>
        if y ≥ 0 then .ok (.int (x ^ y.toNat)) m
        else .unsupported "Integer ** negative (Rational result)"
      | _, _ =>
        if (num? b).isNone then coerceFailed (owner bid) m b
        else .unsupported "** with non-integer"
  | "Float#**" =>
    binArg m args fun b =>
      match recv, num? b with
      | .flt x, some nb =>
        let y := match nb with | .i n => Float.ofInt n | .f v => v
        .ok (.flt (Float.pow x y)) m
      | _, _ =>
        if (num? b).isNone then coerceFailed (owner bid) m b
        else .unsupported "Float#** non-numeric"
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
    -- `Integer#inspect` **is** `int_to_s`, base argument and all [V]. It used to
    -- share this arm but sit in `zeroArgBids` too, so `0.inspect(0)` answered
    -- `wrong number of arguments (given 1, expected 0)` where CRuby says
    -- `invalid radix 0` — found by a tier-1 draw of `each_with_index(&:inspect)`,
    -- which hands the block *two* arguments (L132).
    match recv, args with
    | .int n, [] => okStr m (toString n)
    -- the base goes through `NUM2LONG`, so a Float is **truncated** rather than
    -- refused: `42.to_s(16.5)` is `"2a"` [V]
    | .int n, [bv] =>
      match (match bv with
             | .int b => some b
             | .flt x => if x.isNaN || x.isInf then none else some (floatTruncBits x)
             | _ => none) with
      | none =>
        match bv with
        -- `nil` has its own wording in `rb_to_int`, lowercase and with different
        -- prepositions [V]
        | .nil => .err Boot.typeErrorId "no implicit conversion from nil to integer" m
        -- a non-finite Float is a **RangeError**, not a TypeError [V]
        | .flt x => .err Boot.rangeErrorId
            s!"float {if x.isNaN then "NaN" else "Inf"} out of range of integer" m
        | _ => .err Boot.typeErrorId
            s!"no implicit conversion of {coerceName h bv} into Integer" m
      | some b =>
        if b < 2 || b > 36 then .err Boot.argumentErrorId s!"invalid radix {b}" m
        else okStr m (intToBase n b.toNat)
    | .int _, _ => .err Boot.argumentErrorId
        s!"wrong number of arguments (given {args.length}, expected 0..1)" m
    | _, _ => .unsupported "Integer#to_s on a non-Integer"
  | "Integer#round" | "Integer#ceil" | "Integer#floor" | "Integer#truncate" =>
    -- An Integer rounds to itself for ndigits ≥ 0; a negative count rounds to a
    -- power of ten, and `round` there is half **up** away from zero (`25.round(-1)`
    -- is 30, not 20) while `ceil`/`floor` go their own ways [V].
    match recv, args with
    | .int n, [] => .ok (.int n) m
    | .int n, [.int d] =>
      if d ≥ 0 then .ok (.int n) m
      else
        let p : Int := 10 ^ (-d).toNat
        let q := n / p
        let r := n % p
        let kind := (bid.drop 8).toString
        let adj : Int :=
          if kind == "round" then
            (if r.natAbs * 2 ≥ p.natAbs then (if n ≥ 0 then 1 else -1) else 0)
          else if kind == "ceil" then (if r > 0 then 1 else 0)
          else if kind == "floor" then (if r < 0 then -1 else 0)
          else 0
        .ok (.int ((q + adj) * p)) m
    | _, _ => .unsupported "Integer#round/ceil/floor arity"
  | "Integer#divmod" =>
    binArg m args fun b =>
      match recv, b with
      | .int a, .int c =>
        if c == 0 then .err Boot.zeroDivisionErrorId "divided by 0" m
        else
          let (v, m) := allocArr m #[.int (Int.fdiv a c), .int (Int.fmod a c)]
          .ok v m
      -- coerces like the arithmetic operators (L123)
      | _, _ =>
        if (num? b).isNone then coerceFailed (owner bid) m b
        else .unsupported "Integer#divmod of a Float"
  | "Integer#nonzero?" | "Float#nonzero?" =>
    -- `self` if non-zero, **nil** if zero — the idiom behind
    -- `pkg_version.rb`'s `version_comparison.nonzero? || revision <=> …` [V].
    match recv with
    | .int n => .ok (if n == 0 then .nil else recv) m
    | .flt x => .ok (if x == 0.0 then .nil else recv) m
    | _ => .unsupported "nonzero?"
  | "Integer#chr" =>
    -- CRuby raises RangeError above 255; 128..255 is one byte of an ASCII-8BIT
    -- string [V].
    match recv with
    | .int n =>
      if n < 0 || n > 255 then .err Boot.rangeErrorId s!"{n} out of char range" m
      else if n > 127 then
        -- 128..255 is a single **byte** in an ASCII-8BIT string (L117).
        let (v, m) := allocStrEnc m (String.singleton (Char.ofNat n.toNat)) true
        .ok v m
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
  | "Float#truncate" =>
    match args with
    | [] =>
      match recv with
      | .flt x =>
        if x.isNaN || x.isInf then .unsupported "Float#truncate of Infinity/NaN"
        else .ok (.int (floatTruncBits x)) m
      | _ => .unsupported "Float#truncate"
    | [.int n] =>
      if n > 0 then
        match recv with
        | .flt x => .ok (.flt (roundToDigits "truncate" x n)) m
        | _ => .unsupported "Float#truncate"
      else
        match recv with
        | .flt x => floatToInt m (roundToDigits "truncate" x n)
        | _ => .unsupported "Float#truncate"
    | _ => .unsupported "Float#truncate arity"
  | "Float#to_i" | "Float#to_int" =>
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
  | "Float#round" | "Float#ceil" | "Float#floor" =>
    match recv with
    | .flt x =>
      if x.isNaN || x.isInf then .unsupported "Float#round/ceil/floor of Infinity/NaN"
      else
        let nd : Int := match args with
          | [] => 0
          | [.int n] => n
          | _ => 0
        if args.length > 1 then .unsupported "Float#round/ceil/floor arity"
        else if (match args with | [.int _] => false | [] => false | _ => true) then
          .unsupported "Float#round/ceil/floor with a non-Integer digit count"
        else
          let kind := (bid.drop 6).toString
          let y := roundToDigits kind x nd
          -- ndigits > 0 keeps a Float; 0 or negative yields an Integer [V].
          if nd > 0 then .ok (.flt y) m
          else floatToInt m y
    | _ => .unsupported "Float#round"
  | "Float#divmod" =>
    binArg m args fun b =>
      match recv, b with
      | .flt a, _ =>
        match (match b with | .flt y => some y | .int i => some (Float.ofInt i) | _ => none) with
        | none => coerceFailed (owner bid) m b     -- coerces (L123)
        | some c =>
          if c == 0.0 then .err Boot.zeroDivisionErrorId "divided by 0" m
          else
            -- floored division, so the remainder takes the divisor's sign [V]
            let q := (a / c).floor
            let (v, m) := allocArr m #[.int (floatTruncBits q), .flt (a - q * c)]
            .ok v m
      | _, _ => .unsupported "Float#divmod"
  | "Float#abs" =>
    match recv with | .flt x => .ok (.flt x.abs) m | _ => .unsupported "abs"
  | "Float#zero?" =>
    match recv with | .flt x => .ok (.bool (x == 0.0)) m | _ => .unsupported "zero?"
  | "Float#nan?" =>
    match recv with | .flt x => .ok (.bool x.isNaN) m | _ => .unsupported "nan?"
  | _ => runStrings bid recv args m

end Builtins

end RubyCore
