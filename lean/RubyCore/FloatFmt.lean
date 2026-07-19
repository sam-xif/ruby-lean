/-
Ruby-faithful `Float#to_s` / `#inspect`: the shortest decimal string that round-
trips to the same IEEE-754 double (David Gay's dtoa mode 0 = the Burger–Dubois
"free-format" Dragon4), wrapped in Ruby's fixed-vs-scientific layout.

`Float.toString` in Lean is fixed 6-digit `%f` (lossy: `5.1`→"5.100000",
`0.1+0.2`→"0.300000"), so this is implemented from scratch on the raw bits via
`Float.toBits` and exact `Nat`/`Int` (bignum) arithmetic. Pure and total-by-fuel;
validated against CRuby over a large random sample (see the journal).

Layout rules, matching CRuby `flo_to_s` (numeric.c), with the digit string
`digs` and `decpt` defined so that value = 0.digs × 10^decpt:
  * decpt in 1..15  → fixed        (DBL_DIG = 15)
  * decpt > 15      → scientific
  * decpt in -3..0  → fixed  (0.00ddd)
  * decpt < -3      → scientific
Ruby always prints a fractional digit (`1.0`, not `1`); scientific exponent is
`decpt-1`, sign-prefixed and zero-padded to ≥2 digits; specials are
`Infinity`/`-Infinity`/`NaN`, and zero is `0.0`/`-0.0`.
-/

namespace RubyCore

/-- Shortest round-tripping decimal digits of a positive finite double.
    `m·2^e` is the exact value; `eqGaps` is false only at a power-of-two boundary
    with a half-width lower gap (`frac==0 && expo>1`), `even` selects boundary
    inclusivity for round-half-to-even. Returns `(digits, decpt)` with
    value = 0.d₁d₂… × 10^decpt (digits nonempty, d₁ ∈ 1..9). -/
partial def dragon4 (m : Nat) (e : Int) (eqGaps even : Bool) : List Nat × Int :=
  -- Setup (Burger–Dubois): R/S is the value, m⁺/m⁻ the half-ulp tolerances.
  let (R0, S0, mp0, mm0) :=
    if e ≥ 0 then
      let be : Nat := 2 ^ e.toNat
      if eqGaps then (m * be * 2, 2, be, be)
      else           (m * be * 4, 4, be * 2, be)
    else
      let se : Nat := 2 ^ (-e).toNat
      if eqGaps then (m * 2, se * 2, 1, 1)
      else           (m * 4, se * 4, 2, 1)
  -- High/low boundary tests (inclusive when the mantissa is even).
  let hiGE (r mp s : Nat) : Bool := if even then r + mp ≥ s else r + mp > s
  let loLE (r mm : Nat) : Bool := if even then r ≤ mm else r < mm
  -- Fixup: scale by powers of ten so the first emitted digit is significant.
  let rec scaleUp (r s mp mm : Nat) (k : Int) (fuel : Nat) : Nat × Nat × Nat × Nat × Int :=
    match fuel with
    | 0 => (r, s, mp, mm, k)
    | fuel+1 => if hiGE r mp s then scaleUp r (s * 10) mp mm (k+1) fuel else (r, s, mp, mm, k)
  let rec scaleDown (r s mp mm : Nat) (k : Int) (fuel : Nat) : Nat × Nat × Nat × Nat × Int :=
    match fuel with
    | 0 => (r, s, mp, mm, k)
    | fuel+1 =>
      if hiGE (r*10) (mp*10) s then (r, s, mp, mm, k)   -- (r+mp)*10 would be ≥ s ⇒ value ≥ 1/10
      else scaleDown (r*10) s (mp*10) (mm*10) (k-1) fuel
  let (R1, S1, mp1, mm1, k) := scaleUp R0 S0 mp0 mm0 0 4096
  let (R, S, mp, mm, decpt) := scaleDown R1 S1 mp1 mm1 k 4096
  -- Digit generation.
  let rec gen (r mp mm : Nat) (acc : List Nat) (fuel : Nat) : List Nat :=
    match fuel with
    | 0 => acc.reverse
    | fuel+1 =>
      let r := r * 10; let mp := mp * 10; let mm := mm * 10
      let d := r / S
      let r := r % S
      let low := loLE r mm
      let high := hiGE r mp S
      if !low && !high then gen r mp mm (d :: acc) fuel
      else
        let dFinal :=
          if low && !high then d
          else if high && !low then d + 1
          else -- both: round to nearest, ties to even
            if 2 * r < S then d
            else if 2 * r > S then d + 1
            else if d % 2 == 0 then d else d + 1
        (dFinal :: acc).reverse
  let digits := gen R mp mm [] 64
  -- A final round-up may carry (…9 → …10); propagate, bumping decpt on overflow.
  let rec carry (ds : List Nat) : List Nat × Bool :=
    match ds with
    | [] => ([], true)                       -- carried off the front: "10…" case
    | d :: rest =>
      let (rest', c) := carry rest
      if c then (if d + 1 == 10 then (0 :: rest', true) else ((d + 1) :: rest', false))
      else (d :: rest', false)
  let hasTen := digits.any (· ≥ 10)
  if hasTen then
    -- Replace the trailing 10 with 0 and carry into the prefix.
    let ds := digits.map (fun d => if d ≥ 10 then 0 else d)
    let (ds', overflow) := carry ds
    if overflow then (1 :: ds', decpt + 1) else (ds', decpt)
  else (digits, decpt)

/-- Assemble Ruby's `flo_to_s` layout from shortest digits + `decpt` + sign. -/
def layoutFloat (neg : Bool) (digits : List Nat) (decpt : Int) : String :=
  let cs : List Char := digits.map (fun d => Char.ofNat (d + '0'.toNat))
  let n := cs.length
  let ofL (l : List Char) : String := String.ofList l
  let sign := if neg then "-" else ""
  let expStr (exp10 : Int) : String :=
    let rest := cs.drop 1
    let mant := ofL (cs.take 1) ++ "." ++ (if rest.isEmpty then "0" else ofL rest)
    let es := if exp10 < 0 then "-" else "+"
    let ea := (if exp10 < 0 then -exp10 else exp10).toNat
    let ed := toString ea
    let ed := if ed.length < 2 then "0" ++ ed else ed
    sign ++ mant ++ "e" ++ es ++ ed
  let fixedPos : String :=   -- decpt > 0
    let dp := decpt.toNat
    if dp ≥ n then
      sign ++ ofL cs ++ ofL (List.replicate (dp - n) '0') ++ ".0"
    else
      sign ++ ofL (cs.take dp) ++ "." ++ ofL (cs.drop dp)
  let fixedNonPos : String :=  -- decpt ≤ 0
    sign ++ "0." ++ ofL (List.replicate (-decpt).toNat '0') ++ ofL cs
  -- Fixed vs scientific (empirically matched to CRuby `flo_to_s`): for decpt > 0,
  -- fixed through decpt 15 and, at decpt 16, only when a real fractional digit
  -- exists (ndigits 17) — i.e. `decpt ≤ max 15 (ndigits-1)`; else scientific.
  -- For decpt ≤ 0, fixed while `decpt > -4` (down to 0.000ddd), else scientific.
  if decpt > 0 then
    if decpt ≤ max (15 : Int) ((n : Int) - 1) then fixedPos else expStr (decpt - 1)
  else
    if decpt > -4 then fixedNonPos else expStr (decpt - 1)

/-- Ruby `Float#to_s` / `#inspect` (identical for floats). -/
def rubyFloatRepr (x : Float) : String :=
  let bits := x.toBits
  let neg := (bits >>> 63) == 1
  let expo := ((bits >>> 52) &&& 0x7FF).toNat
  let frac := (bits &&& 0xFFFFFFFFFFFFF).toNat
  if expo == 0x7FF then
    if frac == 0 then (if neg then "-Infinity" else "Infinity") else "NaN"
  else if expo == 0 && frac == 0 then
    if neg then "-0.0" else "0.0"
  else
    let (m, e) := if expo == 0 then (frac, (-1074 : Int))
                  else (frac + 0x10000000000000, (expo : Int) - 1075)
    let eqGaps := frac ≠ 0 || expo ≤ 1     -- unequal only at a power-of-two boundary
    let even := m % 2 == 0
    let (digits, decpt) := dragon4 m e eqGaps even
    layoutFloat neg digits decpt

end RubyCore
