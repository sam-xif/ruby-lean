import RubyCore.Heap

/-! Exact fractions shared by literal evaluation, arithmetic and representation.
    No Ruby methods or constants are consulted by these native operations. -/
namespace RubyCore

def rationalPayload? (h : Heap) : Value → Option (Int × Nat)
  | .ref o => match (h.get o).payload with
    | .rational n d => some (n, d)
    | _ => none
  | _ => none

def exactFraction? (h : Heap) : Value → Option (Int × Nat)
  | .int n => some (n, 1)
  | v => rationalPayload? h v

/-- Callers reject zero denominators before allocation. A denominator of one
    still produces a Rational, never an Integer. -/
def Heap.allocRational (h : Heap) (num : Int) (den : Nat) : Value × Heap :=
  let g := num.natAbs.gcd den
  let (o, h) := h.alloc
    { klass := Boot.rationalId, frozen := true,
      payload := .rational (num / Int.ofNat g) (den / g) }
  (.ref o, h)

/-- Exact binary expansion of a finite Float, before fraction reduction. -/
def floatFraction? (x : Float) : Option (Int × Nat) :=
  if x.isNaN || x.isInf then none else
  let bits := x.toBits
  let exp := ((bits >>> 52) &&& 0x7ff).toNat
  let mant := (bits &&& 0xfffffffffffff).toNat + (if exp == 0 then 0 else 2^52)
  let e : Int := if exp == 0 then -1074 else (exp : Int) - 1075
  let n := if e ≥ 0 then mant <<< e.toNat else mant
  some ((if bits >>> 63 == 1 then -(n : Int) else n),
        if e ≥ 0 then 1 else 2^(-e).toNat)

/-- Correctly rounded binary64, computed with an exact quotient and remainder.
    This also handles fractions whose numerator and denominator separately
    overflow Float, ties to even, subnormals and overflow at the top binade. -/
def exactFractionFloat (num : Int) (den : Nat) : Float :=
  let sign : UInt64 := if num < 0 then 0x8000000000000000 else 0
  if num == 0 then Float.ofBits sign else
  let n := num.natAbs
  let e0 := (n.log2 : Int) - (den.log2 : Int)
  let below := if e0 ≥ 0 then n < den <<< e0.toNat else n <<< (-e0).toNat < den
  let e := if below then e0 - 1 else e0
  if e > 1023 then Float.ofBits (sign ||| 0x7ff0000000000000)
  else if e < -1075 then Float.ofBits sign
  else
    let shift := if e < -1022 then 1074 else 52 - e
    let (a, b) := if shift ≥ 0 then (n <<< shift.toNat, den)
                  else (n, den <<< (-shift).toNat)
    let q := a / b
    let rem := a % b
    let q := if rem * 2 > b || (rem * 2 == b && q % 2 == 1) then q + 1 else q
    let bits := if e < -1022 then q
      else if q == 2^53 then (e + 1024).toNat * 2^52
      else (e + 1023).toNat * 2^52 + (q - 2^52)
    Float.ofBits (sign ||| UInt64.ofNat bits)

/-- CRuby's 64-bit `rb_int_fdiv_double` / `big_fdiv_int`, including its
    intermediate rounding. Rational#to_f is not always the correctly rounded
    exact quotient: a finite Bignum divided by a Fixnum first converts both.
    The large-denominator path keeps 64 denominator bits and 128–160 numerator
    bits, truncates the quotient, converts it, then scales (bignum.c). -/
def fractionFloat (num : Int) (den : Nat) : Float :=
  if num == 0 then 0.0 else
  let smallNum := -(2^62 : Int) ≤ num && num < (2^62 : Int)
  let dx := exactFractionFloat num 1
  if (smallNum && den < 2^53) || (!smallNum && den < 2^62 && !dx.isInf) then
    dx / exactFractionFloat den 1
  else
    let ey := (den.log2 : Int) + 1 - 64
    let y := if ey ≥ 0 then den >>> ey.toNat else den <<< (-ey).toNat
    let ex := (num.natAbs.log2 : Int) + 1 - 128
    let ex := if ex > 32 then ex - 32 else if ex > 0 then 0 else ex
    let x := if ex ≥ 0 then num.fdiv (2^ex.toNat) else num * (2^(-ex).toNat)
    let q := x.tdiv (y : Int)
    let qf := exactFractionFloat q 1
    match floatFraction? qf with
    | none => qf
    | some (a, b) =>
      let scale := ex - ey
      if scale ≥ 0 then exactFractionFloat (a * 2^scale.toNat) b
      else exactFractionFloat a (b <<< (-scale).toNat)

def rationalEq (h : Heap) (n : Int) (d : Nat) (other : Value) : Bool :=
  match other with
  | .flt x => fractionFloat n d == x
  | v => match exactFraction? h v with
    | some (a, b) => n * (b : Int) == a * (d : Int)
    | none => false

end RubyCore
