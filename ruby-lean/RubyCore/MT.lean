/-
CRuby-compatible Mersenne Twister (MT19937) — enough of `Random` to reproduce
`Random.new(seed).rand` bit-for-bit. Ruby seeds a 32-bit-fitting integer with
`init_genrand(seed)` and a bignum seed with `init_by_array` over its little-endian
32-bit words; `rand` (no arg) draws a 53-bit double via
`(a>>5)*2^26 + (b>>6)) / 2^53` from two 32-bit outputs.

Pure `UInt32`/`Array` (wrapping arithmetic is mod 2^32). Validated against CRuby
reference sequences (see the journal). Only the unseeded-vs-seeded `Random.new`
integer path + `#rand`/`#rand(n)` are needed by the ai4r SOM drivers.
-/

namespace RubyCore.MT

def N : Nat := 624
def M : Nat := 397

/-- MT19937 state: the 624-word vector plus the read index. -/
structure State where
  mt : Array UInt32
  mti : Nat
deriving Inhabited

/-- `init_genrand`: seed the vector from a single 32-bit value. -/
def initGenrand (s : UInt32) : Array UInt32 := Id.run do
  let mut mt := Array.replicate N (0 : UInt32)
  mt := mt.set! 0 s
  for i in [1:N] do
    let prev := mt[i-1]!
    mt := mt.set! i ((1812433253 : UInt32) * (prev ^^^ (prev >>> 30)) + UInt32.ofNat i)
  return mt

/-- `init_by_array`: Ruby's integer-seed initializer over 32-bit key words. -/
def initByArray (key : Array UInt32) : State := Id.run do
  let mut mt := initGenrand 19650218
  let keylen := if key.isEmpty then 1 else key.size
  let key := if key.isEmpty then #[0] else key
  let mut i := 1
  let mut j := 0
  let mut k := max N keylen
  while k > 0 do
    let prev := mt[i-1]!
    mt := mt.set! i ((mt[i]! ^^^ ((prev ^^^ (prev >>> 30)) * 1664525)) + key[j]! + UInt32.ofNat j)
    i := i + 1; j := j + 1
    if i ≥ N then mt := mt.set! 0 (mt[N-1]!); i := 1
    if j ≥ keylen then j := 0
    k := k - 1
  k := N - 1
  while k > 0 do
    let prev := mt[i-1]!
    mt := mt.set! i ((mt[i]! ^^^ ((prev ^^^ (prev >>> 30)) * 1566083941)) - UInt32.ofNat i)
    i := i + 1
    if i ≥ N then mt := mt.set! 0 (mt[N-1]!); i := 1
    k := k - 1
  mt := mt.set! 0 0x80000000
  return { mt, mti := N }

/-- Regenerate the whole vector (the "twist"); the three reference loops collapse
    to one with modular indices for `kk+1` and `kk+M`. -/
def twist (mt : Array UInt32) : Array UInt32 := Id.run do
  let mut mt := mt
  for kk in [0:N] do
    let y := (mt[kk]! &&& 0x80000000) ||| (mt[(kk+1) % N]! &&& 0x7fffffff)
    let mag : UInt32 := if y &&& 1 == 0 then 0 else 0x9908b0df
    mt := mt.set! kk (mt[(kk + M) % N]! ^^^ (y >>> 1) ^^^ mag)
  return mt

/-- `genrand_int32` with tempering; twists when the vector is exhausted. -/
def nextU32 (s : State) : UInt32 × State :=
  let (mt, mti) := if s.mti ≥ N then (twist s.mt, 0) else (s.mt, s.mti)
  let y0 := mt[mti]!
  let y1 := y0 ^^^ (y0 >>> 11)
  let y2 := y1 ^^^ ((y1 <<< 7) &&& 0x9d2c5680)
  let y3 := y2 ^^^ ((y2 <<< 15) &&& 0xefc60000)
  let y4 := y3 ^^^ (y3 >>> 18)
  (y4, { mt, mti := mti + 1 })

/-- `rand` with no argument: a 53-bit double in [0,1), Ruby's `genrand_real`. -/
def nextReal (s : State) : Float × State :=
  let (a0, s) := nextU32 s
  let (b0, s) := nextU32 s
  let a := Float.ofNat (a0 >>> 5).toNat      -- 27 bits
  let b := Float.ofNat (b0 >>> 6).toNat      -- 26 bits
  ((a * 67108864.0 + b) * (1.0 / 9007199254740992.0), s)

/-- Little-endian 32-bit words of a `Nat` seed (at least one word). -/
def seedWords (seed : Nat) : Array UInt32 := Id.run do
  if seed == 0 then return #[0]
  let mut n := seed
  let mut out : Array UInt32 := #[]
  while n > 0 do
    out := out.push (UInt32.ofNat (n % 4294967296))
    n := n / 4294967296
  return out

/-- `Random.new(seed)` for a non-negative integer seed. CRuby uses `init_genrand`
    with the single word for a seed that fits in 32 bits, and `init_by_array` only
    for a multi-word (bignum) seed. -/
def seeded (seed : Nat) : State :=
  let words := seedWords seed
  if words.size ≤ 1 then { mt := initGenrand words[0]!, mti := N }
  else initByArray words

end RubyCore.MT
