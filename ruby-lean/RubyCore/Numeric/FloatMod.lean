import RubyCore.Numeric.Rational

/-!
`Float#%` and `Float#divmod`, which share CRuby's `flodivmod` (numeric.c).

The quotient is *not* `(x / y).floor`: that computes the remainder as
`x - y * (x / y).floor`, and every rounding in the middle of that expression
shows up in the answer. `100.0 % 0.1` is the smallest witness — the model
answered `0.0` where CRuby answers `0.09999999999999445` — and the answer is
`-Infinity` when the divisor is denormal (`1.0 % 1e-320`).

CRuby's `flodivmod` is:

```c
if (y == 0.0) rb_num_zerodiv();
mod = (x == 0.0 || (isinf(y) && !isinf(x))) ? x : fmod(x, y);
div = (isinf(x) && !isinf(y)) ? x : (x - mod) / y;
if (modp && divp) div = round(div);          // only `divmod` rounds
if (y * mod < 0) { mod += y; div -= 1.0; }
```

`fmod` is exact (the C standard requires it: the result is always representable),
so it is computed here on the raw bits with bignums — `Float.fmod` is not in
Lean's `Float` — and everything else is the same sequence of double operations
CRuby performs, in the same order. `/` here is IEEE division, so the two agree
bit for bit.
-/

namespace RubyCore

/-- The quiet NaN, from its bits: Lean has no `Float.nan` literal. -/
def nanFloat : Float := Float.ofBits 0x7FF8000000000000

/-- C's `fmod`, exactly: `x - n * y` for the integer `n` nearest zero of `x / y`.
    Both operands are expanded to exact fractions (`floatFraction?`), so the
    remainder is the true one and is rounded to binary64 only once, at the end —
    which is exact, since `fmod` is always representable. The sign of a zero
    remainder is the sign of `x`, as in C. -/
def floatFmod (x y : Float) : Float :=
  if x.isNaN || y.isNaN then nanFloat
  else if x.isInf then nanFloat
  else if y.isInf then x
  else if x == 0.0 then x
  else if y == 0.0 then nanFloat
  else
    match floatFraction? x, floatFraction? y with
    | some (a, da), some (b, db) =>
      -- |x| = a/da, |y| = b/db, so |x| mod |y| = (a*db mod b*da) / (da*db)
      let r := a.natAbs * db % (b.natAbs * da)
      if r == 0 then Float.ofBits (if a < 0 then 0x8000000000000000 else 0)
      else exactFractionFloat (if a < 0 then -(r : Int) else (r : Int)) (da * db)
    | _, _ => nanFloat

/-- CRuby's `flodivmod`: the floored quotient and the divisor-signed remainder.
    `both` is CRuby's `divp != 0` — `divmod` asks for the quotient and rounds it,
    `%` asks only for the remainder and does not. `none` is "the divisor is zero",
    which every caller raises as `ZeroDivisionError` rather than answering. -/
def floDivmod (x y : Float) (both : Bool) : Option (Float × Float) :=
  if y == 0.0 then none
  else
    let mod :=
      -- CRuby tests `isnan(y)` before the ternary, so a NaN divisor is the answer.
      if y.isNaN then y
      else if x == 0.0 || (y.isInf && !x.isInf) then x
      else floatFmod x y
    let div :=
      if x.isInf && !y.isInf then x
      else
        let d := (x - mod) / y
        if both then d.round else d
    -- `%`'s divisor sign rule: the remainder takes the divisor's sign.
    if y * mod < 0 then some (div - 1.0, mod + y) else some (div, mod)

end RubyCore
