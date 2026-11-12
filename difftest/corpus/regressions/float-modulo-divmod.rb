# Float#% and Float#divmod are CRuby's `flodivmod`: `fmod` on the operands, then
# the divisor's sign rule — not `x - y * (x/y).floor`, whose intermediate
# roundings move the answer.

# fmod, not a subtraction: the divisor is not representable, so the true
# remainder is not `x - y * q`.
p 1.0 % 0.3
p 100.0 % 0.1
p 5.0 % 0.7
p 100.0.divmod(0.1)
p 5.0.divmod(0.7)
p 1.0.divmod(0.3)

# A denormal or extreme-exponent divisor: the naive form overflowed the product.
p 1.0 % 1e-320
p 1e300 % 1e-300
p 1.0 % 1e-323
p 1e-300 % 1e300

# Signs: the remainder takes the divisor's sign, and a zero remainder keeps the
# receiver's.
p(-1.0 % 0.3)
p(1.0 % -0.3)
p(-1.0 % -0.3)
p(-0.0 % 3.0)
p(0.0 % -3.0)
p(-6.0 % 3.0)
p(-6.0 % -3.0)
p(-1.0.divmod(0.3))
p(1.0.divmod(-0.3))
p(-1.0.divmod(-0.3))
p(-0.0.divmod(3.0))
p(-6.0.divmod(3.0))

# Exact cases, including the quotient's rounding: `divmod` rounds the quotient
# where `%` does not ask for it.
p 7.5 % 2
p(-7.5 % 2)
p 7.5 % -2
p 2.5 % 0.5
p 3.5 % 3.5
p 3.5.divmod(3.5)
p 7.5.divmod(2)
p(-7.5.divmod(2))

# An Integer receiver with a Float argument takes the same path.
p 1 % 0.3
p 100 % 0.1
p(-7 % 2.5)
p(7 % -2.5)

# An infinite divisor: `mod` is the receiver, then the sign rule can pull in the
# divisor itself.
p 5.0 % Float::INFINITY
p(-5.0 % Float::INFINITY)
p 5.0 % -Float::INFINITY
p(-5.0 % -Float::INFINITY)
p 0.0 % Float::INFINITY
p(-0.0 % -Float::INFINITY)
p 5.0.divmod(Float::INFINITY)
p(-5.0.divmod(Float::INFINITY))
p 5.0.divmod(-Float::INFINITY)
p(-5.0.divmod(-Float::INFINITY))

# NaN propagates through the remainder.
p(2.0 % Float::NAN)
p(Float::NAN % 2.0)
p(Float::NAN % Float::NAN)

# A quotient too large for anything but a Bignum.
p 1e300.divmod(3)
p 1e17.divmod(1e-3)

# Dividing by zero is an error, not a gate.
begin
  1.0 % 0
rescue ZeroDivisionError => e
  p [e.class, e.message]
end
begin
  1.0 % -0.0
rescue ZeroDivisionError => e
  p [e.class, e.message]
end
begin
  1 % 0.0
rescue ZeroDivisionError => e
  p [e.class, e.message]
end
begin
  1.0.divmod(0)
rescue ZeroDivisionError => e
  p [e.class, e.message]
end
