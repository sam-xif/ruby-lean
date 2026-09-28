# L278: exact reduction, signs, mixed arithmetic, ordering and identity.
a = Rational(2, 6)
b = Rational(-10, -15)
p [a, b, a + b, a - b, a * b, a / b, a.quo(2)]
p [2 + a, 2 - a, 2 * a, 2 / a, 0.5 + a, a + 0.5]
p [a < b, a <= b, b > a, a <=> b, a <=> :unknown]
p [1r == 1, 1 == 1r, 0.1r == 0.1, 0.1 == 0.1r, 1r.eql?(1)]
p [Rational(2, 4).eql?(0.5r), {0.5r => :found}[Rational(1, 2)]]
p [a ** 3, a ** -2, 2 ** -3, (-2) ** -3]
p [a.numerator, a.denominator, a.to_s, a.inspect, a.to_f]
p [(-1.5r).to_i, (-1.5r).floor, (-1.5r).ceil, (-1.5r).truncate]
p [(-a).abs, a.abs.equal?(a), a.dup.equal?(a), a.clone.equal?(a), a.to_r.equal?(a)]
p [a.positive?, (-a).negative?, Kernel.Rational(4, 6)]
begin
  a / 0
rescue ZeroDivisionError => e
  puts e.message
end
begin
  Rational(1, 0)
rescue ZeroDivisionError => e
  puts e.message
end
