# L279: signed zero, nonfinite representation/equality, division rounding.
[Complex(-0.0, -0.0), Complex(1, 0.0), Complex(1r, -0.0)].each do |c|
  p [c, c.to_s, c.rect, c.conj, -c]
end
inf = 1.0 / 0.0
nan = 0.0 / 0.0
[Complex(1, inf), Complex(-inf, -inf), Complex(nan, nan)].each do |c|
  p [c, c.to_s, c.finite?, c.infinite?, c == c, c.eql?(c)]
end
c = Complex(nan, 1)
p [c == Complex(nan, 1), c.eql?(Complex(nan, 1))]
p [Complex(1.5, 2.5) / Complex(2.0, 3.0), Complex(1.5, 2.5) / Complex(3.0, 2.0)]
p [Complex(1, 2) / Complex(1e200, 1e199), Complex(1, 2) / 0.0]
