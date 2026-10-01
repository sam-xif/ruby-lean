# L279: exact/floating components, coercion, and quotient canonicalization.
a = Complex(2, 3)
[2, 1.5, 1.2r, Complex(-1, 4), Complex(1.2r, -0.3r), Complex(0.5, 2)].each do |b|
  p [a + b, a - b, a * b, a / b, a.quo(b)]
  p [b + a, b - a, b * a, b / a]
end
p [-a, a.conj, a.conjugate, a.real, a.imag]
p [Complex(4, 2) / 2, Complex(4r, 2r) / 2, Complex(4, 2) / 2r]
p [Complex(1.0, 2) / Complex(1, 0), Complex(1, 2) / Complex(0, 1)]
p [1i == 1.0i, 1i.eql?(1.0i), 1ri == 1i, 1ri.eql?(1i)]
p [Complex(2, 0) == 2, 2 == Complex(2, 0), Complex(2, 0r) == 2.0]
begin
  a / 0
rescue => e
  p [e.class, e.message]
end
begin
  a / 0i
rescue => e
  p [e.class, e.message]
end
