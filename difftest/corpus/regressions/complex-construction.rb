# L279: constructors, component identity, immutability and zero normalization.
r = 1.2r
c = Complex(r, -2)
p [c, c.real.equal?(r), c.imag, c.rect, c.rectangular, c.imaginary]
p [Complex(2), Kernel.Complex(2, 3), Complex.rect(2), Complex.rectangular(r, 3)]
p [2.i, 1.5.i, r.i, 2.to_c, 1.5.to_c, r.to_c]
p [c.dup.equal?(c), c.clone.equal?(c), c.to_c.equal?(c), (+c).equal?(c)]
p [c.frozen?, c.real?, c.is_a?(Numeric), Complex.ancestors[0, 2]]
[Complex(1, 0), Complex(1, 0r), Complex(1, 0.0), Complex(1, 2)].each do |a|
  p [Complex(a).equal?(a), Complex(a, 0).equal?(a), Complex(a, 0r), Complex(a, 0.0)]
  p [Complex(a, 2), Complex(a, 2r), Complex(a, 2.0), Complex(a, 2i)]
end
p [Complex(1r, 2i), Complex(1, Complex(2, 0r)), Complex(1, Complex(2, 0.0))]
begin
  c.instance_variable_set(:@x, 1)
rescue => e
  p [e.class, e.message]
end
begin
  def c.new_method; 1; end
rescue => e
  p [e.class, e.message]
end
p [Complex.respond_to?(:new), Complex.respond_to?(:allocate)]
