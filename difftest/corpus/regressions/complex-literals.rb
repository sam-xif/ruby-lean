# L279: literal construction bypasses dispatch and caches each syntax site.
def Complex(*args)
  :overridden_constructor
end
def imaginary_literal
  1.0000000000000000001ri
end
p [0i, -2i, 0xffi, 077i, 0b11i, 1.2i, -0.0i, 1e20i, 1.2ri]
p [defined?(1i), 1i.class, 1i.frozen?, imaginary_literal]
p [imaginary_literal.equal?(imaginary_literal), 1i.equal?(1i), Complex(1, 2)]
values = []
2.times { values << 1.2ri }
p [values[0].equal?(values[1]), values[0].imag.equal?(values[1].imag)]
class Complex
  def -@
    :negated_by_method
  end
end
p [-1.2i, -(1.2i), -1.2ri, -(1.2ri)]
Complex = :shadowed_constant
p [1i, 1.2ri]
