def Complex(*args)
  :overridden
end
def literal
  -1.0000000000000000001ri
end
p [0i, -0.0i, -1.2i, 0xffi, 077i, 0b101i, 1e20i, 1.25ri, literal]
p [literal.equal?(literal), 1i.equal?(1i), Complex(1, 2)]
class Complex
  def -@
    :negated
  end
end
p [-1.2i, -(1.2i), -1.2ri, -(1.2ri)]
Complex = :shadowed
p [1i, defined?(1.2ri)]
