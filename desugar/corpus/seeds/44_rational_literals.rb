# Native literals remain exact and bypass overridable constructors and constants.
def Rational(*args)
  :constructor_override
end
def literal
  -1.0000000000000000001r
end
p [0r, 0xffr, 077r, 0b101r, 1.25r, literal]
p [literal.equal?(literal), 1r.equal?(1r), Rational(1, 2)]
class Rational
  def -@
    :negated_by_method
  end
end
p [-1.2r, -(1.2r)]
Rational = :constant_override
p [1.2r, defined?(1.2r)]
