# L278: literals bypass constructor methods/constants and preserve every digit.
def Rational(*args)
  puts "overridden constructor"
  :override
end
p Rational(2, 3)
p [0r, -1r, 0xffr, 0b11r, 077r, 1.2r, -1.2r, 1.0000000000000000001r]
p [defined?(1.2r), 1.2r.class, 1.2r.frozen?]
def literal
  1.2r
end
p [literal.equal?(literal), 1.2r.equal?(1.2r)]
values = []
2.times { values << 1.2r }
p values[0].equal?(values[1])
Rational = :shadowed_constant
p 1.0000000000000000001r
