# L278: Integer/Float delegate to Rational#coerce; opaque operands run hooks.
class Partner
  def coerce(other)
    puts "coerce #{other.inspect}"
    [2r, 3r]
  end
  def ==(other)
    puts "compare #{other.inspect}"
    :truthy
  end
end
p [1r + Partner.new, 1r <=> Partner.new, 1r == Partner.new]
class Rational
  alias original_coerce coerce
  def coerce(other)
    puts "rational coerce #{other}"
    original_coerce(other)
  end
end
p [1 + 0.5r, 1.0 + 0.5r]
p 1 / 0.5r                       # native reciprocal bypasses coerce
class Rational
  def self.new
    :custom_constructor
  end
end
p Rational.new

class Rational
  alias native_equal ==
  def ==(other)
    puts "equality hook"
    :truthy
  end
end
a = 1r
p [a.eql?(2r), a.eql?(a), a.eql?(1), a.native_equal(2r)]
