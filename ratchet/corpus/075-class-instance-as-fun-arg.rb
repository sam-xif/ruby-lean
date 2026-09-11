# typed: true
extend T::Sig
class Point
  extend T::Sig
  sig { params(x: Integer).void }
  def initialize(x)
    @x = x
  end

  sig { returns(Integer) }
  def getX
    @x
  end
end

sig { params(p: Point).returns(Integer) }
def describe(p)
  p.getX
end

describe(Point.new(5))
