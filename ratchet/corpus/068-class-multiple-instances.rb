# typed: true
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

a = Point.new(1)
b = Point.new(2)
a.getX + b.getX
