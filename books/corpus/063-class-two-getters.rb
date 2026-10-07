# typed: true
class Point
  extend T::Sig
  sig { params(x: Integer, y: Integer).void }
  def initialize(x, y)
    @x = x
    @y = y
  end

  sig { returns(Integer) }
  def getX
    @x
  end

  sig { returns(Integer) }
  def getY
    @y
  end
end

p = Point.new(3, 4)
p.getX + p.getY
