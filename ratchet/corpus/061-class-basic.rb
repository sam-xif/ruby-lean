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
end

Point.new(1, 2).getX
