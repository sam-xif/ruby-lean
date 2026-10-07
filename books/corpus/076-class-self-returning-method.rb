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

  sig { returns(Point) }
  def myself
    self
  end
end

Point.new(7).myself.getX
