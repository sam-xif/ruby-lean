# typed: true
class Point
  extend T::Sig
  sig { params(x: Integer, y: Integer).void }
  def initialize(x, y)
    @x = x
    @y = y
  end

  sig { returns(Point) }
  def self.origin
    new(0, 0)
  end
end

Point.origin
