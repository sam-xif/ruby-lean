# typed: true
class Point
  extend T::Sig
  sig { params(x: Integer, y: Integer).void }
  def initialize(x, y)
    @x = x
    @y = y
  end

  sig { returns(Integer) }
  attr_reader :x, :y
end

Point.new(1, 2).x + Point.new(1, 2).y
