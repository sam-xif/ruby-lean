# typed: true
class Point
  extend T::Sig
  attr_reader :x, :y

  sig { params(x: Integer, y: Integer).void }
  def initialize(x, y)
    @x = x
    @y = y
  end
end

Point.new(1, 2).x + Point.new(1, 2).y
