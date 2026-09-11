# typed: true
class Point
  extend T::Sig
  sig { params(x: Integer).void }
  def initialize(x)
    @x = x
  end
end

[Point.new(1), Point.new(2)]
