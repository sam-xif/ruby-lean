# typed: true
class Shape
  extend T::Sig
  sig { params(sides: Integer).void }
  def initialize(sides)
    @sides = sides
  end

  sig { returns(Integer) }
  def sides
    @sides
  end
end

class Triangle < Shape
  extend T::Sig
  sig { void }
  def initialize
    super(3)
  end
end

Triangle.new.sides
