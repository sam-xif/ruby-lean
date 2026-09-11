class Shape
  def initialize(sides)
    @sides = sides
  end

  def sides
    @sides
  end
end

class Triangle < Shape
  def initialize
    super(3)
  end
end

Triangle.new.sides
