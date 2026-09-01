class Point
  attr_reader :x, :y

  def initialize(x, y)
    @x = x
    @y = y
  end
end

Point.new(1, 2).x + Point.new(1, 2).y
