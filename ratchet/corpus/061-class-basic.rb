class Point
  def initialize(x, y)
    @x = x
    @y = y
  end

  def getX
    @x
  end
end

Point.new(1, 2).getX
