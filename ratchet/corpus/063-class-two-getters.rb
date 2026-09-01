class Point
  def initialize(x, y)
    @x = x
    @y = y
  end

  def getX
    @x
  end

  def getY
    @y
  end
end

p = Point.new(3, 4)
p.getX + p.getY
