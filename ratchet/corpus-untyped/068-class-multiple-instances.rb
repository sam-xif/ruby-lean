class Point
  def initialize(x)
    @x = x
  end

  def getX
    @x
  end
end

a = Point.new(1)
b = Point.new(2)
a.getX + b.getX
