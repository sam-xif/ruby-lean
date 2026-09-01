class Point
  def initialize(x)
    @x = x
  end

  def getX
    @x
  end
end

def describe(p)
  p.getX
end

describe(Point.new(5))
