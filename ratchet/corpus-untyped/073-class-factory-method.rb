class Point
  def initialize(x, y)
    @x = x
    @y = y
  end

  def self.origin
    new(0, 0)
  end
end

Point.origin
