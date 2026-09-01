class Point
  def initialize(x)
    @x = x
  end

  def getX
    @x
  end

  def myself
    self
  end
end

Point.new(7).myself.getX
