class Point
  attr_accessor :x, :y
end
p = Point.new
p.x = 3
p.y = 4
puts p.x + p.y
puts p.instance_variable_get(:@x)
p.instance_variable_set(:@y, 100)
puts p.y
p Point.instance_methods(false).sort
