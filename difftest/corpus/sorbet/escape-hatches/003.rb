# typed: true
require "sorbet-runtime"

class Point < T::Struct
  prop :x, Integer
end

pt = Point.new(x: 1)
pt.instance_variable_set(:@x, "not an int")
puts pt.x
puts pt.x.class
