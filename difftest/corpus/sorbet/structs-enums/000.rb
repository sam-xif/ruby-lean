# typed: strict
require "sorbet-runtime"

class Point < T::Struct
  const :x, Integer
  const :y, Integer
end

pt = Point.new(x: 1, y: 2)
puts pt.x + pt.y

begin
  Point.new(x: 1, y: T.unsafe("two"))
rescue TypeError
  puts "constructor checked"
end
