# `Array#index` is `Array#find_index`: CRuby defines the name on Array only, so
# every other Enumerable raises NoMethodError. An alias in the prelude's
# `Enumerable` used to answer for all of them.
def attempt
  yield.inspect
rescue Exception => e
  "#{e.class}: #{e.message}"
end

# The Array surface: one argument, or a block; never two.
p attempt { [1, 2, 3].index(2) }
p attempt { [1, 2, 3].index { |x| x > 1 } }
p attempt { [1, 2, 3].index(2, 1) }
p attempt { [1, 2, 3].index(2, 1, 3) }

# Enumerables that are not Arrays.
p attempt { (1..5).index(3) }
p attempt { { a: 1 }.index(1) }
class Counter
  include Enumerable

  def each
    yield 1
    yield 2
  end
end
p attempt { Counter.new.index(2) }

# `find_index` is the Enumerable method, and is still there.
p attempt { (1..5).find_index(3) }
p attempt { { a: 1 }.find_index { |k, v| k == :a } }

# Comparison is `==`, and the array is read live, as `rb_ary_index` does.
class Point
  attr_reader :v

  def initialize(v)
    @v = v
  end

  def ==(other)
    other.is_a?(Point) && @v == other.v
  end
end
p [Point.new(1), Point.new(2)].index(Point.new(2))
xs = [1, 2]
seen = []
p xs.index { |x| seen << x; xs << 3; x > 2 }
p seen
