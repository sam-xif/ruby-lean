# The other half of issue #184: `rb_yield_values2(argc, argv)` hands the block
# the values `each` yielded, exactly as yielded — no packing — for map,
# flat_map, filter_map, find_index, count, take_while and the all?/any?/none?/
# one? family. A one-parameter block therefore sees only the first value, which
# is what a plain `each { |x| ... }` gives it, but a multi-parameter block sees
# every value.
class P
  include Enumerable

  def each
    yield 3, :a
    yield 1, :b
  end
end

# A splat parameter records the exact argument list each method passes.
def args(obj, meth)
  seen = []
  obj.send(meth) { |*a| seen.push(a) }
  seen
end

p args(P.new, :map)
p args(P.new, :flat_map)
p args(P.new, :filter_map)
p args(P.new, :find_index)
p args(P.new, :count)
p args(P.new, :take_while)
p args(P.new, :all?)
p args(P.new, :any?)
p args(P.new, :none?)
p args(P.new, :one?)

p P.new.map { |x| x }
p P.new.map { |a, b| [b, a] }
p P.new.flat_map { |a, b| [a] }
p P.new.filter_map { |a, b| b }
p P.new.find_index { |a, b| b == :b }
p P.new.count { |a, b| b == :a }
p P.new.take_while { |a, b| b == :a }
p P.new.all? { |a, b| b == :a }
p P.new.any? { |a, b| b == :b }
p P.new.none? { |a, b| b == :c }
p P.new.one? { |a, b| b == :a }

# The same block protocol on the native receivers, whose `each` yields one
# value (Hash's yields the [key, value] pair as one value).
h = { a: 1, b: 2 }
p args(h, :map)
p h.map { |k, v| [k, v] }
p h.count { |k, v| v > 1 }
p h.filter_map { |k, v| k if v == 2 }
a = [10, 20]
p args(a, :map)
p a.map { |x| x }
p (1..2).map { |x| x }
p (1..2).select { |x| x > 1 }
