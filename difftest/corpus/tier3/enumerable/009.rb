# The element a class's `each` yields may be several values, one value or none
# (issue #184). CRuby's Enumerable methods work on `rb_enum_values_pack`: an
# Array for several values, the value itself for one, nil for none. A plain
# block parameter cannot stand in — `yield a, b` binds `|x|` to `a` — so a
# method that needs the element must pack it first.
class Pair
  include Enumerable

  def each
    yield 3, :a
    yield 1, :b
  end
end

class Single
  include Enumerable

  def each
    yield 7
  end
end

class Empty
  include Enumerable

  def each
    yield
  end
end

pair = Pair.new

# The methods that collect, test or return the element itself.
p pair.to_a
p pair.entries
p pair.select { |x| x[0] > 1 }
p pair.filter { |x| x.is_a?(Array) }
p pair.find_all { |x| !x.is_a?(Array) }
p pair.reject { |x| x[0] > 1 }
p pair.find { |x| x[0] == 1 }
p pair.detect { |x| x.is_a?(Array) }
p pair.find_index([1, :b])
p pair.group_by { |x| x[0] > 1 }
p pair.partition { |x| x[0] > 1 }
p pair.tally
p pair.include?([1, :b])
p pair.include?(3)
p pair.member?([3, :a])
p pair.first
p pair.first(1)
p pair.take(1)
p pair.drop(1)
p(begin; r = []; pair.each_slice(1) { |s| r.push(s) }; r; end)
p(begin; r = []; pair.each_cons(2) { |s| r.push(s) }; r; end)
p(begin; r = []; pair.reverse_each { |x| r.push(x) }; r; end)
p(begin; r = []; pair.each_with_index { |x, i| r.push([x, i]) }; r; end)
p pair.each_with_object([]) { |x, m| m.push(x) }
p pair.min
p pair.max
p pair.minmax
p pair.min { |a, b| a[0] <=> b[0] }
p pair.max { |a, b| a[0] <=> b[0] }
p pair.min_by { |x| x[0] }
p pair.max_by { |x| x[0] }
p pair.sort
p pair.sort { |a, b| b[0] <=> a[0] }
p pair.sort_by { |x| -x[0] }
p pair.inject { |a, b| b }
p pair.inject(0) { |a, b| a + b[0] }
p pair.inject(:+)
p pair.reduce([], :+)

# `all?`/`any?`/`none?`/`one?`/`count` with no block test the packed element;
# with a block they hand the yielded values to the block unchanged, so a
# two-parameter block still sees both. `take_while` and `find_index` do the
# same, while `drop_while` compares the packed element.
p pair.all?
p pair.any?
p pair.none?
p pair.one?
p pair.count
p pair.all? { |x| x.is_a?(Array) }
p pair.any? { |x| x.is_a?(Array) }
p pair.none? { |x| x.is_a?(Array) }
p pair.one? { |x| x.is_a?(Array) }
p pair.count { |x| x.is_a?(Array) }
p pair.take_while { |x| x.is_a?(Array) }
p pair.take_while { |x| x }
p pair.drop_while { |x| x.is_a?(Array) }
p pair.drop_while { |x| false }
p pair.find_index { |x| x.is_a?(Array) }
p pair.map { |a, b| [a, b] }
p pair.flat_map { |a, b| [a, b] }

# The methods whose block *is* the answer — `map`/`collect`, `flat_map`,
# `filter_map` — forward the yielded values instead (`rb_yield_values2`), so
# `|x|` binds the first and `|a, b|` binds both.
p pair.map { |x| x }
p pair.collect { |*v| v }
p pair.flat_map { |x| [x] }
p pair.filter_map { |x| x }
p Single.new.sum { |x| x }

# Nothing reaches the user's own block parameters: `each { |a, b| }` still
# receives the values separately.
p(begin; r = []; pair.each { |a, b| r.push([a, b]) }; r; end)

# One value, and none at all.
p Single.new.to_a
p Single.new.map { |x| x + 1 }
p Single.new.select { |x| true }
p Single.new.min
p Empty.new.to_a
p Empty.new.map { |x| x.nil? }
p Empty.new.select { |x| x.nil? }
p Empty.new.first
p Empty.new.count
p Empty.new.tally
p Empty.new.sort
p Empty.new.min

# Array, Hash and Range are unaffected: their native `each` is unchanged.
p [1, 2].map { |x| x * 2 }
p [1, 2, 3].select { |x| x > 1 }
p({ "a" => 1 }.map { |k, v| [k, v] })
p({ "a" => 1 }.map { |x| x })
p({ "a" => 1, "b" => 1 }.tally)
p({ "a" => 1 }.each_with_object({}) { |(k, v), m| m[v] = k })
p((1..3).to_a)
p((1..4).sum)
p(begin; r = []; (1..4).each_slice(2) { |s| r.push(s) }; r; end)
