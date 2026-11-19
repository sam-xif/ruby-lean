# Issue #102 — `Array#join` puts a separator boundary around every element, and
# a nested Array is one element. An empty nested Array is therefore a unit that
# renders "" and still opens and closes a boundary; flattening the nesting first
# drops it and answers a shorter String.
def show(label)
  r = begin
    yield.inspect
  rescue => e
    "#{e.class}: #{e.message}"
  end
  puts "#{label}: #{r.gsub(/0x[0-9a-f]+/, '0xADDR')}"
end

show("trailing empty")  { [1, [2, [3, nil]], []].join("-") }
show("leading empty")   { [[], 1].join("-") }
show("middle empty")    { [1, [], 2].join("-") }
show("two empty")       { [[], []].join("-") }
show("nested empty")    { [1, [[]], 2].join("-") }
show("empty after one") { [[1], []].join("-") }
show("empty sep")       { [[], 1].join }
show("nil in nested")   { [[nil, 1], 2].join("-") }
show("sym in nested")   { [[], :a].join("-") }

# The same rule on the prelude twin `__join_slow`, which dispatch picks when an
# element answers `to_ary` or when some element's `to_s` is overridden.
class Pair
  def initialize(a, b) = (@a, @b = a, b)
  def to_ary = [@a, @b]
end
class Loud
  def to_s = "L"
end
show("to_ary+empty")    { [Pair.new(7, 8), []].join("-") }
show("empty+to_ary")    { [[], Pair.new(7, 8)].join("-") }
show("to_s+empty")      { [Loud.new, []].join("-") }
show("empty+to_s")      { [[], Loud.new].join("-") }
show("deep to_ary")     { [1, [[]], Pair.new(7, 8)].join("-") }
