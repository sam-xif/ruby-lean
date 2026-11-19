# A user class whose `each` yields several values, one value and none: the
# Enumerable methods that work on the element must see `rb_enum_values_pack`'s
# answer ([a, b] for several, the value for one, nil for none), not the first
# yielded value (issue #184).
class P
  include Enumerable

  def each
    yield 3, :a
    yield 1, :b
  end
end

class Q
  include Enumerable

  def each
    yield 4
    yield 2, 5
    yield
  end
end

p P.new.to_a
p P.new.entries
p P.new.select { |x| x[0] > 1 }
p P.new.reject { |x| x[0] > 1 }
p P.new.find { |x| x[0] == 1 }
p P.new.include?([1, :b])
p P.new.tally
p P.new.group_by { |x| x[0] }
p P.new.partition { |x| x[0] > 1 }
p P.new.first
p P.new.first(1)
p P.new.take(1)
p P.new.drop(1)
p P.new.take_while { |x| x[0] > 1 }
p P.new.drop_while { |x| x[0] > 1 }
p((o = []; P.new.each_with_index { |x, i| o.push([x, i]) }; o))
p P.new.each_with_object([]) { |x, m| m.push(x) }
p((o = []; P.new.each_slice(1) { |s| o.push(s) }; o))
p((o = []; P.new.each_cons(2) { |s| o.push(s) }; o))
p((o = []; P.new.reverse_each { |x| o.push(x) }; o))
p P.new.min_by { |x| x[0] }
p P.new.max_by { |x| x[0] }
p P.new.min
p P.new.max
p P.new.minmax
p P.new.sort_by { |x| x[0] }
p P.new.sort
p P.new.inject { |a, b| [a, b] }
p P.new.inject([]) { |a, b| a + [b] }
p P.new.inject(:+)

# The block forms that compare a new element with a running one pass both as
# separate arguments, each packed.
seen = []
P.new.min { |a, b| seen.push([a, b]); a[0] <=> b[0] }
p seen
seen = []
P.new.sort { |a, b| seen.push([a, b]); a[0] <=> b[0] }
p seen

# A packed element is what `sum` adds, so a pair that no Integer can absorb
# raises CRuby's `TypeError`.
begin
  P.new.sum
rescue => e
  p [e.class, e.message]
end
p P.new.sum { |x| x[0] }

p Q.new.to_a
p Q.new.select { |x| !x.nil? }
p Q.new.first
p Q.new.take(3)
p Q.new.tally
p((o = []; Q.new.each_with_index { |x, i| o.push([x, i]) }; o))
