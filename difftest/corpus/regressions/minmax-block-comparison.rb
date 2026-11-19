# `Enumerable#minmax` with a block is a *comparison*, not a key function
# (CRuby's `enum_minmax` / `minmax_ii`): elements arrive in consecutive pairs,
# the pair is ordered first, its smaller is offered to the running minimum and
# its larger to the running maximum, and a trailing odd element is offered to
# both last. Answering `[min { ... }, max { ... }]` returned the pair under the
# default comparison and ran the block in a different order, so every line here
# pins the pair, the order or the arguments of the `yield`s.

# The pair under a block that asks for another order.
p [1, 2, 3].minmax { |a, b| b <=> a }
p %w[xxx x xxxx xx].minmax { |a, b| a.size <=> b.size }
p [10, 9, 8].minmax { |a, b| a <=> b }
p [3, 1, 2].minmax { |a, b| a <=> b }
p [4, 4, 1, 1].minmax { |a, b| a <=> b }

# The sequence of comparisons, which a program that logs them observes: the
# pair first, then the smaller against the minimum and the larger against the
# maximum, and a lone trailing element against both.
(1..5).each do |n|
  log = []
  pair = (1..n).to_a.minmax { |a, b|
    log.push([a, b])
    a <=> b
  }
  puts "#{n}: #{pair.inspect} after #{log.inspect}"
end

# Empty and single-element receivers never call the block; the single element is
# both extremes.
empty_log = []
p [].minmax { |a, b|
  empty_log.push([a, b])
  a <=> b
}
p empty_log
single_log = []
p [5].minmax { |a, b|
  single_log.push([a, b])
  a <=> b
}
p single_log

# A tie takes the *earlier* element for both extremes, which is observable when
# two elements compare equal but are not the same object.
class Tie
  attr_reader :tag

  def initialize(tag)
    @tag = tag
  end

  def <=>(other)
    0
  end

  def inspect
    "Tie(#{@tag})"
  end
end

first = Tie.new(:first)
second = Tie.new(:second)
third = Tie.new(:third)
p [first, second].minmax { |a, b| a <=> b }
p [first, second, third].minmax { |a, b| a <=> b }

# A Hash enumerates `[key, value]` pairs, and the block takes both as arguments.
p({ foo: 0, bar: 1, baz: 2 }.minmax { |x, y| x[1] <=> y[1] })
p({ foo: 0, bar: 1, baz: 2 }.minmax { |x, y| y[1] <=> x[1] })

# Ranges, an empty range, and a user class that gets `minmax` from Enumerable.
p (1..7).minmax { |a, b| a <=> b }
p (7..1).minmax { |a, b| a <=> b }

class Bag
  include Enumerable

  def initialize(items)
    @items = items
  end

  def each
    i = 0
    while i < @items.length
      yield(@items[i])
      i = i + 1
    end
  end
end

p Bag.new([4, 1, 3, 2, 5]).minmax { |a, b| a <=> b }
p Bag.new([4, 1, 3, 2, 5]).minmax { |a, b| b <=> a }

# Without a block the pair is the same one `min`/`max` answer.
p [1, 2, 3].minmax
p [3, 1, 2].minmax
p [].minmax
p %w[d c b a].minmax
