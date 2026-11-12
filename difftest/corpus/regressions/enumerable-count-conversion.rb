# #137. `Enumerable#take`, `#drop`, `#each_slice` and `#each_cons` compared the
# count or size argument as it arrived (`n <= 0`, `r.length == n`), so a negative
# count answered instead of raising, a fractional one never matched `length`, a
# non-number raised from `<`, and a count CRuby cannot convert raised nothing.
#
# CRuby converts with `NUM2LONG` first: an Integer, a Float truncated toward
# zero, or an object's `to_int`, then a `long` range check, then the method's
# own validation. Every message in this file is CRuby 4.0.5's, verbatim.

def attempt
  yield
rescue => e
  [e.class, e.message]
end

items = [1, 2, 3, 4]

p attempt { items.take(-1) }
p attempt { items.take(0) }
p attempt { items.take(2.9) }
p attempt { items.take(-0.5) }
p attempt { items.drop(-1) }
p attempt { items.drop(0) }
p attempt { items.drop(2.9) }
p attempt { items.take(nil) }
p attempt { items.drop(nil) }
p attempt { items.take(:sym) }
p attempt { items.drop("2") }
p attempt { items.take(2**63) }
p attempt { items.take(-2**64) }
p attempt { items.take(2**63 - 1) }
p attempt { items.take(Float::NAN) }
p attempt { items.take(Float::INFINITY) }
p attempt { items.drop(-Float::INFINITY) }

class ToInt
  def to_int
    2
  end
end
p attempt { items.take(ToInt.new) }

class ToIntNil
  def to_int
    nil
  end
end
p attempt { items.take(ToIntNil.new) }

class ToIntFloat
  def to_int
    2.0
  end
end
p attempt { items.drop(ToIntFloat.new) }

slices = []
p attempt { items.each_slice(1.5) { |s| slices << s } }
p slices

windows = []
p attempt { items.each_cons(1.5) { |w| windows << w } }
p windows
p attempt { items.each_slice(0) { |s| } }
p attempt { items.each_slice(-2) { |s| } }
p attempt { items.each_cons(0) { |w| } }
p attempt { items.each_cons(-2) { |w| } }
p attempt { items.each_slice(nil) { |s| } }

p attempt { {a: 1, b: 2}.first(-1) }
p attempt { {a: 1, b: 2}.take(1.5) }
p attempt { (1..4).drop(2.5) }

class Counted
  include Enumerable

  def each
    yield 1
    yield 2
    yield 3
  end
end
p attempt { Counted.new.take(-1) }
p attempt { Counted.new.take(1.5) }
p attempt { Counted.new.drop(1.5) }
p attempt { Counted.new.first(1.5) }
