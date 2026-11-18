# `Array#join` places a separator around each nested array **as a unit**, so an
# empty nested array is an empty part and still gets a boundary. Flattening the
# parts away dropped it (issue #102).
p [1, [2, [3, nil]], []].join("-")
p [[], 1].join("-")
p [1, [], 2].join("-")
p [[], []].join("-")
p [1, [[]], 2].join("-")
p [[1], []].join("-")

# The empty separator sees no boundary at all, in either implementation.
p [[], []].join
p [1, [2, [3, nil]], []].join

# `to_ary` decides what is nested (`rb_check_array_type`), so an object that
# answers an empty Array joins as one.
class EmptyAry
  def to_ary = []
end
p [EmptyAry.new, 1].join("-")

# A nested Array subclass that overrides `length` is still measured by its real
# elements: CRuby reads the array, not the Ruby method.
class EmptySub < Array
  def length = 99
end
p [EmptySub.new, 1].join("-")

# `Array#flatten` returns the leaves, so it drops the empty nested arrays that
# `join` keeps as parts. The two share the flattening walk; this pins the side
# that must not grow a part.
p [[], 1].flatten
p [1, [[], 2], []].flatten
p [[]].flatten
p [[[], []]].flatten

# The Ruby implementation (`__join_slow`, chosen when an element overrides
# `to_s`) places the same boundaries.
class Rendered
  def to_s = "r"
end
p [Rendered.new, [], Rendered.new].join("-")
p [[], Rendered.new, []].join("-")
