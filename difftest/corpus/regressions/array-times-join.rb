# `Array#*` with a String is `rb_ary_join` (`rb_ary_times` hands the String
# straight to it), so it renders one part per **element** at every level and
# keeps the separator boundary around an empty nested array.
p [1, 2] * "-"
p [1, 2] * ""
p [] * "-"
p [[], 1] * "-"
p [1, [], 2] * "-"
p [[], []] * "-"
p [[1], []] * "-"
p [1, [[]], 2] * "-"
p [1, [2, [3, []]]] * "-"

# The Integer form is unchanged; a Float converts with `rb_num2long`, which
# truncates toward zero, so `-0.5` is zero rather than a negative count.
p [1, 2] * 2
p [1, 2] * 0
p [1, 2] * 1.9
p [1] * -0.5

# An argument that is neither a String nor convertible is CRuby's `TypeError`
# with CRuby's message, not the blanket "Array#* join form" gate.
[[:x, "no implicit conversion of Symbol into Integer"],
 [nil, "no implicit conversion from nil to integer"],
 [true, "no implicit conversion of true into Integer"]].each do |arg, msg|
  begin
    [1, 2] * arg
  rescue TypeError => e
    p [e.class, e.message == msg]
  end
end

begin
  [1, 2] * -1
rescue ArgumentError => e
  p [e.class, e.message]
end

# "Nested" is `rb_check_array_type`, so an element answering `to_ary` is joined
# as a unit — before `to_s` is asked.
class Pair
  def initialize(a, b)
    @a = a
    @b = b
  end

  def to_ary = [@a, @b]
end
p ["x", Pair.new(7, 8)] * ","
p [[], Pair.new(7, 8)] * ","

# An element overriding `to_s` is rendered by it, at every level.
class Tok
  def to_s = "T"
end
p [Tok.new, 1] * "-"
p [[], Tok.new] * "-"
