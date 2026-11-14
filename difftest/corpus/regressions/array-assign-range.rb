# `Array#[]=` with a **Range** subscript is `rb_range_beg_len` + `rb_ary_splice`,
# not one element write. The model routed every two-argument `[]=` through
# `rb_num2long`, so `a[1..2] = [9]` raised
# `TypeError: no implicit conversion of Range into Integer` — a wrong answer, in
# the TypeError family the validator claims to exclude.
#
# The matrix covers every resolution rule in one breath: which elements a range
# replaces, an empty range (`beg > end`) inserting at `beg`, a start past the end
# padding with `nil`, negative endpoints counting from the end, a start too small
# even after that being `RangeError "<range> out of range"`, endless and
# beginless subscripts, and Float endpoints truncating toward zero.
#
# The value side is separate: an Array value contributes its *elements*, `nil` is
# the single value `nil` (not an empty list), and any other value is one element.

def assign(a, rng, v)
  b = a.dup
  b[rng] = v
  b
end

p [assign([1, 2, 3, 4], 1..2, [9]), assign([1, 2, 3, 4], 1...2, [9])]
p [assign([1, 2, 3, 4], 1..1, [9]), assign([1, 2, 3, 4], 1..0, [9])]
p [assign([1, 2, 3, 4], 0..0, []), assign([1, 2, 3, 4], 1..2, [])]
p [assign([1, 2, 3, 4], 1..5, [9]), assign([1, 2, 3, 4], 1..10, [9])]
p [assign([1, 2, 3, 4], 4..5, [9]), assign([1, 2, 3, 4], 5..6, [9])]
p [assign([1, 2, 3, 4], 5..4, [9]), assign([1, 2, 3, 4], 10..-1, [9])]
p [assign([1, 2, 3, 4], -2..-1, [9]), assign([1, 2, 3, 4], -2..2, [9])]
p [assign([1, 2, 3, 4], -1..-1, [9]), assign([1, 2], -1..0, [9])]
p [assign([1, 2, 3, 4], 1.., [9]), assign([1, 2, 3, 4], 1..., [9])]
p [assign([1, 2, 3, 4], ..2, [9]), assign([1, 2, 3, 4], ..-2, [9])]
p [assign([1, 2, 3, 4], ...2, [9]), assign([1, 2, 3, 4], ..-10, [9])]
p [assign([], 0..0, [9]), assign([], 0...0, [9]), assign([], 0..1, [9])]
p [assign([1], 0..-1, [9]), assign([1], 0..-2, [9]), assign([1], 1..0, [])]
p [assign([1, 2], 2..2, [9]), assign([1, 2], 3..3, [9]), assign([1, 2], 3..2, [9])]
p [assign([1, 2], 5.., [9]), assign([1, 2], 3..., [9])]

# Float endpoints truncate toward zero, and so do negative ones
p [assign([1, 2, 3], 1.7..2, [9]), assign([1, 2, 3], 1..2.9, [9])]
p [assign([1, 2, 3], 2.5..3, [9]), assign([1, 2, 3], 3.9..3.9, [9])]
p [assign([1, 2, 3], -0.5..1, [9]), assign([1, 2, 3], 1..-0.5, [9])]
p [assign([1, 2, 3], 0..-0.1, [9]), assign([1, 2, 3], -1.9..-1.1, [9])]

# the value: elements of an Array, the single value nil, or one element
p [assign([1, 2, 3, 4], 1..2, 9), assign([1, 2, 3, 4], 1..2, nil)]
p [assign([1, 2, 3], 1..2, "ab"), assign([1, 2, 3], 1..2, [nil])]
p [assign([1, 2, 3], 1..2, [[2]]), assign([1, 2, 3], 1..2, 1..2)]
p [assign([1, 2, 3, 4], 1..2, [9, 10, 11]), assign([1, 2, 3], 1..2, [])]

# the write answers the value, and grows the array in place
a = [1, 2, 3]
p [(a[1..1] = :x), a]
p [(a[0..0] = []), a]

# RangeError names the range, and the frozen check comes first
begin
  assign([1, 2, 3, 4], -5..2, [9])
rescue RangeError => e
  p [e.class, e.message]
end
begin
  assign([1, 2, 3, 4], -5...2, [9])
rescue RangeError => e
  p [e.class, e.message]
end
begin
  assign([1, 2, 3, 4], -5.5..2, [9])
rescue RangeError => e
  p [e.class, e.message]
end
begin
  assign([1, 2, 3, 4], -10.., [9])
rescue RangeError => e
  p [e.class, e.message]
end
begin
  [1, 2, 3].freeze[0..1] = [9]
rescue FrozenError => e
  p [e.class, e.message]
end
begin
  [1, 2, 3].freeze[-5..2] = [9]
rescue FrozenError => e
  p [e.class, e.message]
end

# the Integer subscript path is untouched
b = [1, 2, 3]
b[1] = :y
b[5] = :z
p b
begin
  [1, 2, 3][-5] = 0
rescue IndexError => e
  p [e.class, e.message]
end
begin
  [1, 2, 3]["x"] = 0
rescue TypeError => e
  p [e.class, e.message]
end
