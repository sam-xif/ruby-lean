# The `Enumerable` methods a class gets from `include Enumerable` alone (issue
# #182). The receiver defines nothing but `each`, so every answer below comes
# from the module.
class C
  include Enumerable

  def initialize(*xs)
    @xs = xs
  end

  def each
    @xs.each { |x| yield x }
  end
end

# `each` yielding several values, and none at all: `each_entry` packs/answers
# nil, and `to_h`/`zip` pack the values the same way CRuby's
# `rb_enum_values_pack` does.
class D
  include Enumerable

  def each
    yield 1
    yield 1, 2
    yield
  end
end

p C.new(1, 2, 1, 3).uniq
p C.new(1, 1.0, 1).uniq
p C.new(1, 2, 1, 3).uniq { |x| x % 2 }
p C.new(nil, 1, nil, false).compact
p C.new([:a, 1], [:b, 2]).to_h
p C.new([:a, 1], [:b, 2]).to_h { |kv| [kv[0], kv[1] * 10] }
D.new.each_entry { |x| p x }
p C.new(1, 2, 3, 4).minmax_by { |x| -x }
p C.new(1, 1).minmax_by { |x| x }
p C.new(3, 1, 2).minmax_by { |x| x }
p C.new.minmax_by { |x| x }
p C.new(1).minmax_by { |x| x }
p C.new(1, 2, 3).grep(2..3)
p C.new(1, 2, 3).grep(2..3) { |x| x * 10 }
p C.new(1, 2, 3).grep_v(2..3)
p C.new(1, 2).zip([3, 4])
p C.new(1, 2).zip([3])
p C.new(1, 2).zip([3, 4], [5, 6]) { |row| p row }

# The three `to_h` refusals, and `zip`'s. `C.new(1).to_h` reaches
# `rb_hash_set_pair` with an Integer, which is Enumerable's message (no index);
# `Array#to_h`'s message for the same element carries one.
begin
  C.new(1).to_h
rescue => e
  p [e.class, e.message]
end
begin
  C.new([1, 2, 3]).to_h
rescue => e
  p [e.class, e.message]
end
begin
  C.new(1).to_h { |_x| 1 }
rescue => e
  p [e.class, e.message]
end
begin
  C.new(1, 2).zip(3)
rescue => e
  p [e.class, e.message]
end

# `Hash#to_h` is its own method: without a block it answers the receiver, so a
# default survives, and its block sees key and value as two arguments.
h = { a: 1 }
p h.to_h.equal?(h)
p({ a: 1 }.to_h { |k, v| [v, k] })

# The gated names are defined all the same: `respond_to?` must be true, so a
# program can ask before calling and never meet a `NoMethodError`.
p C.new(1, 2).respond_to?(:cycle)
p C.new(1, 2).respond_to?(:lazy)
p C.new(1, 2).respond_to?(:slice_before)
