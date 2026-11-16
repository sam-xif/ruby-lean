# `Range#count` is `Enumerable#count`, not `#size`. CRuby's `enum_count` asks
# the receiver for a size first and uses it only for the bare call, so a block
# counts its matches and an item argument counts equality. The prelude aliased
# `count` to `size` instead, which answered the element count for a block — a
# silent wrong answer — and rejected the item argument with `size`'s arity
# (issue #115).
p (1..5).count
p (1..5).count(2)
p (1..5).count(9)
p (1..5).count(nil)
p (1...5).count
p (1..1).count
p (5..1).count

# the block form counts matches, not elements
p (1..5).count { |x| x > 2 }
p (1...5).count { |x| x.even? }
p (1..5).count { |x| false }
p (5..1).count { |x| true }

# an item argument counts equality, and a block beside it is ignored
p (1..5).count(2) { |x| x > 2 }

begin
  (1..5).count(2, 3)
rescue ArgumentError => e
  p e.message
end

# `#size` is still `#size`, and still takes no argument
p (1..5).size
p (1..5).count

begin
  (1..5).size(1)
rescue ArgumentError => e
  p e.message
end

# the other collections are untouched by the Range fix
p [1, 2, 3].count
p [1, 2, 3].count { |x| x > 1 }
p({ a: 1 }.count)
