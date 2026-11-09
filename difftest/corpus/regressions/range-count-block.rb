# `Range#count` was `alias count size`, so a block was a silent no-op: the model
# answered the element count where CRuby answers the count of matches, and
# `(1..5).count(2)` came back as `size`'s arity error rather than a count.
#
# CRuby's `enum_count` defers to `size` only for the bare form; everything else
# counts. The bare form still answers `size` here (it is O(1), and `size` is what
# CRuby's `enum_count` asks for anyway); a block counts through `each`; the item
# form stays the named `Enumerable#count with an argument` gate that every other
# collection (`Array#count`) already gives.
def show(label)
  puts("#{label} => #{yield.inspect}")
rescue StandardError => e
  puts("#{label} => #{e.class}: #{e.message}")
end

# The bare form is `size`, and keeps `size`'s O(1) path
show("bare")         { (1..5).count }
show("exclusive")    { (1...5).count }
show("empty")        { (1..0).count }
show("empty excl")   { (1...1).count }

# A block counts matches, not elements
show("some")         { (1..5).count { |x| x > 2 } }
show("none")         { (1..5).count { |x| x > 10 } }
show("all")          { (1..5).count { |x| x > 0 } }
show("truthy")       { (1..5).count { |x| x } }
show("single")       { (3..3).count { |x| x == 3 } }

# `size` keeps its own arity: `count` no longer inherits it
show("size")         { (1..5).size }
show("size arity")   { (1..5).size(1) }

# Iteration is `succ`, and CRuby refuses a Float begin — the block form must
# reach that refusal, not the model's own `succ` NoMethodError
show("float each")   { (1.0..3.0).each { |x| x } }
show("float count")  { (1.0..3.0).count { |x| x > 1 } }
