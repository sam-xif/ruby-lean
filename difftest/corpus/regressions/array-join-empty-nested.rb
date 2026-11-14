# `ary_join_1` appends the separator **before** every element after the first,
# at every level, so a nested array keeps the boundary its position earned even
# when it renders nothing. Collecting the rendered elements into a flat list of
# parts and intercalating it loses that boundary.
p [1, [2, [3, nil]], []].join("-")
p [[], 1].join("-")
p [1, [], 2].join("-")
p [[], []].join("-")
p [1, [[]], 2].join("-")
p [[1], []].join("-")

# The boundary is not the separator's contents: an empty separator hides it.
p [1, [], 2].join
p [[], []].join
p [1, [], 2].join("")

# nil renders as the empty string, and still takes its boundary.
p [nil, nil].join(",")
p [[nil], nil].join(",")

# Deeper nesting, and a directory-like shape (empty arrays on both sides).
p [[1, []], [2]].join("-")
p [1, [2, []], 3].join(", ")
p [[[], [[]], []], []].join("x")

# An element answering `to_ary` is joined, so it keeps a boundary too.
class EmptyAry
  def to_ary = []
end
p [EmptyAry.new, [1]].join(",")
p [1, EmptyAry.new, 2].join(",")

# And an element rendered with `to_s` — the dispatching path, which is the same
# rule one level down.
class Tag
  def initialize(name)
    @name = name
  end

  def to_s = @name
end
p [Tag.new("a"), [], Tag.new("b")].join("-")
p [Tag.new("a"), [[], []], Tag.new("b")].join("-")
