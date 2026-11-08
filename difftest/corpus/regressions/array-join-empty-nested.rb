# Each element is one part of the join. A nested Array is joined with the same
# separator and contributes that whole result as one part, so an empty nested
# Array is an empty part and still gets a separator boundary. The Lean fast
# path and the prelude's to_s-sensitive twin must both follow this.
p [1, [2, [3, nil]], []].join("-")
p [[], 1].join("-")
p [1, [], 2].join("-")
p [[], []].join("-")
p [1, [[]], 2].join("-")
p [[1], []].join("-")
p [1, [2, 3], 4].join("-")
p [[], []].join("")

class T
  def to_s = "x"
end

p [T.new, [], T.new].join(":")
p [["a", []], T.new].join("!")
p [T.new, ["a", [], "b"], []].join(",")
