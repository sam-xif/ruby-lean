# Structured parameters (C25): optional, keyword (required + optional), keyword-rest, and
# block-capture params, plus post-rest requireds — exercised together and via a block.
def m(a, b = 10, *c, d, e:, f: 20, **g)
  [a, b, c, d, e, f, g]
end
print("full=#{m(1, 2, 3, 4, 5, e: 6, g: 7, extra: 8).inspect};")  # all slots busy
print("mins=#{m(1, 9, e: 0).inspect};")                            # b,f defaulted; c empty

# A later optional default may reference an earlier param (callee scope).
def dep(a, b = a * 2)
  [a, b]
end
print("dep=#{dep(4).inspect};")

# Optional/keyword params in a block, and keyword-rest collection in a block.
sum = [[1, 2], [3, 4]].map { |x, y = 100, **rest| x + y }
print("blk=#{sum.inspect};")

# Bare anonymous rest/kwrest/block forwarding.
def fwd(*, **, &)
  inner(*, **, &)
end
def inner(*a, **k)
  [a, k]
end
print("anon=#{fwd(1, 2, z: 3) { }.inspect}")
m(1, 9, e: 0)
