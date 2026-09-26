# Keyword call args (C25): a brace-less trailing `a: 1, **h` is KEYWORD args, kept as a
# `[:kwargs,…]` marker and rendered brace-less — NOT a positional hash `{a: 1}`. Ruby 3
# separates the two: keyword args bind to keyword params, a positional hash to a positional
# param. This seed pins the separation in both directions.
def kw(a:, b: 2, **rest)
  [a, b, rest]
end
def pos(h)
  h
end

print("kw=#{kw(a: 1, c: 3).inspect};")          # binds keyword params + kwrest
h = { a: 10, b: 20 }
print("splat=#{kw(**h).inspect};")              # ** splat of a hash into keywords

# A brace-less hash to a positional-param method still passes as one positional hash.
print("pos=#{pos(x: 1, y: 2).inspect};")

# Non-symbol keys in a keyword hash (`"s" => v`) are still a keyword hash, not a literal.
print("strkey=#{pos("s" => 1, 2 => 3).inspect};")

# Eval order: positional arg before the keyword values, keyword values left-to-right.
def ord(a, b:, c:)
  [a, b, c]
end
r = ord((print("a;"); 0), b: (print("b;"); 1), c: (print("c;"); 2))
print("ord=#{r.inspect}")
r
