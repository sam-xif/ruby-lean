# C32 implicit_node: Ruby 3.1 hash / keyword shorthand `{x:}` and `foo(x:)`. Prism
# resolves the omitted value to either a local read or a self-call, so both resolutions
# have to survive the desugaring — and the eval-order obligation is that the resolved
# expression is evaluated exactly once, in argument position.
x = 1
y = 2
h = { x:, y: }
print("hash=#{h.inspect};")

def take(x:, y: 0)
  "#{x}/#{y}"
end
print("kw=#{take(x:, y:)};")

# Shorthand mixed with explicit pairs, and as one keyword argument among several.
print("mix=#{{ x:, w: 7 }.inspect};")
print("kwmix=#{take(y: 5, x:)};")

# The omitted value can resolve to a *method* call, not a local.
class C
  def name = "c"

  def to_h = { name: }
end
print("meth=#{C.new.to_h.inspect};")

# Eval-order: a shorthand whose resolution is a method call must fire exactly once, and
# in source order relative to its neighbours.
def one
  print("one;")
  1
end

def two
  print("two;")
  2
end
print("order=#{{ a: one, one:, two: }.inspect}")
[h, x, y]
