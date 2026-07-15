# M6a keyword heads (C28): for (index leaks), redo, undef, alias.
acc = []
for i in [1, 2, 3]
  acc << i
end
print("for=#{acc.inspect};")
print("leak=#{i};")           # `for` index leaks to enclosing scope (unlike a block param)

# for over a range with multiple targets.
pairs = []
for a, b in [[1, 2], [3, 4]]
  pairs << (a + b)
end
print("for2=#{pairs.inspect};")

# redo: re-run the current iteration (guarded so it terminates).
seen = []
tries = 0
[10, 20].each do |x|
  seen << x
  if x == 10 && tries < 1
    tries += 1
    redo
  end
end
print("redo=#{seen.inspect};")

# alias + undef on a fresh class.
class K
  def orig; "orig"; end
  alias aliased orig
  def gone; "gone"; end
  undef gone
end
k = K.new
print("alias=#{k.aliased};")
print("undef=#{k.respond_to?(:gone)};")
acc
