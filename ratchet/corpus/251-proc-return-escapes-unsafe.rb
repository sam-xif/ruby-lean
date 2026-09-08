def f
  p = proc { return "s" }
  p.call
  1
end
f + 1
