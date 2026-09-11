def apply(f, v)
  f.call(v)
end

apply(->(x) { x * 2 }, 5)
