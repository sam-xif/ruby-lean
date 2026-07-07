def opts(**kw)
  kw
end
base = {a: 1, b: 2}
p opts(**base, b: 3, c: 4)
p opts(a: 1, **base)
p opts(**base, **{d: 5})
