def collect(**kw)
  kw
end
p collect(a: 1, b: 2)
h = {"x" => 1, :y => 2}
p collect(**h)
p collect(**{})
