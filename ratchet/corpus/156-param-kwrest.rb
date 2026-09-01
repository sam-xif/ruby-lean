def opts(**kw)
  kw["a"].nil? ? 0 : 1
end

opts(a: 1)
