def f(a, b = 2, *rest, c:, d: 4, **kw, &blk)
  [a, b, rest.length, c, d, kw.length, blk.nil?].length
end

f(1, c: 3)
