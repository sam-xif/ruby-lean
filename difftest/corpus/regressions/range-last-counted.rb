# `Range#last` is two methods under one name. The bare form is `#end` except on
# an endless range, where CRuby raises RangeError; the counted form walks back
# from the end, clamps at the beginning, and has its own ArgumentErrors. The
# model gave the builtin zero arity, so every counted call raised
# `wrong number of arguments (given 1, expected 0)` — an answer where the model
# must decline (issue #110).
p (1..5).last(2)
p (1..5).last(0)
p (1..5).last(9)
p (1...5).last(2)
p (nil..5).last(2)
p (nil...5).last(2)
p (5..1).last(2)
p (1...1).last(2)
p (1..0).last(2)
p (1..5).last
p (nil..5).last

begin
  (1..).last
rescue RangeError => e
  p e.message
end

begin
  (1..).last(2)
rescue RangeError => e
  p e.message
end

begin
  (1..5).last(-1)
rescue ArgumentError => e
  p e.message
end

begin
  (1..5).last(2, 3)
rescue ArgumentError => e
  p e.message
end
