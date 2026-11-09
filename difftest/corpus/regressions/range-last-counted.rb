# Range#last: the counted form, the beginless form, and the bare form on an
# endless range.
p (1..5).last(2)
p (1..5).last(0)
p (1..5).last(9)
p (1...5).last(2)
p (nil..5).last(2)
p (5..1).last(2)
begin
  (1..).last
rescue RangeError => e
  p e.message
end
begin
  (1..5).last(-1)
rescue ArgumentError => e
  p e.message
end
