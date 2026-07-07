def dispatch
  yield(a: 1, b: 2)
end
r1 = dispatch { |a:, b:| a + b }
puts r1
r2 = dispatch { |a:, b: 100, **rest| [a, b, rest] }
p r2
