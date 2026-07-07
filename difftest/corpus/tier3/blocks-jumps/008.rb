def make_returner
  lambda { |x| return x * 2; 999 }
end
l = make_returner
puts l.call(21)

p1 = proc { |a, (b, c)| "#{a}|#{b}|#{c}" }
puts p1.call(1, [2, 3])
puts p1.call(1, 2)

lm = ->(a, *rest, z) { "#{a} #{rest.inspect} #{z}" }
puts lm.call(1, 2, 3, 4)
puts lm.call(1, 2)

puts proc { |*a| a }.call(1, 2, 3).inspect
