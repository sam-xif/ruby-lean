def m
  result = [1,2,3,4,5].each do |x|
    break "broke at #{x}" if x == 3
    puts x
  end
  puts "break value: #{result}"
  result
end
puts m.inspect

vals = [10,20,30].map do |x|
  next x * 2 if x == 20
  x
end
p vals
