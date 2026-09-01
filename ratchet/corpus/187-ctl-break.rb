s = 0
[1, 2, 3, 4].each do |x|
  break if x == 3
  s = s + x
end
s
