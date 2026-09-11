s = 0
[1, 2, 3, 4].each do |x|
  next if x == 2
  s = s + x
end
s
