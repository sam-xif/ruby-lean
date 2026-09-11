s = 0
[1, 2].each do |y|
  s = "a"
  next if y == 2
  s = 1
end
s + 1
