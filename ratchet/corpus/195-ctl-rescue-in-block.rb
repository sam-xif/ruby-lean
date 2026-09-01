s = 0
[1, 0, 2].each do |d|
  s = s + (10 / d)
rescue ZeroDivisionError
  next
end
s
