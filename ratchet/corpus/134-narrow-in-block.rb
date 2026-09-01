t = [1, 2]
s = 0
t.each do |x|
  y = [10, 20][x]
  if y
    s = s + y
  end
end
s
