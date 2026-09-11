def h
  p = proc { |y| return "s" }
  x = [1].map(&p)
  1
end
h + 1
