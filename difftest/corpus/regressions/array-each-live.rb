# L273 / ratchet F53: Array#each reads the live array at an advancing index.
xs = [1, 2]
seen = []
result = xs.each do |x|
  seen << x
  xs << 3 if x == 2
end
p [seen, result.equal?(xs)]

xs = [1, 2, 3]
seen = []
xs.each do |x|
  seen << x
  xs.pop if x == 1
end
p seen

xs = [1, 2, 3]
seen = []
xs.each do |x|
  seen << x
  xs.shift if x == 1
end
p seen

xs = [1, 2, 3]
seen = []
xs.each do |x|
  seen << x
  xs[1] = 7 if x == 1
end
p seen

# Reassigning a captured variable does not replace the receiver being iterated.
xs = [1, 2]
original = xs
seen = []
result = xs.each do |x|
  seen << x
  xs = [8, 9]
end
p [seen, result.equal?(original), xs]

# Native iteration bypasses Ruby overrides of indexed access and length.
xs = [1, 2]
def xs.length; 0; end
def xs.[](index); 99; end
seen = []
xs.each { |x| seen << x }
p seen

xs = [1, 2]
seen = []
xs.each do |x|
  if x == 1
    xs.each do |y|
      xs << 3 if y == 2
      break if y == 3
    end
  end
  seen << x
end
p seen

# next advances; redo repeats the same yielded value even after an append.
xs = [1, 2]
seen = []
redone = false
result = xs.each do |x|
  if x == 1 && !redone
    redone = true
    xs << 3
    redo
  end
  next if x == 2
  seen << x
  break 42 if x == 3
end
p [seen, result]

def return_from_each
  [1, 2].each { |x| return x }
  99
end
p return_from_each
p [].each { raise "empty block ran" }
seen = []
begin
  [1, 2, 3].each do |x|
    seen << x
    raise "stop" if x == 2
  end
rescue RuntimeError
  p seen
end
