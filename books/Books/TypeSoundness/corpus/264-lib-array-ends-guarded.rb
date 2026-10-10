# typed: true
xs = [1, 2, 3]
x = xs.first
y = xs.last
if xs.empty?
  0
else
  (x.nil? ? 0 : x) + (y.nil? ? 0 : y)
end
