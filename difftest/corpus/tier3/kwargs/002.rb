def calc(a, b = a * 2, c = a + b)
  [a, b, c]
end
p calc(1)
p calc(1, 5)
p calc(1, 5, 10)
p calc(3)
