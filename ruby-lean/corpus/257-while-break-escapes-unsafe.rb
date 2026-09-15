# typed: true
i = 0
x = 1
while i < 2
  i = i + 1
  x = "s"
  break if i == 2
  x = 2
end
x + 1
