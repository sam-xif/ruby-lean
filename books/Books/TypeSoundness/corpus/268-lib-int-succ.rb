# typed: true
i = 0
total = 0
while i < 3
  total += i.succ
  i = i.succ
end
total
