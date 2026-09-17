# unless->if and until->while
i = 0
until i >= 3 do
  print(i)
  i = i + 1
end
puts("done") unless i == 0
i
