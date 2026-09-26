# plain if/else expression and a while loop
n = 5
result = if n > 3 then "big" else "small" end
count = 0
while count < n do
  count = count + 1
end
print("#{result}:#{count}")
