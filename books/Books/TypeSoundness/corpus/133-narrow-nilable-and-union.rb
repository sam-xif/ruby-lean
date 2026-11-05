# typed: true
arr = [1, "a"]
v = arr[0]
if v.is_a?(Integer)
  v + 1
else
  v + "!"
end
