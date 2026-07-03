# hash literal (mixed key kinds); return inside a def; break/next inside a block
def classify(n)
  return "zero" if n == 0
  return "neg" if n < 0
  "pos"
end

h = {name: "x", "count" => 3, 1 => :one}
sum = 0
[1, -2, 0, 5].each do |v|
  next if v == 0
  break if sum > 100
  sum += v
end
print([classify(-3), classify(0), classify(4), h, sum].inspect)
