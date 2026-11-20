# typed: true
n = -7
s = "abc"
if n.odd? && s.end_with?("c")
  s.reverse + (n.abs + 1).to_s
else
  n.even? ? "even" : "odd"
end
