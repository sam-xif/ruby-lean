# typed: true
s = 0
[10, 20].each_with_index do |v, i|
  s = s + v + i
end
s
