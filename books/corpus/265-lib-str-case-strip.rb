# typed: true
s = "  Foo  "
t = s.strip
if t.empty?
  ""
else
  t.upcase + t.downcase
end
