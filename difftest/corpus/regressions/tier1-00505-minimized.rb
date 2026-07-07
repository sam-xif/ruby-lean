def m0
  puts(0)
  false
end
def m1
  (a = 0)
  m0()
end
(a = (m0() && 0))
puts(0)
