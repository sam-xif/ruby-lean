def t
  yield(1)
end

a = 1
t { |x| a = a + x }
a + 1
