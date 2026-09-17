# block-local variable (|x; t|) shadows the outer `t`, so the outer is untouched.
t = 100
[1, 2, 3].each { |x; t| t = x * 10 }
print(t)
t
