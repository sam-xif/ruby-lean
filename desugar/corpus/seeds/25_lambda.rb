# `->` lambda literal desugars to a lambda-send (rule lambda->send). Strict arity,
# call returns the body value.
f = ->(a, b) { a + b }
g = -> { 42 }
print(f.call(3, 4))
print(g.call)
f.call(1, 2)
