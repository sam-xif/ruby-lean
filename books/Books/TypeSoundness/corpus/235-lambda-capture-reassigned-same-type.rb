# typed: true
x = 1
f = lambda { x }
x = 2
f.call + 1
