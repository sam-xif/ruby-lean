def foo
  "method foo"
end
foo = "local foo"
puts foo
puts foo()
puts defined?(foo)
puts defined?(foo())
def bar; "m"; end
bar = bar()
puts bar
bar
