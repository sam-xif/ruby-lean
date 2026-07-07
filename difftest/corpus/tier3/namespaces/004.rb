@x
puts @x.inspect
puts defined?(@x)
@x = nil
puts defined?(@x)
y = 1 if false
puts y.inspect
puts defined?(y)
puts defined?(z)
y
