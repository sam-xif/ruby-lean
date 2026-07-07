counter = 0
klass = Class.new do
  define_method(:tick) { counter += 1 }
end
o = klass.new
puts o.tick
puts o.tick
o2 = klass.new
puts o2.tick
puts counter
