class Foo
  define_method(:bar) { |x| x * 2 }
end
f = Foo.new
puts f.bar(21)
m = :bar
puts f.send(m, 5)
puts f.public_send(:bar, 10)
p Foo.instance_method(:bar).arity
