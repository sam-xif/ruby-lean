class C
  def foo; "orig"; end
end
c = C.new
puts c.foo
c.singleton_class.class_eval do
  define_method(:foo) { "singleton " + super() }
end
puts c.foo
puts C.new.foo
