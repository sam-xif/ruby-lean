class A
  def foo(x)
    "A#foo(#{x})"
  end
end
class B < A
  def foo(x)
    x = x * 2
    super
  end
end
puts B.new.foo(5)
puts B.new.foo(3)
