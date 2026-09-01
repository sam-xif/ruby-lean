class Foo
  def a
    1
  end
end

class Foo
  def b
    2
  end
end

Foo.new.a + Foo.new.b
