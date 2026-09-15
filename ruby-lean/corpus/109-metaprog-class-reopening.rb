# typed: true
class Foo
  extend T::Sig
  sig { returns(Integer) }
  def a
    1
  end
end

class Foo
  extend T::Sig
  sig { returns(Integer) }
  def b
    2
  end
end

Foo.new.a + Foo.new.b
