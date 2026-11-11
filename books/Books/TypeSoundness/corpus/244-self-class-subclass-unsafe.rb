# typed: true
class C
  extend T::Sig
  sig { returns(T.class_of(C)) }
  def whoami
    self.class
  end
  sig { returns(Integer) }
  def tag
    1
  end
end
class D < C
  extend T::Sig
  sig { returns(String) }
  def tag
    "s"
  end
end
D.new.whoami.new.tag + 1
