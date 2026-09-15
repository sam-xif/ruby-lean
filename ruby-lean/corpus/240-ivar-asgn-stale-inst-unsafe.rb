# typed: true
class C
  extend T::Sig
  sig { void }
  def initialize
    @a = 1
  end
  sig { returns(Integer) }
  def get
    @a
  end
  sig { returns(Integer) }
  def leak
    x = self
    @a = "s"
    x.get + 1
  end
end
C.new.leak
