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
end
o = C.new
xs = [o, o.instance_variable_set(:@a, "s")]
xs[0].get + 1
