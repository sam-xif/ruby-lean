# typed: true
class Integer
  extend T::Sig
  sig { params(c: T.untyped).returns(String) }
  def is_a?(c)
    "s"
  end
end
5.is_a?(Integer) & true
