# typed: true
extend T::Sig
@a = "s"
sig { params(n: T.untyped).returns(Integer) }
def method_missing(*n)
  @a = 1
  2
end
x
@a + "b"
