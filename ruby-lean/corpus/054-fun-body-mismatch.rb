# typed: true
extend T::Sig
sig { params(x: Integer).returns(Integer) }
def bad(x)
  x + true
end
bad(1)
