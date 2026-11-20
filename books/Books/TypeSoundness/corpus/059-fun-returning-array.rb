# typed: true
extend T::Sig
sig { params(x: Integer, y: Integer).returns(T::Array[Integer]) }
def make_pair(x, y)
  [x, y]
end
make_pair(1, 2)
