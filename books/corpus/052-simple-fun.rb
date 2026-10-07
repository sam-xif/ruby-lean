# typed: true
extend T::Sig
sig { params(x: Integer, y: Integer).returns(Integer) }
def add(x, y)
  x + y
end
add(1, 2)
