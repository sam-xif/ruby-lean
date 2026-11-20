# typed: true
extend T::Sig
sig { params(a: Integer, b: Integer).returns(Integer) }
def add(a, b)
  a + b
end

xs = [1, 2]
add(*xs)
