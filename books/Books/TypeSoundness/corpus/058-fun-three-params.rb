# typed: true
extend T::Sig
sig { params(a: Integer, b: Integer, c: Integer).returns(Integer) }
def sum3(a, b, c)
  a + b + c
end
sum3(1, 2, 3)
