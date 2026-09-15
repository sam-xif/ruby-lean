# typed: true
extend T::Sig
sig { params(a: Integer).returns(Integer) }
def f(a)
  a
end

f(1, 2)
