# typed: true
extend T::Sig
sig { params(n: Integer).returns(Integer) }
def fact(n)
  if n <= 1
    1
  else
    n * fact(n - 1)
  end
end
fact(4)
