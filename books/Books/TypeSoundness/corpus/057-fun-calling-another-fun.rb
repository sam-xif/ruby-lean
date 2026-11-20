# typed: true
extend T::Sig
sig { params(x: Integer).returns(Integer) }
def inc(x)
  x + 1
end
sig { params(x: Integer).returns(Integer) }
def twice(x)
  inc(inc(x))
end
twice(3)
