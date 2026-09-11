# typed: true
extend T::Sig
sig { returns(T.untyped) }
def m
  yield
end
sig { returns(Integer) }
def h
  m { return "s" }
  1
end
h + 1
