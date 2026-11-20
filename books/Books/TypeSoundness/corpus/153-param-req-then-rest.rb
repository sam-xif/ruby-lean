# typed: true
extend T::Sig
sig { params(first: Integer, rest: Integer).returns(Integer) }
def tag(first, *rest)
  first + rest.length
end

tag(1, 2, 3)
