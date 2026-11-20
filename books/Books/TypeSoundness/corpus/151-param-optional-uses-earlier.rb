# typed: true
extend T::Sig
sig { params(s: String, n: Integer).returns(Integer) }
def pad(s, n = s.length)
  n
end

pad("abc")
