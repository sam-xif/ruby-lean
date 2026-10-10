# typed: true
extend T::Sig
sig { params(flag: T::Boolean).returns(T.any(Integer, String)) }
def pick(flag)
  if flag
    1
  else
    "s"
  end
end

v = pick(false)
case v
when Integer
  v * 2
when String
  v + v
end
