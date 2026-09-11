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
if v.is_a?(Integer)
  v + "!"
else
  v + 1
end
