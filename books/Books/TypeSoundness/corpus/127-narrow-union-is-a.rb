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

v = pick(true)
if v.is_a?(Integer)
  v + 1
else
  v + "!"
end
