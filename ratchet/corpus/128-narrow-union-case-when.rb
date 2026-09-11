# typed: true
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
else
  0
end
