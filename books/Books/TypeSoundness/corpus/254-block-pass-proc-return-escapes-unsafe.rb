# typed: true
extend T::Sig
sig { returns(Integer) }
def h
  p = proc { |y| return "s" }
  x = [1].map(&p)
  1
end
h + 1
