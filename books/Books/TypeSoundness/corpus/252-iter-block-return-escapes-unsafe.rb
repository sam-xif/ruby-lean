# typed: true
extend T::Sig
sig { returns(Integer) }
def h
  x = [1].map { |y| return "s" }
  1
end
h + 1
