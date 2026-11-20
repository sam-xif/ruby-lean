# typed: true
extend T::Sig
sig { returns(Integer) }
def mixed
  total = nil
  total = yield(1)
  result = yield(2)
  total + result
end

total = 0
mixed { |x| total = total + x }
total
