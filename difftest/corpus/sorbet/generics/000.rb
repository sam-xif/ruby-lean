# typed: true
require "sorbet-runtime"
extend T::Sig

sig { params(xs: T::Array[Integer]).returns(Integer) }
def total(xs)
  xs.sum
end

puts total([1, 2, 3])
puts total(T.unsafe([1, "two"]))
