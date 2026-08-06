# typed: true
require "sorbet-runtime"
extend T::Sig

sig { params(x: T.untyped).returns(Integer) }
def as_int(x)
  T.cast(x, Integer)
end

puts as_int(1)
puts as_int("nope")
