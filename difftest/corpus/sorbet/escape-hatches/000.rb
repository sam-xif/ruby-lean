# typed: strict
require "sorbet-runtime"
extend T::Sig

sig { params(x: Integer).returns(Integer) }
def inc(x)
  x + 1
end

puts inc(1)
T.unsafe(nil).no_such_method
