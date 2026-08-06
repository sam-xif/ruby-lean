# typed: true
require "sorbet-runtime"
extend T::Sig

sig { params(n: Integer).returns(Integer) }
def double(n)
  n * 2
end

def untyped_caller(v)
  double(v)
end

puts untyped_caller(21)
puts untyped_caller("x")
