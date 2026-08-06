# typed: strict
require "sorbet-runtime"
extend T::Sig

sig { params(x: Integer).returns(String) }
def stringify(x)
  x.to_s
end

puts stringify(1)
puts stringify("two")
