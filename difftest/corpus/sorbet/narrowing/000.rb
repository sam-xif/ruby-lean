# typed: strict
require "sorbet-runtime"
extend T::Sig

sig { params(s: T.nilable(String)).returns(Integer) }
def length_or_zero(s)
  return 0 if s.nil?
  s.length
end

puts length_or_zero("abcd")
puts length_or_zero(nil)
