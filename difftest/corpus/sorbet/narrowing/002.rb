# typed: true
require "sorbet-runtime"
extend T::Sig

sig { params(x: T.any(Integer, String)).returns(String) }
def render(x)
  return x.upcase if x.respond_to?(:upcase)
  x.to_s
end

puts render("ab")
puts render(3)
