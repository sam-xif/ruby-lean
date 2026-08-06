# typed: true
require "sorbet-runtime"
extend T::Sig

sig { params(x: Integer).returns(String).checked(:never) }
def label(x)
  "n=#{x}"
end

puts label(1)
puts label(T.unsafe("s"))
