# typed: true
require "sorbet-runtime"
extend T::Sig

sig { params(h: T::Hash[String, Integer], k: String).returns(Integer) }
def fetch!(h, k)
  T.must(h[k])
end

puts fetch!({ "a" => 1 }, "a")
puts fetch!({ "a" => 1 }, "b")
