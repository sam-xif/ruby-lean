# typed: true
require "sorbet-runtime"
extend T::Sig

sig { returns(T.proc.params(a: String, b: String).returns(Integer)) }
def comparator_for
  tiebreak = 0
  cmp = ->(a, b) { "wrong" }
  cmp
end

def use_comparator
  cmp = comparator_for
  cmp.call("foo", "barbaz")
end

use_comparator
