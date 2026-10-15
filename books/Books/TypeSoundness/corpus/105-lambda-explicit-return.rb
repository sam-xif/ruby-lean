# typed: true
extend T::Sig
sig { returns(Integer) }
def apply_twice
  doubler = ->(x) { return x * 2 }
  doubler.call(3)
end

apply_twice
