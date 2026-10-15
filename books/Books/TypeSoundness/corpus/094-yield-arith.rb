# typed: true
extend T::Sig
sig { returns(Integer) }
def twice
  yield(1) + yield(2)
end

twice { |x| x * 10 }
