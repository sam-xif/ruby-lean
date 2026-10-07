# typed: true
extend T::Sig
sig { params(ns: Integer).returns(Integer) }
def total(*ns)
  ns.inject(0) { |a, b| a + b }
end

total(1, 2, 3) + total()
