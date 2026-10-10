# typed: true
extend T::Sig
sig { returns(Integer) }
def lambda
  5
end
f = lambda { 1 }
f.call + 1
