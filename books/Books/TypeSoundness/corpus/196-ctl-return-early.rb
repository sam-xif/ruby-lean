# typed: true
extend T::Sig
sig { params(a: T::Array[Integer], d: Integer).returns(Integer) }
def first_or(a, d)
  return d if a.empty?
  a[0]
end

first_or([], 9) + first_or([1], 9)
