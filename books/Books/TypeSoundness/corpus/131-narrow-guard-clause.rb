# typed: true
extend T::Sig
sig { params(a: T::Array[Integer]).returns(Integer) }
def first_or_zero(a)
  x = a[0]
  return 0 if x.nil?
  x + 1
end


first_or_zero([5])
