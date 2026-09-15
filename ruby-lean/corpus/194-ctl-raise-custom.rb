# typed: true
extend T::Sig
class Uncomparable < StandardError
end

sig { params(a: T.nilable(Integer)).returns(Integer) }
def cmp(a)
  raise Uncomparable if a.nil?
  1
rescue Uncomparable
  0
end

cmp(nil) + cmp(1)
