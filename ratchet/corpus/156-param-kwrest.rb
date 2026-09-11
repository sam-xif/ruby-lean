# typed: true
extend T::Sig
sig { params(kw: T.untyped).returns(Integer) }
def opts(**kw)
  kw["a"].nil? ? 0 : 1
end

opts(a: 1)
