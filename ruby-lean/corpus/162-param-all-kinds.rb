# typed: true
extend T::Sig
sig { params(a: Integer, b: Integer, rest: Integer, c: Integer, d: Integer, kw: T.untyped, blk: T.untyped).returns(Integer) }
def f(a, b = 2, *rest, c:, d: 4, **kw, &blk)
  [a, b, rest.length, c, d, kw.length, blk.nil?].length
end

f(1, c: 3)
