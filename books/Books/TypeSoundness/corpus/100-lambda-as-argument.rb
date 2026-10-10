# typed: true
extend T::Sig
sig { params(f: T.proc.params(x: Integer).returns(Integer), v: Integer).returns(Integer) }
def apply(f, v)
  f.call(v)
end

apply(->(x) { x * 2 }, 5)
