# typed: true
extend T::Sig
sig { params(b: T.proc.params(x: Integer).returns(Integer)).returns(Integer) }
def run(&b)
  b.call(2)
end

run { |x| x * 3 }
