# typed: true
extend T::Sig
sig { params(b: T.proc.params(x: Integer).returns(Integer)).returns(Integer) }
def run(&b)
  b.call(5)
end

run { |x| x + 1 }
