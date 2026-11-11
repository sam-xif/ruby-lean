# typed: true
extend T::Sig
sig { params(b: T.proc.params(x: Integer).returns(Integer)).returns(Integer) }
def run(&b)
  copy = b
  b = nil
  copy.call(5)
  copy = nil
  yield(7)
end

total = 0
run { |value| total = total + value }
total
