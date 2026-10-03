# typed: true
module Twice
  extend T::Sig
  sig { params(f: T.proc.params(arg0: Integer).returns(Integer), v: Integer).returns(Integer) }
  def self.apply(f, v)
    f.call(f.call(v))
  end
end


Twice.apply(lambda { |x| x + 1 }, 5)
