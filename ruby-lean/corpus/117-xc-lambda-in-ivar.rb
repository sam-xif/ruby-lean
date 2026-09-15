# typed: true
class Box
  extend T::Sig
  sig { params(f: T.proc.params(x: Integer).returns(Integer)).void }
  def initialize(f)
    @f = f
  end

  sig { params(v: Integer).returns(Integer) }
  def apply(v)
    @f.call(v)
  end
end


Box.new(lambda { |x| x * 2 }).apply(4)
