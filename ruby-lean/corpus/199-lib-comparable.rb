# typed: true
class Rev
  extend T::Sig
  include Comparable

  sig { params(n: Integer).void }
  def initialize(n)
    @n = n
  end

  sig { returns(Integer) }
  def n
    @n
  end

  sig { params(other: Rev).returns(Integer) }
  def <=>(other)
    n <=> other.n
  end
end

r = Rev.new(1)
s = Rev.new(2)
[r < s, r > s, r.between?(r, s), r.clamp(r, s).n].length
