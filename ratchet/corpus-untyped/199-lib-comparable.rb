class Rev
  include Comparable

  def initialize(n)
    @n = n
  end

  def n
    @n
  end

  def <=>(other)
    n <=> other.n
  end
end

r = Rev.new(1)
s = Rev.new(2)
[r < s, r > s, r.between?(r, s), r.clamp(r, s).n].length
