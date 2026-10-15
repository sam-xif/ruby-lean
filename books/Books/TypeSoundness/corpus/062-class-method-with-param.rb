# typed: true
class Counter
  extend T::Sig
  sig { params(n: Integer).void }
  def initialize(n)
    @n = n
  end

  sig { params(k: Integer).returns(Integer) }
  def add(k)
    @n + k
  end
end

c = Counter.new(10)
c.add(5)
