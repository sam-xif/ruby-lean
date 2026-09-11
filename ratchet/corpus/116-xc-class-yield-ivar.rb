# typed: true
class Counter
  extend T::Sig
  sig { params(n: Integer).void }
  def initialize(n)
    @n = n
  end

  sig { returns(Integer) }
  def bump
    yield(@n)
  end
end


Counter.new(5).bump { |x| x + 1 }
