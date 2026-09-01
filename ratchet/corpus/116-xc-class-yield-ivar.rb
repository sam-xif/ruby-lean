class Counter
  def initialize(n)
    @n = n
  end

  def bump
    yield(@n)
  end
end


Counter.new(5).bump { |x| x + 1 }
