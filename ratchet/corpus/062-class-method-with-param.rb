class Counter
  def initialize(n)
    @n = n
  end

  def add(k)
    @n + k
  end
end

c = Counter.new(10)
c.add(5)
