# b ** n by squaring: about log2(n) loop iterations instead of n.
class Power
  def initialize(base)
    @base = base
  end

  def raise_to(exponent)
    result = 1
    square = @base
    left = exponent
    while left > 0
      if left % 2 == 1
        result = result * square
      end
      square = square * square
      left = left / 2
    end
    result
  end
end

power = Power.new(3)
answer = power.raise_to(13)
puts answer
answer
