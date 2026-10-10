# b ** n by repeated multiplication: n multiplications.
class Power
  def initialize(base)
    @base = base
  end

  def raise_to(exponent)
    result = 1
    left = exponent
    while left > 0
      result = result * @base
      left = left - 1
    end
    result
  end
end

power = Power.new(3)
answer = power.raise_to(13)
puts answer
answer
