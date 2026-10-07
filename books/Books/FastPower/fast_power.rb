# Exponentiation by squaring, with the work done by a small stateful object.
#
# `Power.new(b).raise_to(n)` computes b**n using O(log n) multiplications and
# counts the loop iterations it took in @steps.
class Power
  def initialize(base)
    @base = base
    @steps = 0
  end

  def steps
    @steps
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
      @steps = @steps + 1
    end
    result
  end
end

power = Power.new(3)
answer = power.raise_to(13)
puts answer
[answer, power.steps]
