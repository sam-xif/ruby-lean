# Range#each steps its begin with `succ` and compares with `<=>`.
#
# Two defects in one method: a begin CRuby cannot step raised the NoMethodError
# of the `succ` call instead of CRuby's TypeError (and, for `each` with a block,
# only after yielding the first element); and the loop compared with `<`/`<=`,
# so an object that defines `succ` and `<=>` raised NoMethodError on `<` where
# CRuby iterates.

def attempt
  yield
  :no_error
rescue => e
  [e.class.to_s, e.message]
end

# A begin with no `succ`: a TypeError raised before anything is yielded, on the
# eager and the iterator forms alike.
p attempt { (1.0..2.0).each { |x| p x } }
p attempt { (1.0..2.0).map { |x| x } }
p attempt { (1.0..2.0).to_a }

# An Integer begin still iterates, and still respects a non-Integer end.
p attempt { (1..2.0).to_a }
p attempt { (1..3).each { |x| p x } }

# A begin that can be stepped and compared: CRuby's loop uses `<=>` only, so an
# object needs no `<` or `<=` (and no `Comparable`).
class Stepper
  attr_reader :n
  def initialize(n)
    @n = n
  end

  def succ
    Stepper.new(@n + 1)
  end

  def <=>(other)
    @n <=> other.n
  end
end

seen = []
(Stepper.new(1)..Stepper.new(1)).each { |x| seen << x.n }
p seen
seen = []
(Stepper.new(1)...Stepper.new(1)).each { |x| seen << x.n }
p seen
seen = []
(Stepper.new(1)..Stepper.new(3)).each { |x| seen << x.n }
p seen

# A `succ` that answers the receiver itself never advances. CRuby tests `<=>`
# before each step and yields the end value once after the loop, so this yields
# exactly one element and stops rather than spinning.
class FixedPoint
  def succ
    self
  end

  def <=>(other)
    0
  end
end

seen = []
(FixedPoint.new..FixedPoint.new).each { |x| seen << x.class.to_s }
p seen
seen = []
(FixedPoint.new...FixedPoint.new).each { |x| seen << x.class.to_s }
p seen
