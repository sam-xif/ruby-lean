# L123. A real `coerce` runs and the operator is re-dispatched on the pair it
# returns — so the answer, the side effect, and a ZeroDivisionError raised *from
# the pair* all come from Ruby that the model used to never reach.
class Money
  def initialize(n)
    @n = n
  end

  def coerce(other)
    puts("coerce #{other.inspect}")
    [other, @n]
  end

  def inspect = "#<Money>"
end

puts((3 + Money.new(4)).inspect)
puts((3 - Money.new(4)).inspect)
puts((3 * Money.new(4)).inspect)
puts((12 / Money.new(4)).inspect)
puts((7 % Money.new(4)).inspect)
puts((2 ** Money.new(3)).inspect)
puts(7.divmod(Money.new(2)).inspect)
puts((3 < Money.new(4)).inspect)
puts((3 > Money.new(4)).inspect)
puts((3 <= Money.new(4)).inspect)
puts((3 >= Money.new(4)).inspect)
puts((3 <=> Money.new(4)).inspect)
puts((3 == Money.new(3)).inspect)
begin
  puts((3 / Money.new(0)).inspect)
rescue StandardError => e
  puts("#{e.class}: #{e.message}")
end
