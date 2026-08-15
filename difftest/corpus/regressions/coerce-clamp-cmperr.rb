# L123. Two things the coerce protocol reached that were wrong here:
# `Comparable#clamp` skipped CRuby's up-front `min <=> max` check (so a coercible
# `min` made it *return the argument*, and `3.clamp(9, 1)` answered 9), and the
# `comparison of X with Y failed` message was a hand-written copy that rendered a
# Float argument as "Float" where CRuby shows its value.
class Cmp
  def coerce(other) = [other, 4]

  def inspect = "#<Cmp>"
end

class Tok
  include Comparable

  def initialize(n)
    @n = n
  end

  def <=>(other) = other.is_a?(Tok) ? (@n <=> other.n) : nil

  def n = @n

  def inspect = "#<Tok>"
end

begin
  puts(3.clamp(9, 1).inspect)
rescue StandardError => e
  puts("#{e.class}: #{e.message}")
end
begin
  puts(3.clamp(Cmp.new, 9).inspect)
rescue StandardError => e
  puts("#{e.class}: #{e.message}")
end
puts(3.clamp(1, Cmp.new).inspect)
puts(3.clamp(5, 5).inspect)
puts(3.between?(Cmp.new, 9).inspect)
puts(3.between?(9, 1).inspect)

[1.5, 2, :a, nil, true, "a", 0.25].each do |arg|
  begin
    puts(Tok.new(1) < arg)
  rescue StandardError => e
    puts("#{e.class}: #{e.message}")
  end
  begin
    puts(Tok.new(1).clamp(arg, 9).inspect)
  rescue StandardError => e
    puts("#{e.class}: #{e.message}")
  end
end
puts(Tok.new(1).clamp(Tok.new(2), Tok.new(3)).inspect)
puts(Tok.new(1).between?(Tok.new(0), Tok.new(3)).inspect)
