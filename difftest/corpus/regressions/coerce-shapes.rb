# L123. What `coerce` *answers* selects the error, and the arithmetic operators
# and the comparisons disagree about only one of the cases: a nil answer is
# "incomparable" for `<`/`<=>` but "coerce must return [x, y]" for `+`. A
# non-nil answer of the wrong shape raises in both.
class Bad
  def initialize(r)
    @r = r
  end

  def coerce(other)
    @r
  end

  def inspect = "#<Bad>"
end

[nil, 5, [5], [1, 2, 3], ["a", "b"]].each do |shape|
  ["+", "<", "<=>"].each do |op|
    begin
      puts("#{shape.inspect} #{op} => #{0.send(op, Bad.new(shape)).inspect}")
    rescue StandardError => e
      puts("#{shape.inspect} #{op} => #{e.class}: #{e.message}")
    end
  end
end

# nothing supplies `coerce` at all: the message names the operand CRuby's way —
# a special constant by value, everything else by class
class Plain
  def inspect = "#<Plain>"
end

[Plain.new, nil, :k, true, false, "s", [1], (1..2)].each do |v|
  begin
    puts(0 + v)
  rescue StandardError => e
    puts("#{e.class}: #{e.message}")
  end
  begin
    puts(0 < v)
  rescue StandardError => e
    puts("#{e.class}: #{e.message}")
  end
  puts((0 <=> v).inspect)
end
puts("end")
