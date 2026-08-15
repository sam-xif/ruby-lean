# L123. `Integer#==`/`Float#==` do not coerce: they hand the comparison to the
# argument (`rb_equal(y, x)`) and reduce its answer to a boolean, so a user `==`
# decides and a `5` means `true`. `!=` follows, being the negation of `==`.
class Truthy
  def ==(other) = 5

  def inspect = "#<Truthy>"
end

class Falsy
  def ==(other) = nil

  def inspect = "#<Falsy>"
end

class Plain
  def inspect = "#<Plain>"
end

[Truthy.new, Falsy.new, Plain.new].each do |o|
  puts((0 == o).inspect)
  puts((0 != o).inspect)
  puts((0.0 == o).inspect)
  puts((0.0 != o).inspect)
  puts((o == 0).inspect)
  # `eql?` does *not* reverse [V]
  puts(0.eql?(o).inspect)
end
puts("end")
