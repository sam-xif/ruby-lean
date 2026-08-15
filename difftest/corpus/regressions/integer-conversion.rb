# OPEN — `HANDOFF.md` §Known wrong answers 2, which undersold it: this is not
# only a wrong error *class*, it is a wrong **answer**.
#
# `Kernel#Integer(obj)` for a non-String, non-numeric argument tries `to_int`,
# then `to_i`, and only then raises `TypeError: can't convert X into Integer`.
# The model raises `ArgumentError: invalid value for Integer()` — which is
# CRuby's message for an unparseable *String* — without trying either, so an
# object that defines `to_i` gets an exception where CRuby answers a number.
#
# The `Float(obj)` half gates (`unmodeled method Object#Float`) rather than
# answering, so it is out of this file: a gate would refuse the whole program.
def show(label)
  puts("#{label} => #{yield.inspect}")
rescue StandardError => e
  puts("#{label} => #{e.class}: #{e.message}")
end

class WithToI
  def to_i = 5
end

class WithToInt
  def to_int = 7
end

class WithBoth
  def to_i = 5
  def to_int = 7        # `to_int` wins [V]
end

class WithBadToInt
  def to_int = "no"
end

class Plain
  def inspect = "#<Plain>"   # fixed inspect: no address in the observation (N38)
end

show("to_i")          { Integer(WithToI.new) }
show("to_int")        { Integer(WithToInt.new) }
show("both")          { Integer(WithBoth.new) }
show("to_int wrong")  { Integer(WithBadToInt.new) }
show("neither")       { Integer(Plain.new) }
show("nil")           { Integer(nil) }
show("true")          { Integer(true) }
show("symbol")        { Integer(:sym) }
show("array")         { Integer([1]) }

# the cases the model already gets right, as controls
show("integer")       { Integer(5) }
show("float")         { Integer(2.9) }
show("string")        { Integer("42") }
show("string base")   { Integer("ff", 16) }
show("bad string")    { Integer("zz") }
show("string spaces") { Integer("  7  ") }
