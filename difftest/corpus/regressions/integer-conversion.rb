# FIXED in L130 — a guard now. `HANDOFF.md` §Known wrong answers 2 undersold it:
# this was not only a wrong error *class*, it was a wrong **answer**, and the
# String half was wrong too.
#
# `Kernel#Integer(obj)` for a non-String, non-numeric argument tries `to_int`,
# then `to_i`, and only then raises `TypeError: can't convert X into Integer`.
# The model raises `ArgumentError: invalid value for Integer()` — which is
# CRuby's message for an unparseable *String* — without trying either, so an
# object that defines `to_i` gets an exception where CRuby answers a number.
#
# The `Float(obj)` half used to gate (`unmodeled method Object#Float`) rather than
# answer, so it was out of this file. `Kernel#Float` is written now (L130) and is
# in, along with the three String-path defects found while writing the conversion
# half: the default base is **0**, not 10, so `Integer("0xff")` is 255 and
# `Integer("010")` is 8; and `_` is a digit separator, so `Integer("1_000")` is
# 1000. All three raised `ArgumentError`.
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

# the String path: three of these were wrong answers, not controls
show("integer")       { Integer(5) }
show("float")         { Integer(2.9) }
show("float negative"){ Integer(-2.9) }
show("hex prefix")    { Integer("0xff") }
show("octal by 0")    { Integer("010") }
show("binary prefix") { Integer("0b101") }
show("decimal prefix"){ Integer("0d19") }
show("underscores")   { Integer("1_000") }
show("double _")      { Integer("1__0") }
show("leading _")     { Integer("_1") }
show("prefix + base") { Integer("0xff", 16) }
show("prefix vs base"){ Integer("0xff", 10) }
show("octal + base 8"){ Integer("017", 8) }
show("radix 1")       { Integer("1", 1) }
show("radix 37")      { Integer("1", 37) }
show("base for int")  { Integer(5, 16) }
show("base for obj")  { Integer(WithToI.new, 16) }
show("exception:")    { Integer("zz", exception: false) }
show("whitespace")    { Integer("\t 42 \n") }

# `method_missing` can serve the conversion, and a **custom `respond_to_missing?`**
# is consulted first — which is what made the `to_str` probe that runs before
# `to_int` raise from inside the user's `super`
class WithMM
  def method_missing(n, *a) = n == :to_int ? 9 : super
  def respond_to_missing?(n, p = false) = n == :to_int || super
end
show("method_missing") { Integer(WithMM.new) }

# `Kernel#Float` — the same two rules with three differences [V]: no `to_str`, no
# base, and a *looser* String grammar than a Ruby float literal
class WithToF; def to_f = 1.5; end
class WithBadToF; def to_f = "no"; end
class WithToStr2; def to_str = "1.5"; end
show("Float to_f")    { Float(WithToF.new) }
show("Float bad to_f"){ Float(WithBadToF.new) }
show("Float neither") { Float(Plain.new) }
show("Float to_str")  { Float(WithToStr2.new) }
show("Float int")     { Float(5) }
show("Float string")  { Float("1.5") }
show("Float leading .") { Float(".5") }
show("Float trailing .") { Float("5.") }
show("Float exponent")  { Float("1E3") }
show("Float underscore"){ Float("1_0.5") }
show("Float bad")     { Float("zz") }
show("Float 1e")      { Float("1e") }
show("Float nil")     { Float(nil) }
show("Float true")    { Float(true) }
show("Float symbol")  { Float(:a) }
show("Float exception:") { Float("zz", exception: false) }
show("string")        { Integer("42") }
show("string base")   { Integer("ff", 16) }
show("bad string")    { Integer("zz") }
show("string spaces") { Integer("  7  ") }
