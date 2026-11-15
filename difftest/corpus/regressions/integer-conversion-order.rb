# #158: `Kernel#Integer` is `rb_convert_to_integer`, and the order of its probes
# is observable. With no base it is `to_int`, then `to_str`, then `to_i`; with a
# base it is `rb_check_string_type` alone, refusing every non-String. The prelude
# asked `to_str` first in both cases, so an object defining both conversions
# converted through its String.
#
# Everything here is rescued so one wrong answer does not take the program with
# it, and object addresses are normalised: `ArgumentError` messages name the
# converted String or the class, never the object id.
def show(label)
  puts("#{label} => #{yield.inspect.gsub(/0x[0-9a-f]+/, '0xADDR')}")
rescue StandardError => e
  puts("#{label} => #{e.class}: #{e.message.gsub(/0x[0-9a-f]+/, '0xADDR')}")
end

class Both
  def to_int = 7
  def to_str = "42"
end

# `to_int` answers, so `to_str` is never reached and the unparseable String it
# would have returned does not matter.
class BothBad
  def to_int = 7
  def to_str = "zz"
end

class StrOnly; def to_str = "0x1f"; end
class IntOnly; def to_int = 9; end
class ToIOnly; def to_i = 5; end
class BadToI;  def to_i = "x"; end
class BadToInt; def to_int = "3"; end
class BadToStr; def to_str = 42; end
class BadStr;  def to_str = "zz"; end
class SubStr < String; def to_int = 7; end

# The `to_int` probe runs under `rb_protect`, so a raise from it is swallowed and
# the conversion carries on to `to_i` — for any exception class.
class RaisingToInt
  def to_int = raise "from to_int"
  def to_i = 9
end

class RaisingToIntOnly
  def to_int = raise Exception, "from to_int"
end

class RaisingToI
  def to_i = raise "from to_i"
end

show("both")             { Integer(Both.new) }
show("both-exception")   { Integer(Both.new, exception: false) }
show("both-bad")         { Integer(BothBad.new) }
show("both-bad-exc")     { Integer(BothBad.new, exception: false) }
show("str-only")         { Integer(StrOnly.new) }
show("int-only")         { Integer(IntOnly.new) }
show("to-i-only")        { Integer(ToIOnly.new) }
show("bad-to-i")         { Integer(BadToI.new) }
show("bad-to-int")       { Integer(BadToInt.new) }
show("bad-to-str")       { Integer(BadToStr.new) }
show("bad-to-str-exc")   { Integer(BadToStr.new, exception: false) }
show("bad-str")          { Integer(BadStr.new) }
show("bad-str-exc")      { Integer(BadStr.new, exception: false) }
show("substr")           { Integer(SubStr.new("12")) }

# A String is parsed before any conversion is probed, even a String subclass that
# defines `to_int`.
show("substr-to-int")    { Integer(SubStr.new("12")) }

# `rb_protect(rb_check_to_int)`: a raising `to_int` is not an error, it is "no
# answer", and the conversion continues.
show("raising-to-int")   { Integer(RaisingToInt.new) }
show("raising-int-exc")  { Integer(RaisingToInt.new, exception: false) }
show("raising-only")     { Integer(RaisingToIntOnly.new) }
show("raising-only-exc") { Integer(RaisingToIntOnly.new, exception: false) }
show("raising-to-i")     { Integer(RaisingToI.new) }
show("raising-i-exc")    { Integer(RaisingToI.new, exception: false) }

# A base means "String only": `to_str` decides even when `to_int` is defined.
show("both-base")        { Integer(Both.new, 16) }
show("str-only-base")    { Integer(StrOnly.new, 16) }
show("substr-base")      { Integer(SubStr.new("12"), 8) }
show("bad-str-base")     { Integer(BadStr.new, 16) }
show("bad-str-base-exc") { Integer(BadStr.new, 16, exception: false) }
show("obj-base")         { Integer(Object.new, 16) }
show("obj-base-exc")     { Integer(Object.new, 16, exception: false) }
show("nil-base")         { Integer(nil, 16) }
show("float-base")       { Integer(3.9, 16) }
show("int-base")         { Integer(7, 16) }

# The String grammar is unchanged, including the base-0 prefix rules, and
# `exception: false` returns nil for a bad literal while an invalid radix raises
# either way (`invalid_radix` is not gated by that flag).
show("prefix-hex")       { Integer("0x1f") }
show("prefix-octal")     { Integer("010") }
show("prefix-binary")    { Integer("0b101") }
show("underscore")       { Integer("1_000") }
show("padded")           { Integer("  42  ") }
show("signed")           { Integer("-0x10") }
show("empty")            { Integer("") }
show("empty-exc")        { Integer("", exception: false) }
show("bad-literal-exc")  { Integer("zz", 16, exception: false) }
show("bad-radix-exc")    { Integer("42", 99, exception: false) }

show("nil")              { Integer(nil) }
show("nil-exc")          { Integer(nil, exception: false) }
show("true")             { Integer(true) }
show("symbol")           { Integer(:sym) }
show("float")            { Integer(3.9) }
show("nan-exc")          { Integer(Float::NAN, exception: false) }
show("infinity-exc")     { Integer(Float::INFINITY, exception: false) }

nil
