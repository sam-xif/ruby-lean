# `String#to_i` reads its radix argument. The model read every call as base 10,
# so `"ff".to_i(16)` answered 0 and `"10".to_i(2)` answered 10: a silent wrong
# answer, not a gate, on the method Ruby uses to read a hex string.
#
# CRuby's `to_i` is a lenient `rb_int_parse_cstr`: skip `rb_isspace` whitespace,
# take an optional sign, resolve the radix (`0` means "read the prefix"), then
# read digits, stopping at the first character that is not a digit in that
# radix. No digit at all is 0, never an error. `_` separates digits and is
# accepted only *between* two of them. An explicit base accepts only its own
# prefix, so `"0b11".to_i(16)` is `2833` and `"0x11".to_i(8)` is 0. A radix
# outside 0 and 2..36 is `ArgumentError: invalid radix N`, and a second
# argument is an arity error.
#
# The same prefix parsers skipped only ` \t\n\r`, so `"\v10".to_i` and
# `"\f1.5".to_f` answered 0. CRuby's `rb_isspace` set includes `\v` and `\f`.
def show(label)
  puts("#{label} => #{yield.inspect}")
rescue StandardError => e
  puts("#{label} => #{e.class}: #{e.message}")
end

show("hex")           { "ff".to_i(16) }
show("hex upper")     { "FF".to_i(16) }
show("from binary")   { "101".to_i(2) }
show("from octal")    { "17".to_i(8) }
show("from 36")       { "zz".to_i(36) }
show("letter prefix") { "abc".to_i(16) }

# An explicit base accepts only its own prefix
show("0x at 16")      { "0x1f".to_i(16) }
show("0x at 10")      { "0x1f".to_i(10) }
show("0b at 2")       { "0b101".to_i(2) }
show("0b at 16")      { "0b11".to_i(16) }
show("0o at 8")       { "0o17".to_i(8) }
show("0o at 16")      { "0o17".to_i(16) }
show("0d at 10")      { "0d19".to_i(10) }

# Base 0 reads the prefix, and a bare leading 0 is octal
show("auto hex")      { "0x1f".to_i(0) }
show("auto binary")   { "0b101".to_i(0) }
show("auto octal")    { "0o17".to_i(0) }
show("auto decimal")  { "0d19".to_i(0) }
show("auto bare 0")   { "017".to_i(0) }
show("auto digit 8")  { "08".to_i(0) }
show("auto 0189")     { "0189".to_i(0) }

# Lenient in every other way: a sign, whitespace, and a stop at the first
# character that is not a digit *in the radix*
show("signed")        { "  -ff".to_i(16) }
show("plus")          { "+10".to_i(2) }
show("stops")         { "ffzz".to_i(16) }
show("not a digit")   { "9".to_i(8) }
show("no digits")     { "nope".to_i(16) }
show("empty")         { "".to_i(16) }
show("vtab space")    { "\v10".to_i(2) }
show("formfeed space"){ "\f10".to_i(2) }
show("space set")     { " \t\n\v\f\r7".to_i(16) }

# `_` separates digits, and is only accepted between two of them
show("separators")    { "f_f".to_i(16) }
show("leading _")     { "_f".to_i(16) }
show("trailing _")    { "f_".to_i(16) }
show("double _")      { "1__0".to_i(2) }
show("after prefix")  { "0x_1f".to_i(16) }
show("after bare 0")  { "0_17".to_i(0) }

# Radix validation and arity
show("radix 1")       { "10".to_i(1) }
show("radix 37")      { "10".to_i(37) }
show("radix -1")      { "10".to_i(-1) }
show("radix 0")       { "10".to_i(0) }
show("two args")      { "10".to_i(2, 3) }

# The whitespace set is shared with `to_f`
show("to_f vtab")     { "\v1.5".to_f }
show("to_f formfeed") { "\f1.5".to_f }
show("to_f converted"){ "12abc".to_f }
