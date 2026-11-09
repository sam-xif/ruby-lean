# #109. `String#strip` removed only space, "\t", "\n" and "\r" (Lean's
# `trimAscii`), so NUL, "\v" and "\f" stayed attached; CRuby's set is
# " \t\n\v\f\r" plus NUL, and nothing else.
#
# The matrix over all 256 bytes, not just the seven characters, is the point:
# "nothing else is stripped" — high bytes, the C1 controls \x1c-\x1e, Unicode
# whitespace — is checked in the same breath.

left = []
right = []
both = []
(0..255).to_a.each do |b|
  ch = b.chr
  left << b if (ch * 2 + "a").strip == "a"
  right << b if ("a" + ch * 2).strip == "a"
  both << b if (ch * 2 + "a" + ch * 2).strip == "a"
end
p left
p right
p both

p ["\0a\0".strip, "\0".strip, "\0\0a".strip, "a\0".strip, "\0a\0".strip.length]
p ["\va\f".strip, "\v".strip, "\f\f".strip, "\t\n\v\f\r\0a\r\0\v\f\n\t".strip]
p ["a\0b".strip, "a\0b".strip.bytes, "\0a\0b\0".strip.bytes]
p ["\x1ca\x1c".strip, "\x1da\x1d".strip, "\x1ea\x1e".strip]
p ["".strip, " ".strip, "\t \0".strip.empty?, "\0\0".strip.length]
p ["\u00a0a\u00a0".strip, "\u3000a\u3000".strip, "éaé".strip]
p ["\u0085a\u0085".strip, "\u2028a\u2028".strip]

# the encoding tag is inherited, and a high byte is never stripped
high = 0xC3.chr.b
p [(high * 2 + "a" + high * 2).strip.bytes, (high * 2 + "a" + high * 2).strip.encoding.name]
p [("\0a\0".b).strip, ("\0a\0".b).strip.encoding.name]

# a frozen receiver is not mutated and the answer is a new String
p [(" a ".freeze).strip, (" a ".freeze).strip.frozen?]
s = " a "
p [s.strip == "a", s.strip.equal?(s), s]
