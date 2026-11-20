# `Kernel#format`'s flags and conversions.
#
# CRuby reads every flag the directive allows: `-` left-justifies, `0`
# zero-pads *after* the sign and the `#` base prefix, `+` and space give a
# non-negative number its sign, and `#` adds the base prefix. A numeric
# directive converts its argument the way `rb_Integer` does — a String is
# parsed with base 0, anything else goes through `to_int`/`to_i`, and what is
# left raises — so `%d` of `"0x10"` is 16 and of `nil` raises.
#
# A negative number in base 2, 8 or 16 is **two's complement**, which CRuby
# writes with an infinite leading digit run as `..`: `-255` in hex is `..f01`,
# `-1` is `..f`, and the `0` flag widens the digit run before the `..` is
# placed. The sign flags (`+`, space) turn that off and give the ordinary
# signed form `-0xff`.

FLAGS = ["", "-", "+", " ", "0", "#", "-0", "+0", " 0", "#0", "-#", "+ ", "-+", "-+0#"]
CONVS = %w[d i s x X o b]
VALUES = {
  "d" => [0, 42, -42, 1234567, -1234567],
  "i" => [0, 7, -7],
  "s" => ["", "ab", "abcdefgh"],
  "x" => [0, 255, 4095, 100000],
  "X" => [0, 255],
  "o" => [0, 8, 511],
  "b" => [0, 5, 255],
}

# Every flag set against every directive, at three widths.
FLAGS.each do |f|
  CONVS.each do |c|
    VALUES[c].each do |v|
      [0, 4, 10].each do |w|
        fmt = "%#{f}#{w.zero? ? '' : w}#{c}"
        puts fmt + " " + v.inspect + " => " + format(fmt, v).inspect
      end
    end
  end
end

# A negative receiver in every base, with and without the flags that select the
# two's-complement form, at widths that widen the digit run.
NEGATIVES = {
  "d" => [-1, -7, -255],
  "x" => [-1, -2, -7, -255, -4096],
  "X" => [-1, -255],
  "o" => [-1, -8, -511],
  "b" => [-1, -5, -4095],
}
FLAGS.each do |f|
  NEGATIVES.each do |c, vs|
    vs.each do |v|
      [0, 3, 6, 12].each do |w|
        fmt = "%#{f}#{w.zero? ? '' : w}#{c}"
        puts fmt + " " + v.to_s + " => " + format(fmt, v).inspect
      end
    end
  end
end

# A bare `%%` is the only form CRuby accepts; a flag or width on it is an error.
puts format("%%").inspect
["%5%", "%-5%", "%05%", "%#5%", "%+5%", "% 5%"].each do |fmt|
  begin
    puts fmt + " => " + format(fmt).inspect
  rescue ArgumentError => e
    puts fmt + " => ArgumentError: " + e.message
  end
end

# `rb_Integer` on the argument: a String is parsed with base 0, a Float
# truncates toward zero, and the rest raise with CRuby's class and message.
["010", "0x10", "0b11", "0o17", " 5 ", "5_0", "+5", "-5"].each do |s|
  puts "d " + s.inspect + " => " + format("%d", s).inspect +
       ", x => " + format("%x", s).inspect
end
[0.0, 2.9, -2.9, 100.0].each do |f|
  puts "d " + f.to_s + " => " + format("%d", f).inspect
end
["abc", "", "1.9", nil, true, false, :sym, [], {}, [1]].each do |v|
  begin
    puts "d " + v.inspect + " => " + format("%d", v).inspect
  rescue TypeError, ArgumentError => e
    puts "d " + v.inspect + " => " + e.class.to_s + ": " + e.message
  end
end

to_int = Object.new
def to_int.to_int
  8
end
puts "to_int => " + format("%d", to_int).inspect

to_str = Object.new
def to_str.to_str
  "12"
end
puts "to_str => " + format("%d", to_str).inspect

to_i = Object.new
def to_i.to_i
  7
end
puts "to_i => " + format("%d", to_i).inspect
