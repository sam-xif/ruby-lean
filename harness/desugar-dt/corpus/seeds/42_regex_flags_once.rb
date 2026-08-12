# C33 regex literal fidelity: the `n` (NOENCODING) flag, and `/o` (compile-once).
# Homebrew's version.rb uses `/\A#{Token::PATTERN}\z/o` eight times, so `/o` is on the
# critical path and must not be silently dropped.

# Flags survive into Regexp.new's option word.
print("opts=#{[/a/.options, /a/i.options, /a/x.options, /a/m.options, /a/n.options,
               /a/imxn.options].inspect};")
print("match=#{("ABC" =~ /b/i).inspect},#{("a\nb" =~ /a.b/m).inspect},#{("ab" =~ / a b /x).inspect};")

# /o compiles once: the interpolation runs on the first evaluation only, and every later
# evaluation yields the *same object*.
$n = 0

def bump
  $n += 1
  "x"
end

def once_re = /\A#{bump}\z/o

a = once_re
b = once_re
print("once_calls=#{$n};")
print("once_same=#{a.equal?(b)};")
print("once_stale=#{once_re.source};")   # still "\\Ax\\z" though bump would now say "x" again

# Without /o the interpolation re-runs and a fresh object is built each time.
$m = 0

def each_time
  $m += 1
  "y"
end

def plain_re = /\A#{each_time}\z/

c = plain_re
d = plain_re
print("plain_calls=#{$m};")
print("plain_same=#{c.equal?(d)};")
print("plain_eq=#{c == d}")
[a.source, c.source]
