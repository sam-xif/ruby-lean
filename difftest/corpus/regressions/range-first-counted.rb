# Issue #114 — `Range#first` is two methods behind one name, the mirror of
# `Range#last`. The counted form is `Enumerable#first(n)`, so an over-large `n`
# is the whole range and an endless range still answers; the bare form is
# `#begin`, except that a beginless range has no first element and raises
# `RangeError` before the arity check.
#
# Deliberately absent: a non-Integer count (`(1..5).first(2.7)` is `[1, 2]`
# through `NUM2LONG`) and a range with non-Integer endpoints (`(1.0..5.0)` raises
# `can't iterate from Float` out of the class's own `each`). The model declines
# both with a named `Unsupported`, which would gate the whole program and leave
# this case pinning nothing.
def show(label)
  r = begin
    yield.inspect
  rescue => e
    "#{e.class}: #{e.message}"
  end
  puts "#{label}: #{r}"
end

# The counted form.
show("counted")         { (1..5).first(2) }
show("counted-zero")    { (1..5).first(0) }
show("counted-exact")   { (1..5).first(5) }
show("counted-past")    { (1..5).first(9) }
show("excl-past")       { (1...5).first(9) }
show("excl-edge")       { (1...5).first(4) }
show("excl-over")       { (1...5).first(5) }
show("endless")         { (1..).first(2) }
show("endless-zero")    { (1..).first(0) }
show("descending")      { (5..1).first(2) }
show("empty-range")     { (1...1).first(5) }
show("negative-lo")     { (-3..-1).first(2) }
show("single")          { (0..0).first(2) }

# The bare form, and the endless range it allows.
show("bare")            { (1..5).first }
show("bare-excl")       { (1...5).first }
show("bare-endless")    { (1..).first }
show("bare-descending") { (5..1).first }

# The beginless range raises for every argument shape, because `rb_range_first`
# checks the begin before it scans the arguments.
show("beginless")       { (nil..5).first }
show("beginless-n")     { (nil..5).first(2) }
show("beginless-args")  { (nil..5).first(1, 2) }
show("beginless-neg")   { (nil..5).first(-1) }
show("nil-endless")     { (nil...nil).first(1) }

# Argument shapes: arity, the negative count, `NUM2LONG`'s bignum refusal, and
# the preallocated array's own size limit (`ARY_MAX_SIZE`, `LONG_MAX /
# sizeof(VALUE)`, `2**60 - 1` on a 64-bit build). The array is allocated before
# the range is iterated, so a huge count refuses there rather than at `each`.
show("too-many-args")   { (1..5).first(1, 2) }
show("negative-count")  { (1..5).first(-1) }
show("bignum-count")    { (1..5).first(2**64) }
show("bignum-neg")      { (1..5).first(-2**64) }
show("long-min")        { (1..5).first(-2**63) }
show("below-long-min")  { (1..5).first(-2**63 - 1) }
show("above-long-max")  { (1..5).first(2**63) }
show("ary-too-big")     { (1..5).first(2**62) }
show("ary-long-max")    { (1..5).first(2**63 - 1) }
show("ary-too-big-nonint-range") { (1.0..5.0).first(2**62) }

# `#begin` keeps its arity of zero: the counted form belongs to `#first` alone.
show("begin")           { (1..5).begin }
show("begin-arg")       { (1..5).begin(0) }
