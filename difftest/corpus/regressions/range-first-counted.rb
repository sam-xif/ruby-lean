# Issue #114 — `Range#first` is two methods behind one name, the mirror of
# `Range#last`. The counted form is `Enumerable#first(n)`, so an over-large `n`
# is the whole range and an endless range still answers; the bare form is
# `#begin`, except that a beginless range has no first element and raises
# `RangeError` *before* the arity check.
def show(label)
  r = begin
    yield.inspect
  rescue => e
    "#{e.class}: #{e.message}"
  end
  puts "#{label}: #{r}"
end

# The counted form.
show("counted")        { (1..5).first(2) }
show("counted-zero")   { (1..5).first(0) }
show("counted-exact")  { (1..5).first(5) }
show("counted-past")   { (1..5).first(9) }
show("excl-past")      { (1...5).first(9) }
show("excl-edge")      { (1...5).first(4) }
show("excl-over")      { (1...5).first(5) }
show("endless")        { (1..).first(2) }
show("endless-zero")   { (1..).first(0) }
show("descending")     { (5..1).first(2) }
show("empty-range")    { (1...1).first(5) }
show("negative-lo")    { (-3..-1).first(2) }
show("single")         { (0..0).first(2) }

# The bare form, and the endless range it allows.
show("bare")           { (1..5).first }
show("bare-excl")      { (1...5).first }
show("bare-endless")   { (1..).first }
show("bare-descending") { (5..1).first }

# The beginless range raises for every argument shape, because `rb_range_first`
# checks the begin before it scans the arguments.
show("beginless")      { (nil..5).first }
show("beginless-n")    { (nil..5).first(2) }
show("beginless-args") { (nil..5).first(1, 2) }
show("beginless-neg")  { (nil..5).first(-1) }
show("nil-endless")    { (nil...nil).first(1) }

# Argument shapes: arity, the negative count, and `NUM2LONG`'s bignum refusal.
show("too-many-args")  { (1..5).first(1, 2) }
show("negative-count") { (1..5).first(-1) }
show("bignum-count")   { (1..5).first(2**64) }
show("bignum-neg")     { (1..5).first(-2**64) }

# `#begin` keeps its arity: the counted form belongs to `#first` alone.
show("begin")          { (1..5).begin }
show("begin-arg")      { (1..5).begin(0) }
