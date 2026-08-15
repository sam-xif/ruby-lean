# FIXED in L129/C38 — a guard now. CRuby never lets a non-String out
# of `rb_obj_as_string`: it calls `to_s`, and **if the result is not a String it
# falls back to the default `#<C:0x…>` form** (`rb_any_to_s` — the same function
# L124 added as `Heap.anyToS`). The model uses whatever `to_s` returned.
#
# `rb_inspect` is the same shape one level up: a non-String from `inspect` gets
# `to_s` called *on the result*, which is why `p` prints `1` rather than raising.
#
# Where the fix went, in both halves:
#   * the desugarer's `as_string` (C30) lowered interpolation to
#     `t = e; String === t ? t : t.to_s`, and its cold arm is now `t.__as_string`
#     (C38) — one prelude definition of `rb_obj_as_string` instead of a second
#     inline copy of it, with a plain-Ruby twin in the round-trip's wrapper;
#   * the prelude twins that do the same in Ruby — `__join_slow`, `__puts_slow`,
#     `__print_slow`, `__p_slow` and the container `__inspect_slow`s — render
#     through `__as_string`/`__as_inspect` rather than a bare `to_s`/`inspect`.
#     `__to_s_slow` was *not* `rb_any_to_s` as the note here used to claim: on
#     Array/Hash/Range it is that class's own renderer, so the fallback is the new
#     `Object#__any_to_s` primitive (L129).
#
# `puts obj` and `print obj` were deliberately absent while this was open, because
# the model **gated** on them (`__write of a non-String`) and a gate anywhere
# refuses the whole program. They are in now (L129/C38), and they are the cheapest
# check that the prelude twins were fixed alongside the desugarer.
# Each observation is rescued: the wrong value escapes into the *enclosing*
# interpolation, so an unrescued line takes the whole program with it
# (`"x => " + 1` is a TypeError) and pins one defect instead of eight.
def show(label)
  puts("#{label} => #{yield.inspect}")
rescue StandardError => e
  puts("#{label} => #{e.class}: #{e.message}")
end

class BadToS
  def to_s = 1
end

class NilToS
  def to_s = nil
end

class SymToS
  def to_s = :sym
end

class BadInspect
  def inspect = 1
end

class BothBad
  def to_s = 1
  def inspect = 2
end

show("interp integer") { "#{BadToS.new}" }
show("interp nil")     { "#{NilToS.new}" }
show("interp symbol")  { "#{SymToS.new}" }
show("interp twice")   { "#{BadToS.new}#{BadToS.new}" }
show("join")           { [BadToS.new].join(",") }
show("join nested")    { [[BadToS.new]].join(",") }
show("p")              { p(BadInspect.new) }
show("p in an array")  { p([BadInspect.new]) }
show("p both bad")     { p(BothBad.new) }
show("inspect of arr") { [BadInspect.new].inspect }

# a `to_s` that answers a String subclass is fine and must stay fine
class SubToS
  class S2 < String; end
  def to_s = S2.new("sub")
end
show("string subclass") { "#{SubToS.new}" }

# and the ordinary cases, as controls
class GoodToS
  def to_s = "good"
  def inspect = "GOOD"
end
show("normal to_s")    { "#{GoodToS.new}" }
show("normal inspect") { p(GoodToS.new) }

# `puts`/`print`, which gated while this defect was open — the prelude-twin half of
# the fix, as opposed to the desugarer's interpolation half
show("puts")           { puts(BadToS.new) }
show("print")          { print(BadToS.new, "\n") }
show("puts an array")  { puts([BadToS.new, BadToS.new]) }

# `inspect` answering a non-String has `rb_obj_as_string` applied to **the result**,
# so a result whose own `to_s` is bad falls back to *its* default form [V]
class DeepInspect
  def inspect = BadToS.new
end
show("p, nested bad") { p(DeepInspect.new) }

# two more found by probing the fix, both pre-existing and neither about a bad
# `to_s`: `Array#to_s`/`Hash#to_s` *are* `inspect`, so their purity test is
# inspect-sensitivity (the model gated), and `join`'s separator goes through
# `StringValue`, not `to_s` (the model raised)
show("hash to_s")      { { a: BadInspect.new }.to_s }
show("array to_s")     { [BadInspect.new].to_s }
show("join sep")       { ["a", "b"].join("-") }
class String
  def to_s = 1
end
show("join sep, String#to_s redefined") { ["a", "b"].join("-") }
show("interp, String#to_s redefined")   { "#{"lit"}" }
