# OPEN — `HANDOFF.md` §Known wrong answers 1. CRuby never lets a non-String out
# of `rb_obj_as_string`: it calls `to_s`, and **if the result is not a String it
# falls back to the default `#<C:0x…>` form** (`rb_any_to_s` — the same function
# L124 added as `Heap.anyToS`). The model uses whatever `to_s` returned.
#
# `rb_inspect` is the same shape one level up: a non-String from `inspect` gets
# `to_s` called *on the result*, which is why `p` prints `1` rather than raising.
#
# Where the fix goes (both halves are small; the ratchet round is the cost):
#   * the desugarer's `as_string` (C30) lowers interpolation to
#     `t = e; String === t ? t : t.to_s` and needs the second test:
#     `u = t.to_s; String === u ? u : t.__to_s_slow`;
#   * the prelude twins that do the same in Ruby — `__join_slow`, `__puts_slow`,
#     `__print_slow`, `__p_slow` — where `__to_s_slow` already *is* `rb_any_to_s`.
#
# NOT in this file, deliberately: `puts obj` and `print obj`, which the model
# **gates** (`__write of a non-String`). A gate anywhere refuses the whole
# program, and this file exists to reproduce wrong answers. Add those two lines
# when the fix lands — they are the cheapest check that the twins were fixed too.
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
