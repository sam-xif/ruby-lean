# OPEN — a **wrong answer**, not the gate `slice-gates.md` files it as. `pureOk`
# decides whether Lean's pure `Repr` may speak for a value by asking whether any
# ancestor of its class defines a repr-sensitive method. It asks about the
# **class**, so a method defined on the *object* — `def obj.inspect`, or an
# `extend` — is invisible to it, and the pure path renders the default
# `#<C:0x…>` while ignoring the override.
#
# This is exactly the L122 miss one level down (`pureOk` was not recursing into a
# Range's endpoints, and the pure path ignored a user `inspect` on one), which is
# why `HANDOFF.md` has been carrying it as "worth doing" for three sessions. It
# reproduces, so it belongs here rather than in the gates list.
#
# The fix: `reprOverridden` walks `ancestors (classOf …)`, which already starts at
# the eigenclass — but `pureOk` calls it with `(h.get o).klass`, the *real* class.
# `__user_defines?` was fixed for this in L115 (`classOf`, not `realClassOf`) and
# the purity path was not. Check both twins after changing it: `Repr` and the
# prelude's `__inspect_slow`.
def show(label)
  puts("#{label} => #{yield.inspect}")
rescue StandardError => e
  puts("#{label} => #{e.class}: #{e.message}")
end

class Plain; end

module Fancy
  def inspect = "MIXED"
end

show("singleton inspect, p") do
  o = Plain.new
  def o.inspect = "SING"
  p(o)
end

show("singleton inspect, in an array") do
  o = Plain.new
  def o.inspect = "SING"
  [o].inspect
end

show("singleton inspect, in a hash") do
  o = Plain.new
  def o.inspect = "SING"
  { k: o }.inspect
end

show("singleton inspect, in a range") do
  o = Plain.new
  def o.inspect = "SING"
  def o.<=>(other) = 0
  (o..o).inspect
end

show("extended inspect, p") do
  o = Plain.new
  o.extend(Fancy)
  p(o)
end

show("singleton inspect, as an ivar") do
  o = Plain.new
  def o.inspect = "SING"
  h = Plain.new
  h.instance_variable_set(:@x, o)
  h.inspect
end

# the class-level versions, which already work — the controls that say the defect
# is the *eigenclass*, not `inspect` dispatch in general
class WithInspect
  def inspect = "CLS"
end
show("class inspect, p")       { p(WithInspect.new) }
show("class inspect, array")   { [WithInspect.new].inspect }

# `to_s` through interpolation is an ordinary send, so it already dispatches to a
# singleton definition — the asymmetry is worth pinning, since a fix that routes
# `inspect` the same way should leave this alone
show("singleton to_s, interp") do
  o = Plain.new
  def o.to_s = "SING"
  "#{o}"
end
