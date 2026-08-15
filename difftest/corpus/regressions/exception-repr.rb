# FIXED in L131 — a guard. Every way of asking an exception what it says goes
# through **`to_s`**, and the model had it backwards in both directions:
#
#   * `Exception#message` *is* `to_s` in CRuby (`exc_message` is one `rb_funcall`),
#     so a user `to_s` shows through it. As a Lean builtin sharing `to_s`'s arm it
#     read the payload, and `E.new("boom").message` answered "boom" for a class
#     whose `to_s` says otherwise — and `inspect` did the same;
#   * a user **`message`** changes nothing about `to_s` or `inspect`, but `message`
#     was in `inspectSensitive`/`toSSensitive`, so the model *refused* four shapes
#     CRuby answers.
#
# `to_s`-on-an-Exception is repr-sensitive per **value**, not per sensitivity list
# (an exception inside an Array is rendered through its `to_s` too), so the test
# lives in `pureOk`'s `.exc` arm rather than in either list.
#
# Deliberately not here: an **uncaught** exception with a user `to_s`/`message`.
# The control observes `__exc.message`, which dispatches, and the model has no
# machine left to dispatch in once the program has ended — so it gates, and a gate
# would refuse this whole file. `impure-repr-gates.rb` carries that one.
def show(label)
  v = yield
  puts("#{label} => #{v.inspect.gsub(/0x[0-9a-f]+/, '0xADDR')}")
rescue StandardError => e
  puts("#{label} => #{e.class}: #{e.message.gsub(/0x[0-9a-f]+/, '0xADDR')}")
end

# a user `message`: invisible to everything, and the model used to refuse
class MsgOnly < RuntimeError
  def message = "OVER"
end
show("message, inspect")   { MsgOnly.new("boom").inspect }
show("message, to_s")      { MsgOnly.new("boom").to_s }
show("message, message")   { MsgOnly.new("boom").message }
show("message, p")         { p(MsgOnly.new("boom")) }
show("message, in array")  { [MsgOnly.new("boom")].inspect }
show("message, interp")    { "#{MsgOnly.new("boom")}" }
show("message, rescued")   do
  begin
    raise MsgOnly, "boom"
  rescue StandardError => e
    [e.message, e.to_s, e.inspect]
  end
end

# a user `to_s`: visible to all three, and the model used to answer the payload
class ToSOnly < RuntimeError
  def to_s = "OVER"
end
show("to_s, inspect")      { ToSOnly.new("boom").inspect }
show("to_s, to_s")         { ToSOnly.new("boom").to_s }
show("to_s, message")      { ToSOnly.new("boom").message }
show("to_s, p")            { p(ToSOnly.new("boom")) }
show("to_s, in array")     { [ToSOnly.new("boom")].inspect }
show("to_s, in a hash")    { { k: ToSOnly.new("boom") }.inspect }
show("to_s, as an ivar")   do
  class Holder; def initialize(e); @e = e; end; end
  Holder.new(ToSOnly.new("boom")).inspect
end
show("to_s, interp")       { "#{ToSOnly.new("boom")}" }
show("to_s, rescued")      do
  begin
    raise ToSOnly, "boom"
  rescue StandardError => e
    [e.message, e.to_s, e.inspect]
  end
end

# an empty `to_s` prints the bare class name, not `#<C: >` [V]
class EmptyToS < RuntimeError
  def to_s = ""
end
show("empty to_s, inspect") { EmptyToS.new("boom").inspect }
show("empty message")       { RuntimeError.new("").inspect }

# a user `inspect`, which only `inspect` sees
class InspectOnly < RuntimeError
  def inspect = "OVER"
end
show("inspect, inspect")   { InspectOnly.new("boom").inspect }
show("inspect, to_s")      { InspectOnly.new("boom").to_s }
show("inspect, message")   { InspectOnly.new("boom").message }

# a `to_s` that is not a String — the L129 rule, on an exception
class BadToS < RuntimeError
  def to_s = 1
end
show("bad to_s, message")  { BadToS.new("boom").message }
show("bad to_s, inspect")  { BadToS.new("boom").inspect }

# and the plain cases, as controls
show("plain inspect")      { RuntimeError.new("boom").inspect }
show("plain message")      { RuntimeError.new("boom").message }
show("plain to_s")         { RuntimeError.new("boom").to_s }
show("no message")         { RuntimeError.new.message }
show("in an array")        { [RuntimeError.new("boom")].inspect }
show("rescued builtin")    do
  begin
    1 / 0
  rescue StandardError => e
    [e.class.to_s, e.message, e.inspect]
  end
end
