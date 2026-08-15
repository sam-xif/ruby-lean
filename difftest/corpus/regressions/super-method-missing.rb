# OPEN — a **wrong answer**. `super` inside a user `method_missing` must reach
# `BasicObject#method_missing`, which raises the ordinary
# `NoMethodError: undefined method 'X' for an instance of C`. The model has no such
# method, so `super` fails on its own terms and the program sees
# `NoMethodError: super: no superclass method 'method_missing' …` instead.
#
# `def method_missing(n, *a) = handled?(n) ? … : super` is *the* idiomatic way to
# write one — anything else swallows every typo in the class — so this is not an
# exotic shape. It was found while fixing L130, where the same defect one name over
# (`super` inside a user `respond_to_missing?`) was in the way of the
# `Integer(obj)` conversion protocol; that one is fixed, because a default
# `Object#respond_to_missing?` is a two-line builtin.
#
# This one is not, and the reason is worth recording: making
# `BasicObject#method_missing` a builtin puts the model's **whole dispatch-miss
# path** through a method-table entry, since `lookup` would then always find a
# `method_missing` to dispatch. The message that path produces today is exact
# (L124's `receiverDesc`), so the change is a refactor of the miss path rather than
# a new rule, and it has to reproduce that message from inside a builtin.
def show(label)
  v = yield
  puts("#{label} => #{v.inspect.gsub(/0x[0-9a-f]+/, '0xADDR')}")
rescue StandardError => e
  puts("#{label} => #{e.class}: #{e.message.gsub(/0x[0-9a-f]+/, '0xADDR')}")
end

class Handler
  def method_missing(name, *args)
    return "handled #{name}" if name.to_s.start_with?("go_")

    super
  end

  def respond_to_missing?(name, include_private = false)
    name.to_s.start_with?("go_") || super
  end
end

show("handled")        { Handler.new.go_left }
show("unhandled")      { Handler.new.nope }
# NB: no `respond_to?` call here, deliberately. The model **gates** on
# `respond_to?` when the receiver has a user `respond_to_missing?`
# (`Interp/Reflect.lean` — a builtin cannot dispatch it), and a gate anywhere
# refuses the whole program, so one would hide every wrong answer in this file.
# That gate is now cheaper to close than it was: a prelude twin for `respond_to?`
# can dispatch, and L130 gave it a default `Object#respond_to_missing?` to fall
# back on.

# the same through `send`, and with arguments, which is where the message's shape
# matters
show("unhandled, args") { Handler.new.nope(1, 2) }
show("unhandled, send") { Handler.new.send(:nope) }

# a bare `super` with no user `respond_to_missing?`: the same defect, so the
# `respond_to_missing?` half is not what causes it
class Bare
  def method_missing(name, *args)
    name == :ok ? 1 : super
  end
end
show("bare handled")   { Bare.new.ok }
show("bare unhandled") { Bare.new.other }
