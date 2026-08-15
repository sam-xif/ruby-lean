# GATED — the two coverage holes L128 opened, deliberately, by making `pureOk`
# see a singleton `inspect` (the fix for `pureok-eigenclass.rb`). Both were
# **wrong answers** before it and are refusals now, which is the direction §4.4
# wants; both are `inspectP` call sites, where pure repr must speak for a value
# and cannot dispatch.
#
#   1. `frozenErr` renders the receiver into `can't modify frozen C: <inspect>`.
#      CRuby dispatches `inspect` there. The model already gated for a
#      *class-level* override; L128 extends that to a singleton one, where it used
#      to answer `#<Plain:0x…>`.
#   2. `Obs.observe`'s `result_repr` is the same shape one layer out, and is the
#      architectural version: the program's final value is inspected **after the
#      program has ended**, where nothing can dispatch. `p o` at toplevel returns
#      `o`, so a program whose last value carries a singleton `inspect` now gates
#      on the observation even though its stdout is right.
#
# Closing (2) means letting the observation dispatch — a synthetic `inspect` send
# on a machine that has already halted — which is a change to the observation
# contract rather than to a rule. Closing (1) means a prelude twin that can raise
# with a dispatched message. Pinned so both choices stay visible: if either gate
# is ever closed this case starts testing itself.
class Plain; end

o = Plain.new
def o.inspect = "SING"
o.freeze
begin
  o.instance_variable_set(:@x, 1)
rescue StandardError => e
  puts("frozen, impure receiver => #{e.class}: #{e.message}")
end

a = [1]
def a.inspect = "SING"
a.freeze
begin
  a.push(2)
rescue StandardError => e
  puts("frozen, impure array => #{e.class}: #{e.message}")
end

# and the observation: the value this program *returns* is the impure object, so
# `result_repr` has to render it without a machine to dispatch in
r = Plain.new
def r.inspect = "SING"
r
