# GATED — the coverage holes opened, deliberately, by teaching the model that a
# repr-sensitive method it cannot run *is* an override: `pureOk` seeing a singleton
# `inspect` (L128, the fix for `pureok-eigenclass.rb`) and `Exception#message`
# being `to_s` (L131). All three were **wrong answers** before and are refusals
# now, which is the direction §4.4 wants. All three are sites where a renderer must
# speak for a value and cannot dispatch.
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
#   3. An **uncaught** exception whose message is dispatched — the same site as (2).
#      The control observes `__exc.message`, and `Exception#message` is `to_s`
#      (L131), so a user `to_s` or `message` decides what the observation says.
#      Reading the payload was a wrong answer; this refuses. Every *rescued* form
#      agrees and is guarded in `exception-repr.rb`.
#
# Closing (2) and (3) means letting the observation dispatch — a synthetic send on a
# machine that has already halted — which is a change to the observation contract
# rather than to a rule, and closes both at once. Closing (1) means a prelude twin
# that can raise with a dispatched message. Pinned so the choices stay visible: if
# any of the gates is ever closed this case starts testing itself.
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

# (3) — commented out rather than deleted, because it *is* the third instance of
# the same architectural hole and it has to be one line away from being run. Its
# gate would refuse the two shapes above, and a file that pins one thing pins less
# than a file that pins three.
#
#   class Loud < RuntimeError
#     def to_s = "LOUD"
#   end
#   raise Loud, "quiet"      # CRuby observes ("Loud", "LOUD"); the model refuses
