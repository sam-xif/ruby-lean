# OPEN, and expected to report **gated** rather than still_open — the model
# refuses this program rather than answering it (`HANDOFF.md` §Known wrong
# answers 4). Filed anyway, for the reason N41 gives: if the gate is ever closed
# the case starts testing itself, and a gate nobody pinned is a gate nobody
# revisits.
#
# sorbet-runtime describes a value whose `inspect` is the *default* one by its
# `hash` rather than its inspect ("`#<Object:0x0…>` is ugly", says the gem). That
# hash is per-process seeded, so no implementation has a stable answer (N38) and
# L127 made the shim refuse instead of inventing one — it used to answer the
# `with value` form, which was simply wrong.
#
# What closing it would take: teaching the difftest observation to normalize
# `with hash <N>` the way it already normalizes `0x…` addresses, which is an
# amendment to N38's rule rather than a model change. The cost of not closing it
# is the whole program: any `sig` or `T.let` that fails on a plain object gates,
# and a plain object is the common shape in real code.
require "sorbet-runtime"

class Plain; end

begin
  T.let(Plain.new, Integer)
rescue TypeError => e
  # `sub` the hash away, so that a future normalization has something to compare:
  # the *shape* is stable even though the number is not.
  puts(e.message.sub(/with hash -?\d+/, "with hash N"))
end
