# The `Integer#truncate` shapes around CRuby's Fixnum boundary that the model
# still answers, and the remainders that keep the gate in
# `integer-truncate-bignum-exact-multiple` exact.
#
# CRuby's `rb_int_truncate` truncates a Fixnum receiver directly and takes the
# Bignum path only past `FIXNUM_MIN = -(2**62)`. On that path it computes
# `m = num mod f` and, below zero, answers `num + (f - m)`: an exact multiple
# (`m = 0`) overshoots by one granularity, which the model declines, and every
# other remainder lands on the multiple truncation wants. So the whole family is
# pinned from both sides — remainder 0 declines only past the boundary, and
# remainders 1, `f/2` and `f - 1` answer everywhere.

# Past the boundary (a Bignum), remainders 1, f/2 and f-1.
p [(-(2**62) * 10 - 1).truncate(-1), (-(2**62) * 10 - 5).truncate(-1), (-(2**62) * 10 - 9).truncate(-1)]
p [(-(10**19) * 10**20 - 1).truncate(-20), (-(10**19) * 10**20 - 5 * 10**19).truncate(-20),
   (-(10**19) * 10**20 - (10**20 - 1)).truncate(-20)]

# At and above the boundary the receiver is still a Fixnum, so an exact multiple
# of the granularity is answered exactly, overshoot or not.
p [(-(2**62) + 4).truncate(-1), (-500).truncate(-2), (-555).truncate(-1), (-555).truncate(-2)]

# A positive receiver signs the same Bignum expression the other way and never
# overshoots: exact multiples and remainders both.
p [(10**19).truncate(-1), (10**19 + 1).truncate(-1), (10**19 + 5).truncate(-1), (10**19 + 9).truncate(-1)]
p [(10**30).truncate(-20), (10**30).truncate(-30)]

# A granularity with more digits than the receiver cannot divide it, so the
# answer is zero and nothing is declined.
p [(-(10**19)).truncate(-20), (-(2**62) - 6).truncate(-20), (-(10**19)).truncate(-30)]
