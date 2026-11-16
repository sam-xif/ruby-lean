# `Integer#truncate` with a negative count on a **negative Bignum** that is an
# exact multiple of the granularity `f = 10**-ndigits`.
#
# CRuby's `rb_int_truncate` takes the Bignum path as soon as the receiver is past
# `FIXNUM_MIN`: it computes `m = num mod f` (always in `[0, f)`) and then, below
# zero, answers `num + (f - m)`. For an exact multiple `m` is 0, so the answer
# moves one granularity *away from zero* instead of staying put —
# `(-(10**19)).truncate(-1)` is -9999999999999999990, not -(10**19), and
# `(-(10**30)).truncate(-30)` is 0.
#
# Reproducing that means modelling CRuby's Fixnum/Bignum split, a word-size fact
# about the oracle rather than about Ruby, so the model declines these shapes
# with a named reason instead of answering them. Every other truncate shape
# (positive receivers, Fixnum receivers, and Bignums whose remainder is not zero)
# still answers: see `integer-truncate-bignum-remainders`.
p (-(10**19)).truncate(-1)
p (-(2**62) * 10).truncate(-1)
p (-(10**30)).truncate(-1)
p (-(10**30)).truncate(-20)
p (-(10**30)).truncate(-30)
# just past the Fixnum boundary, and an exact multiple of the granularity
p (-(2**62) - 6).truncate(-1)
