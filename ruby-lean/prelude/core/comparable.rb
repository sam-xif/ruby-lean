# ─── Comparable ─────────────────────────────────────────────────────────────

module Comparable
  # `==` via `<=>`, which the old global `reprPure` flag made impossible to put
  # here: defining `==` anywhere in the prelude turned pure repr off for the
  # whole program (retired in L103). Its absence was observable — Homebrew's
  # `Version::Token` mixes in Comparable and its specs compare a token to a
  # String, which fell through to `Object#==` (identity) and answered false.
  # A `<=>` of nil means "not comparable", which is `false`, not an error [V];
  # and CRuby swallows a StandardError from `<=>` here rather than propagating.
  def ==(other)
    c = begin
      self <=> other
    rescue StandardError
      nil
    end
    !c.nil? && c.zero?
  end

  # `cmp_between`: two dispatches of `>=`/`<=` on the *receiver*, which is why a
  # numeric receiver reaches its coerce protocol here (`3.between?(coercible, 9)`
  # answers rather than raising).
  def between?(min, max)
    self >= min && self <= max
  end

  # CRuby's `cmp_clamp`, and the order is the interesting part: the **min ≤ max**
  # check happens *first*, so `3.clamp(9, 1)` raises instead of answering 9, and
  # an incomparable pair raises about `min` and `max` rather than about the
  # receiver [V]. Both were wrong here before: this method used to compare with
  # `<`/`>` and skip the check entirely, which L123 turned from a latent bug into
  # a visible one — `3.clamp(coercible, 9)` coerced its way to a `true` and
  # *returned the argument*.
  # A **nil bound means "unbounded on that side"** and is skipped, checks
  # included — `Tok.new(1).clamp(nil, 9)` raises about `Tok` and `9`, not about
  # NilClass. `*bounds` rather than `(min, max = nil)` so that the one-argument
  # Range form stays distinguishable from an explicit nil max: it *gates* (CRuby
  # accepts a Range and this does not model it) instead of being silently read as
  # "no upper bound". A wrong arity gates for the same reason — CRuby's
  # ArgumentError there says `expected 1..2`, which is a message this cannot
  # produce while the Range form is unmodeled.
  def clamp(*bounds)
    return __unsupported__("Comparable#clamp with a Range") if bounds.length == 1
    return __unsupported__("Comparable#clamp arity (CRuby: 1..2)") unless bounds.length == 2

    min = bounds[0]
    max = bounds[1]
    if !min.nil? && !max.nil? && min.__cmpint(max) > 0
      raise ArgumentError, "min argument must be less than or equal to max argument"
    end
    return min if !min.nil? && __cmpint(min) < 0
    return max if !max.nil? && __cmpint(max) > 0

    self
  end

  def <(other) = __cmpint(other) < 0

  def <=(other) = __cmpint(other) <= 0

  def >(other) = __cmpint(other) > 0

  def >=(other) = __cmpint(other) >= 0
end

