# ─── Range ──────────────────────────────────────────────────────────────────
#
# One `each` (plus `include Enumerable`) turns Range from an opaque value into a
# collection: `map`/`to_a`/`select`/`sum`/`each_with_index`/… all follow.

class Range
  include Enumerable

  # CRuby's `range_init` **validates the endpoints**: with both ends present,
  # `lo <=> hi` must answer non-nil, or it raises `ArgumentError: bad value for
  # range` [V]. Three details, each probed rather than assumed:
  #
  #   * only *non-nil* is required. An endpoint whose `<=>` answers `"junk"`
  #     builds a Range quite happily — the check is not "is this an Integer";
  #   * a **beginless or endless** range skips the check entirely, so `(nil..nil)`,
  #     `(nil.."a")` and `("a"..nil)` are all legal;
  #   * `<=>` is dispatched on the **left** endpoint, so `Range.new(D.new, 1)`
  #     succeeds where `Range.new(1, D.new)` raises, for a `D` whose `<=>`
  #     answers 0. A `<=>` that raises propagates.
  #
  # It is prelude Ruby because it *dispatches*; the arity error
  # comes out of this signature for free (`given 1, expected 2..3` [V]). Range
  # literals `a..b`/`a...b` desugar to this send, so they are checked too.
  def self.new(lo, hi, excl = false)
    raise ArgumentError, "bad value for range" if !lo.nil? && !hi.nil? && (lo <=> hi).nil?

    __range_new_unchecked(lo, hi, excl)
  end

  def each
    return __unsupported__("Enumerator: Range#each without a block") unless block_given?
    i = self.begin
    fin = self.end
    return __unsupported__("Range#each over a beginless/endless range") if i.nil? || fin.nil?
    if exclude_end?
      while i < fin
        yield(i)
        i = i.succ
      end
    else
      while i <= fin
        yield(i)
        i = i.succ
      end
    end
    self
  end

  def cover?(x)
    lo = self.begin
    hi = self.end
    return __unsupported__("Range#cover? over a beginless/endless range") if lo.nil? || hi.nil?
    return false if x < lo
    if exclude_end?
      x < hi
    else
      x <= hi
    end
  end

  def ===(x)
    cover?(x)
  end

  # `include?`/`member?` are `cover?` for numeric ranges but *iterate* for
  # non-numeric ones (`('a'..'z').include?('cc')` is false while `cover?` is
  # true), so restrict to the numeric case rather than guess.
  def include?(x)
    lo = self.begin
    unless lo.is_a?(Integer) || lo.is_a?(Float)
      return __unsupported__("Range#include? over a non-numeric range")
    end
    cover?(x)
  end
  alias member? include?

  def size
    lo = self.begin
    hi = self.end
    unless lo.is_a?(Integer) && hi.is_a?(Integer)
      return __unsupported__("Range#size over a non-Integer range")
    end
    n = exclude_end? ? hi - lo : hi - lo + 1
    n < 0 ? 0 : n
  end
  alias count size
end

