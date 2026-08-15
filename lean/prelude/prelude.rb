# frozen_string_literal: true

# The **prelude**: the part of Ruby's core library modeled in RubyCore itself
# rather than as Lean primitives (L62). Loaded from H₀ before the program under
# test; `scripts/gen_prelude.rb` desugars this file into `RubyCore/Prelude.lean`.
#
# Rules for authoring (the ratchet depends on them):
#
# 1. **Stay inside the desugar fragment and the Lean fragment.** Generation fails
#    loudly on the former; the latter shows up as gates at *call* time. `while`,
#    `if`, `yield`, `block_given?`, `def`, `alias`, arithmetic, `Array#[]`/`[]=`/
#    `push`/`length`, `Hash#[]`/`[]=` are all safe.
# 2. **Declare, never guess.** A form this code cannot model faithfully calls
#    `__unsupported__("reason")`, the builtin that returns the engine's
#    Unsupported gate — the RubyCore-level equivalent of `.unsupported` in Lean.
#    Blockless Enumerable calls (which CRuby answers with an `Enumerator`) are the
#    standard case.
# 3. **Repr-sensitive methods** (`to_s`, `inspect`, `==`, `eql?`, `message`,
#    `to_str`) are fine on a class this file *introduces* — `Pathname`, `Struct`,
#    `T::Struct`, `Encoding` all define them — because purity is a per-class
#    question (L103) and an impure receiver dispatches a prelude twin (L116).
#    Defining one on a class the model already renders (String, Array, Integer, …)
#    is still wrong: it makes every instance impure, and `Obs`'s `result_repr` is
#    computed after the program ends, where nothing can dispatch.
# 4. **A prelude method is the model of the CRuby builtin of that name** — it
#    suppresses the shadow gate for its own name (L62), so fidelity is on this
#    file. Match CRuby exactly, including the empty-receiver and tie cases.

# ─── BasicObject ────────────────────────────────────────────────────────────

class BasicObject
  # `!=` *is* the negation of `==` in Ruby, so it must **dispatch** `==` — a
  # builtin comparing payloads gets `ma != "a_"` wrong the moment a subclass
  # overrides `==` (test_yjit_115). One definition here covers every class.
  def !=(other)
    !(self == other)
  end
end

# ─── Kernel/Object ──────────────────────────────────────────────────────────

class Object
  # `===` is `==` for everything except Module (builtin), Range and Proc (below).
  def ===(other)
    self == other
  end

  def tap
    return __unsupported__("Enumerator: Object#tap without a block") unless block_given?
    yield(self)
    self
  end

  # `rb_cmpint`: `self <=> other`, with a nil — "not comparable" — turned into the
  # `ArgumentError: comparison of X with Y failed` that every comparison operator
  # except `==` raises [V]. The message comes from the `__cmp_failed` primitive so
  # that one rule names an operand (`coerceDesc`, L123): the hand-written copy
  # this replaces rendered a **Float argument as "Float"** where CRuby shows
  # `1.5`, which is the kind of drift a second copy buys.
  #
  # On Object rather than in Comparable because `clamp` needs it for its two
  # *arguments*, which need not be Comparable themselves.
  def __cmpint(other)
    c = self <=> other
    __cmp_failed(other) if c.nil?

    c
  end
end

class Proc
  # `case x when ->(v){…}` — Proc#=== calls the proc.
  def ===(other)
    call(other)
  end
end

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
  # answers rather than raising, L123).
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

# ─── Enumerable ─────────────────────────────────────────────────────────────
#
# Everything here is written against `each` alone, so one `each` per collection
# (Array/Hash natively, `Range#each` below, any user class) buys the whole module.
# Early exit uses `return` from inside the block (unwinds to this method's frame)
# or `break` (returns from `each`) — both already modeled (artifact 04 §4).

module Enumerable
  def to_a
    r = []
    each { |x| r.push(x) }
    r
  end
  alias entries to_a

  def map
    return __unsupported__("Enumerator: Enumerable#map without a block") unless block_given?
    r = []
    each { |x| r.push(yield(x)) }
    r
  end
  alias collect map

  def flat_map
    return __unsupported__("Enumerator: Enumerable#flat_map without a block") unless block_given?
    r = []
    each { |x|
      v = yield(x)
      if v.is_a?(Array)
        i = 0
        while i < v.length
          r.push(v[i])
          i = i + 1
        end
      else
        r.push(v)
      end
    }
    r
  end
  alias collect_concat flat_map

  def select
    return __unsupported__("Enumerator: Enumerable#select without a block") unless block_given?
    r = []
    each { |x| r.push(x) if yield(x) }
    r
  end
  alias filter select
  alias find_all select

  def reject
    return __unsupported__("Enumerator: Enumerable#reject without a block") unless block_given?
    r = []
    each { |x| r.push(x) unless yield(x) }
    r
  end

  def filter_map
    return __unsupported__("Enumerator: Enumerable#filter_map without a block") unless block_given?
    r = []
    each { |x|
      v = yield(x)
      r.push(v) if v
    }
    r
  end

  def find
    return __unsupported__("Enumerator: Enumerable#find without a block") unless block_given?
    each { |x| return x if yield(x) }
    nil
  end
  alias detect find

  def find_index(*a)
    if a.empty?
      return __unsupported__("Enumerator: Enumerable#find_index without a block") unless block_given?
      i = 0
      each { |x|
        return i if yield(x)
        i = i + 1
      }
      nil
    elsif a.length == 1
      target = a[0]
      i = 0
      each { |x|
        return i if x == target
        i = i + 1
      }
      nil
    else
      __unsupported__("Enumerable#find_index arity")
    end
  end
  # `Array#index` with a block is the same search (the blockless forms stay on
  # the builtin; the block form falls through to here, L63).
  alias index find_index

  def all?(*pat)
    return __unsupported__("Enumerable#all? with a pattern argument") unless pat.empty?
    if block_given?
      each { |x| return false unless yield(x) }
    else
      each { |x| return false unless x }
    end
    true
  end

  def any?(*pat)
    return __unsupported__("Enumerable#any? with a pattern argument") unless pat.empty?
    if block_given?
      each { |x| return true if yield(x) }
    else
      each { |x| return true if x }
    end
    false
  end

  def none?(*pat)
    return __unsupported__("Enumerable#none? with a pattern argument") unless pat.empty?
    if block_given?
      each { |x| return false if yield(x) }
    else
      each { |x| return false if x }
    end
    true
  end

  def one?(*pat)
    return __unsupported__("Enumerable#one? with a pattern argument") unless pat.empty?
    n = 0
    if block_given?
      each { |x| n = n + 1 if yield(x) }
    else
      each { |x| n = n + 1 if x }
    end
    n == 1
  end

  def count(*a)
    return __unsupported__("Enumerable#count with an argument") unless a.empty?
    n = 0
    if block_given?
      each { |x| n = n + 1 if yield(x) }
    else
      each { |x| n = n + 1 }
    end
    n
  end

  def sum(*a)
    return __unsupported__("Enumerable#sum arity") if a.length > 1
    acc = 0
    acc = a[0] if a.length == 1
    if block_given?
      each { |x| acc = acc + yield(x) }
    else
      each { |x| acc = acc + x }
    end
    acc
  end

  def each_with_index
    return __unsupported__("Enumerator: Enumerable#each_with_index without a block") unless block_given?
    i = 0
    each { |x|
      yield(x, i)
      i = i + 1
    }
    self
  end

  def each_with_object(memo)
    return __unsupported__("Enumerator: Enumerable#each_with_object without a block") unless block_given?
    each { |x| yield(x, memo) }
    memo
  end

  def group_by
    return __unsupported__("Enumerator: Enumerable#group_by without a block") unless block_given?
    h = {}
    each { |x|
      k = yield(x)
      if h.key?(k)
        h[k].push(x)
      else
        h[k] = [x]
      end
    }
    h
  end

  def partition
    return __unsupported__("Enumerator: Enumerable#partition without a block") unless block_given?
    yes = []
    no = []
    each { |x|
      if yield(x)
        yes.push(x)
      else
        no.push(x)
      end
    }
    [yes, no]
  end

  def tally
    h = {}
    each { |x|
      if h.key?(x)
        h[x] = h[x] + 1
      else
        h[x] = 1
      end
    }
    h
  end

  def include?(obj)
    each { |x| return true if x == obj }
    false
  end
  alias member? include?

  def first(*a)
    if a.empty?
      each { |x| return x }
      nil
    elsif a.length == 1
      take(a[0])
    else
      __unsupported__("Enumerable#first arity")
    end
  end

  def take(n)
    r = []
    return r if n <= 0
    each { |x|
      r.push(x)
      break if r.length == n
    }
    r
  end

  def take_while
    return __unsupported__("Enumerator: Enumerable#take_while without a block") unless block_given?
    r = []
    each { |x|
      break unless yield(x)
      r.push(x)
    }
    r
  end

  def drop(n)
    r = []
    i = 0
    each { |x|
      r.push(x) if i >= n
      i = i + 1
    }
    r
  end

  def drop_while
    return __unsupported__("Enumerator: Enumerable#drop_while without a block") unless block_given?
    r = []
    dropping = true
    each { |x|
      dropping = false if dropping && !yield(x)
      r.push(x) unless dropping
    }
    r
  end

  def each_slice(n)
    return __unsupported__("Enumerator: Enumerable#each_slice without a block") unless block_given?
    return __unsupported__("Enumerable#each_slice with n <= 0 (ArgumentError)") if n <= 0
    buf = []
    each { |x|
      buf.push(x)
      if buf.length == n
        yield(buf)
        buf = []
      end
    }
    yield(buf) if buf.length > 0
    self
  end

  def each_cons(n)
    return __unsupported__("Enumerator: Enumerable#each_cons without a block") unless block_given?
    return __unsupported__("Enumerable#each_cons with n <= 0 (ArgumentError)") if n <= 0
    buf = []
    each { |x|
      buf.push(x)
      buf.shift if buf.length > n
      yield(buf.dup) if buf.length == n
    }
    self
  end

  def reverse_each
    return __unsupported__("Enumerator: Enumerable#reverse_each without a block") unless block_given?
    a = []
    each { |x| a.push(x) }
    i = a.length - 1
    while i >= 0
      yield(a[i])
      i = i - 1
    end
    self
  end

  def min_by
    return __unsupported__("Enumerator: Enumerable#min_by without a block") unless block_given?
    best = nil
    bestk = nil
    have = false
    each { |x|
      k = yield(x)
      if !have
        best = x
        bestk = k
        have = true
      else
        c = (k <=> bestk)
        return __unsupported__("Enumerable#min_by with a nil <=>") if c.nil?
        if c < 0
          best = x
          bestk = k
        end
      end
    }
    best
  end

  def max_by
    return __unsupported__("Enumerator: Enumerable#max_by without a block") unless block_given?
    best = nil
    bestk = nil
    have = false
    each { |x|
      k = yield(x)
      if !have
        best = x
        bestk = k
        have = true
      else
        c = (k <=> bestk)
        return __unsupported__("Enumerable#max_by with a nil <=>") if c.nil?
        if c > 0
          best = x
          bestk = k
        end
      end
    }
    best
  end

  def min(*a)
    return __unsupported__("Enumerable#min with an argument") unless a.empty?
    best = nil
    have = false
    each { |x|
      if !have
        best = x
        have = true
      else
        c = block_given? ? yield(x, best) : (x <=> best)
        return __unsupported__("Enumerable#min with a nil comparison") if c.nil?
        best = x if c < 0
      end
    }
    best
  end

  def max(*a)
    return __unsupported__("Enumerable#max with an argument") unless a.empty?
    best = nil
    have = false
    each { |x|
      if !have
        best = x
        have = true
      else
        c = block_given? ? yield(x, best) : (x <=> best)
        return __unsupported__("Enumerable#max with a nil comparison") if c.nil?
        best = x if c > 0
      end
    }
    best
  end

  def minmax
    [min, max]
  end

  # Insertion sort over an extracted key vector: `<=>` dispatch means user
  # classes and mixed comparables work, and it is stable (CRuby's sort is not,
  # so programs that observe tie order are outside what this models faithfully).
  def sort_by
    return __unsupported__("Enumerator: Enumerable#sort_by without a block") unless block_given?
    keys = []
    vals = []
    each { |x|
      keys.push(yield(x))
      vals.push(x)
    }
    i = 1
    while i < vals.length
      k = keys[i]
      v = vals[i]
      j = i - 1
      done = false
      while j >= 0 && !done
        c = (keys[j] <=> k)
        return __unsupported__("Enumerable#sort_by with a nil <=>") if c.nil?
        if c > 0
          keys[j + 1] = keys[j]
          vals[j + 1] = vals[j]
          j = j - 1
        else
          done = true
        end
      end
      keys[j + 1] = k
      vals[j + 1] = v
      i = i + 1
    end
    vals
  end

  def sort
    vals = []
    each { |x| vals.push(x) }
    i = 1
    while i < vals.length
      v = vals[i]
      j = i - 1
      done = false
      while j >= 0 && !done
        c = block_given? ? yield(vals[j], v) : (vals[j] <=> v)
        return __unsupported__("Enumerable#sort with a nil comparison") if c.nil?
        if c > 0
          vals[j + 1] = vals[j]
          j = j - 1
        else
          done = true
        end
      end
      vals[j + 1] = v
      i = i + 1
    end
    vals
  end

  def inject(*a)
    if block_given?
      if a.empty?
        acc = nil
        have = false
        each { |x|
          if have
            acc = yield(acc, x)
          else
            acc = x
            have = true
          end
        }
        acc
      elsif a.length == 1
        acc = a[0]
        each { |x| acc = yield(acc, x) }
        acc
      else
        __unsupported__("Enumerable#inject with a block and 2 arguments")
      end
    else
      if a.length == 1
        op = a[0]
        acc = nil
        have = false
        each { |x|
          if have
            acc = acc.send(op, x)
          else
            acc = x
            have = true
          end
        }
        acc
      elsif a.length == 2
        acc = a[0]
        op = a[1]
        each { |x| acc = acc.send(op, x) }
        acc
      else
        __unsupported__("Enumerable#inject arity")
      end
    end
  end
  alias reduce inject
end

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
  # It is prelude Ruby because it *dispatches* (L115, L122); the arity error
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

# ─── Integer ────────────────────────────────────────────────────────────────

class Numeric
  # CRuby mixes Comparable into Numeric, not into Integer/Float — which is also
  # where it lands in `Integer.ancestors` [V].
  include Comparable
end

class Integer
  def upto(n)
    return __unsupported__("Enumerator: Integer#upto without a block") unless block_given?
    i = self
    while i <= n
      yield(i)
      i = i + 1
    end
    self
  end

  def downto(n)
    return __unsupported__("Enumerator: Integer#downto without a block") unless block_given?
    i = self
    while i >= n
      yield(i)
      i = i - 1
    end
    self
  end

  def step(limit, by)
    return __unsupported__("Enumerator: Integer#step without a block") unless block_given?
    return __unsupported__("Integer#step with a zero step (ArgumentError)") if by == 0
    i = self
    if by > 0
      while i <= limit
        yield(i)
        i = i + by
      end
    else
      while i >= limit
        yield(i)
        i = i + by
      end
    end
    self
  end
end

class String
  include Comparable
end

class Symbol
  include Comparable

  # Symbol ordering *is* String ordering of the names [V]. Without this the
  # `include` above was inert and worse than inert: `Comparable#<` found a `nil`
  # `<=>` and raised `ArgumentError: comparison of Symbol with :v failed` where
  # CRuby answers `true` — a **disagreement**, not a gate, and the one the W4b
  # heads turned up first (N39).
  #
  # Only Symbol compares to Symbol; `:k <=> 1` and `:k <=> "k"` are both nil [V],
  # and Comparable turns that nil into the ArgumentError for the operators.
  def <=>(other)
    return nil unless other.is_a?(Symbol)
    to_s <=> other.to_s
  end
end

# ─── Hash ───────────────────────────────────────────────────────────────────
#
# Enumerable applies to Hash (its `each` yields `[k, v]` pairs), but the methods
# below differ from the generic ones: they return a **Hash** and yield the key
# and value as *two* arguments [V].

class Hash
  include Enumerable

  def select
    return __unsupported__("Enumerator: Hash#select without a block") unless block_given?
    r = {}
    each { |k, v| r[k] = v if yield(k, v) }
    r
  end
  alias filter select

  def reject
    return __unsupported__("Enumerator: Hash#reject without a block") unless block_given?
    r = {}
    each { |k, v| r[k] = v unless yield(k, v) }
    r
  end

  def transform_values
    return __unsupported__("Enumerator: Hash#transform_values without a block") unless block_given?
    r = {}
    each { |k, v| r[k] = yield(v) }
    r
  end

  def transform_keys
    return __unsupported__("Enumerator: Hash#transform_keys without a block") unless block_given?
    r = {}
    each { |k, v| r[yield(k)] = v }
    r
  end

  def any?(*pat)
    return __unsupported__("Hash#any? with a pattern argument") unless pat.empty?
    return __unsupported__("Hash#any? without a block") unless block_given?
    each { |k, v| return true if yield(k, v) }
    false
  end

  def all?(*pat)
    return __unsupported__("Hash#all? with a pattern argument") unless pat.empty?
    return __unsupported__("Hash#all? without a block") unless block_given?
    each { |k, v| return false unless yield(k, v) }
    true
  end

  def none?(*pat)
    return __unsupported__("Hash#none? with a pattern argument") unless pat.empty?
    return __unsupported__("Hash#none? without a block") unless block_given?
    each { |k, v| return false if yield(k, v) }
    true
  end

  def count(*a)
    return __unsupported__("Hash#count with an argument") unless a.empty?
    return length unless block_given?
    n = 0
    each { |k, v| n = n + 1 if yield(k, v) }
    n
  end

  def sum(*a)
    return __unsupported__("Hash#sum arity") if a.length > 1
    return __unsupported__("Hash#sum without a block") unless block_given?
    acc = 0
    acc = a[0] if a.length == 1
    each { |k, v| acc = acc + yield(k, v) }
    acc
  end
end

class Array
  include Enumerable
end

class String
  # `delete_prefix`/`delete_suffix`/`start_with?`-adjacent trimming, in RubyCore
  # rather than as Lean rules (L62: a missing builtin should cost a few lines of
  # Ruby). `version.rb` and `vulns/purl.rb` use `delete_prefix` on URL scheme and
  # `v`-prefix handling.
  def delete_prefix(pre)
    start_with?(pre) ? self[pre.length, length - pre.length] : self
  end

  def delete_suffix(suf)
    end_with?(suf) ? self[0, length - suf.length] : self
  end
end

class Array
  # `zip` over one or more other arrays; a short partner pads with nil [V]. The
  # block form yields each tuple and returns nil.
  def zip(*others)
    out = []
    i = 0
    while i < length
      row = [self[i]]
      others.each { |o| row.push(o[i]) }
      out.push(row)
      i += 1
    end
    return out unless block_given?
    out.each { |row| yield(row) }
    nil
  end

  def dig(i, *rest)
    v = self[i]
    return v if rest.empty? || v.nil?
    v.dig(*rest)
  end

  # `[[k, v], …].to_h`, or `to_h { |e| [k, v] }` [V]. A non-pair element is a
  # TypeError naming the element's class **and its index** — `rb_ary_to_h` has the
  # index and says so, where `Enumerable#to_h`'s otherwise-identical message does
  # not [V] (L124; found writing the guard for the class-naming rule below).
  def to_h
    h = {}
    i = 0
    each do |e|
      pair = block_given? ? yield(e) : e
      unless pair.is_a?(Array) && pair.length == 2
        # `.class.to_s`, not `.class.name`: CRuby names the class through
        # `rb_class_name`, which renders an *anonymous* class by address, where
        # `Module#name` answers nil and `+` would raise (L124). Every message in
        # this file that names a class follows that rule.
        unless pair.is_a?(Array)
          raise TypeError, "wrong element type " + pair.class.to_s + " at " + i.to_s +
                           " (expected array)"
        end
        raise ArgumentError, "wrong array length at " + i.to_s +
                             " (expected 2, was " + pair.length.to_s + ")"
      end
      h[pair[0]] = pair[1]
      i += 1
    end
    h
  end

  # Element-wise `<=>`: the first non-zero comparison wins, else length decides;
  # nil if any element pair is incomparable [V].
  def <=>(other)
    return nil unless other.is_a?(Array)
    n = length < other.length ? length : other.length
    i = 0
    while i < n
      c = self[i] <=> other[i]
      return nil if c.nil?
      return c unless c.zero?
      i += 1
    end
    length <=> other.length
  end

  # `fetch(i)` raises where `[]` returns nil, and `fetch(i, default)` /
  # `fetch(i) { … }` supply one instead.
  def fetch(i, *default)
    n = length
    j = i < 0 ? n + i : i
    if j >= 0 && j < n
      self[j]
    elsif block_given?
      yield(i)
    elsif default.length == 1
      default[0]
    else
      raise IndexError, "index " + i.to_s + " outside of array bounds: " +
                        (n.zero? ? "0...0" : (-n).to_s + "..." + n.to_s)
    end
  end
end



# ─── Kernel conversions ─────────────────────────────────────────────────────

module Kernel
  # `Integer(x, base)` is `rb_convert_to_integer`, and it is **two rules wearing
  # one name** (L130). The version here used to be only the second half's
  # happy path — `arg.to_s.strip`, then digits — which was wrong twice over:
  #
  #   * a non-String argument is not stringified at all. It is **converted**:
  #     `to_str` (so a String-like is parsed), then `to_int`, then `to_i`, and
  #     only if none of those answers an Integer does it raise
  #     `TypeError: can't convert X into Integer`. So `Integer(obj)` for an object
  #     with a `to_i` **answers a number** where this raised, and the error class
  #     was wrong for everything else (`ArgumentError` is what an unparseable
  #     *String* gets);
  #   * the default base is **0**, not 10 — which means "look at the prefix", so
  #     `Integer("0xff")` is 255, `Integer("010")` is **8**, and `Integer("1_000")`
  #     is 1000 [V]. All three raised.
  #
  # `vulns/identify.rb` uses the base-16 form to decode a percent-escape.
  #
  # `exception: false` answers **nil** instead of raising, for both failure classes
  # [V]. It is a real keyword parameter rather than a gate because without one the
  # keyword arrives as a positional Hash (Ruby 3's rule for a method that declares
  # no keywords) and is read as the *base*.
  def Integer(arg, base = nil, exception: true)
    return __integer(arg, base) if exception

    begin
      __integer(arg, base)
    rescue ArgumentError, TypeError
      nil
    end
  end

  def __integer(arg, base)
    # `rb_check_string_type` first: a String (or a `to_str`) is *parsed*, and it is
    # the only argument a base may accompany [V].
    str = String === arg ? arg : __check_convert(arg, :to_str)
    return __parse_int(str, base.nil? ? 0 : base, arg) if String === str

    raise ArgumentError, "base specified for non string value" unless base.nil?
    return arg if Integer === arg

    if Float === arg
      # `Integer(2.9)` is 2 and `Integer(-2.9)` is -2 — truncation toward zero,
      # which is `Float#to_i`. NaN/Infinity raise `FloatDomainError`, a class this
      # model does not have, so they refuse rather than answer something else.
      return __unsupported__("Integer() of a NaN or Infinity (FloatDomainError is not modeled)") \
        if arg.nan? || arg == Float::INFINITY || arg == -Float::INFINITY

      return arg.to_i
    end

    __to_integer(arg)
  end

  # The `to_int`-then-`to_i` half, with CRuby's two different failure messages.
  # `to_int` goes through `rb_check_funcall` (so a custom `respond_to?` can refuse
  # it, and a `method_missing` can serve it) and a non-Integer answer is simply
  # **ignored**; `to_i` then decides, and *its* non-Integer answer is named in the
  # message — "can't convert X to Integer (X#to_i gives Y)", with `to`, against the
  # `into` of the no-method case [V].
  def __to_integer(arg)
    t = __check_convert(arg, :to_int)
    return t if Integer === t

    # nil/true/false have no `to_i` (nil's is a builtin CRuby does not consult
    # here), and are named literally rather than by class [V].
    unless arg.nil? || arg.equal?(true) || arg.equal?(false)
      if arg.__user_defines?(:to_i) || arg.__user_defines?(:method_missing)
        u = arg.to_i
        return u if Integer === u

        raise TypeError, "can't convert " + arg.class.to_s + " to Integer (" +
                         arg.class.to_s + "#to_i gives " + u.class.to_s + ")"
      end
    end
    raise TypeError, "can't convert " + __conv_desc(arg) + " into Integer"
  end

  # How `can't convert X into Integer` names its argument: nil/true/false
  # literally, everything else by class [V] — `Integer(:sym)` says "Symbol", not
  # ":sym". (The same rule as Lean's `coerceName`, one file over.)
  def __conv_desc(arg)
    return "nil" if arg.nil?
    return "true" if arg.equal?(true)
    return "false" if arg.equal?(false)

    arg.class.to_s
  end

  # `rb_int_parse_cstr`: strip, sign, prefix, then digits with single `_`
  # separators. `orig` is the argument the error message shows.
  def __parse_int(s, base, orig)
    return __unsupported__("Integer() with a negative base") if base < 0
    raise ArgumentError, "invalid radix " + base.to_s if base == 1 || base > 36

    t = s.strip
    neg = t.start_with?("-")
    t = t[1, t.length - 1] if neg || t.start_with?("+")
    pfx = t[0, 2].downcase
    # base 0 means "read the prefix"; an explicit base accepts only *its own*
    # prefix, so `Integer("0xff", 10)` is an error [V].
    if base.zero?
      if pfx == "0x" then base = 16; t = t[2, t.length - 2]
      elsif pfx == "0b" then base = 2; t = t[2, t.length - 2]
      elsif pfx == "0o" then base = 8; t = t[2, t.length - 2]
      elsif pfx == "0d" then base = 10; t = t[2, t.length - 2]
      elsif t.length > 1 && t.start_with?("0") then base = 8; t = t[1, t.length - 1]
      else base = 10
      end
    elsif (base == 16 && pfx == "0x") || (base == 2 && pfx == "0b") ||
          (base == 8 && pfx == "0o") || (base == 10 && pfx == "0d")
      t = t[2, t.length - 2]
    elsif base == 8 && t.length > 1 && t.start_with?("0")
      t = t[1, t.length - 1]
    end

    digits = "0123456789abcdefghijklmnopqrstuvwxyz"[0, base]
    bad = ArgumentError.new("invalid value for Integer(): " + orig.inspect)
    raise bad if t.empty? || t.start_with?("_") || t.end_with?("_")

    n = 0
    prev_us = false
    t.each_char do |c|
      if c == "_"
        raise bad if prev_us

        prev_us = true
        next
      end
      prev_us = false
      d = digits.index(c.downcase)
      raise bad if d.nil?

      n = n * base + d
    end
    neg ? -n : n
  end

  # `Kernel#Float` is the same two-rule shape, with three differences worth
  # spelling out because they are easy to assume away [V]: it does **not** consult
  # `to_str` (an object with only a `to_str` raises `TypeError`), it takes no base,
  # and its String grammar is *looser* than a Ruby float literal — `".5"` is 0.5
  # and `"5."` is 5.0, both of which are syntax errors as literals.
  def Float(arg, exception: true)
    return __float(arg) if exception

    begin
      __float(arg)
    rescue ArgumentError, TypeError
      nil
    end
  end

  def __float(arg)
    return arg if Float === arg
    return arg.to_f if Integer === arg
    # nil/true/false are refused **before** the `to_f` probe, as CRuby's `NIL_P`
    # test is: the prelude defines `NilClass#to_f`, so without this `Float(nil)`
    # answered 0.0 where CRuby raises [V].
    raise TypeError, "can't convert " + __conv_desc(arg) + " into Float" \
      if arg.nil? || arg.equal?(true) || arg.equal?(false)

    if String === arg
      bad = ArgumentError.new("invalid value for Float(): " + arg.inspect)
      t = arg.strip
      # Hexadecimal floats (`"0x1p3"` is 8.0) are a second grammar with its own
      # rounding, and refusing is better than a wrong number.
      return __unsupported__("Float() of a hexadecimal float string") \
        if t.downcase.start_with?("0x") || t.downcase.start_with?("-0x") ||
           t.downcase.start_with?("+0x")
      raise bad unless /\A[+-]?(?:[0-9][0-9_]*)?(?:\.[0-9_]*)?(?:[eE][+-]?[0-9][0-9_]*)?\z/.match?(t)
      # the grammar above still admits `""`, `"."`, `"+"` and `"1_"`-style
      # separators at an edge, so the digit-shape checks are explicit
      raise bad unless /[0-9]/.match?(t)
      raise bad if /__|_\z|\._|_\.|\A_|[eE]_|_[eE]/.match?(t)

      return t.gsub("_", "").to_f
    end

    t = __check_convert(arg, :to_f)
    return t if Float === t

    unless arg.nil? || arg.equal?(true) || arg.equal?(false)
      if arg.__user_defines?(:to_f) || arg.__user_defines?(:method_missing)
        raise TypeError, "can't convert " + arg.class.to_s + " to Float (" +
                         arg.class.to_s + "#to_f gives " + t.class.to_s + ")"
      end
    end
    raise TypeError, "can't convert " + __conv_desc(arg) + " into Float"
  end

  # `format("%%%02X", n)` and the handful of directives the slice uses.
  def format(fmt, *args)
    out = ""
    i = 0
    ai = 0
    while i < fmt.length
      c = fmt[i]
      if c != "%"
        out += c
        i += 1
        next
      end
      j = i + 1
      flags = ""
      while j < fmt.length && "0-+ #".include?(fmt[j])
        flags += fmt[j]
        j += 1
      end
      width = ""
      while j < fmt.length && "0123456789".include?(fmt[j])
        width += fmt[j]
        j += 1
      end
      return __unsupported__("format: unterminated directive") if j >= fmt.length
      conv = fmt[j]
      i = j + 1
      if conv == "%"
        out += "%"
        next
      end
      v = args[ai]
      ai += 1
      body = case conv
             when "d", "i" then v.to_i.to_s
             when "s" then v.to_s
             when "X" then __to_base(v.to_i, 16).upcase
             when "x" then __to_base(v.to_i, 16)
             when "o" then __to_base(v.to_i, 8)
             when "b" then __to_base(v.to_i, 2)
             else return __unsupported__("format directive %" + conv)
             end
      w = width.empty? ? 0 : width.to_i
      pad = flags.include?("0") ? "0" : " "
      body = pad * (w - body.length) + body if body.length < w
      out += body
    end
    out
  end

  def __to_base(n, base)
    return "0" if n.zero?
    neg = n.negative?
    n = -n if neg
    digits = "0123456789abcdefghijklmnopqrstuvwxyz"
    s = ""
    while n.positive?
      s = digits[n % base] + s
      n /= base
    end
    neg ? "-" + s : s
  end

  # `Array(x)`: nil → [], an Array (or `to_ary`) → itself, `to_a` if it has one,
  # else a one-element array [V]. `vulns/vulnerability.rb` uses it three times to
  # normalize optional OSV list fields.
  def Array(arg)
    return [] if arg.nil?
    return arg if arg.is_a?(Array)
    return arg.to_ary if arg.respond_to?(:to_ary)
    return arg.to_a if arg.respond_to?(:to_a)
    [arg]
  end
end

class NilClass
  def to_i = 0

  def to_f = 0.0

  def to_h = {}
end

class Hash
  # `dig(a, b, …)`: follow the chain, stopping at the first nil [V]. A non-nil
  # intermediate that cannot be dug raises TypeError, which falls out of the
  # `dig` send below.
  def dig(key, *rest)
    v = self[key]
    return v if rest.empty? || v.nil?
    v.dig(*rest)
  end

  # `compact` drops nil *values*; `compact!` is deliberately absent until asked
  # for (it returns nil when nothing changed, which is easy to get wrong).
  def compact
    h = {}
    each { |k, v| h[k] = v unless v.nil? }
    h
  end
end

# ─── Dispatching repr: the prelude twins ────────────────────────────────────
#
# Pure repr (`Repr.lean`) renders a value without running any Ruby, which is fast
# and is what almost every program needs. It cannot speak for a value whose class
# — or whose *contents* — override `inspect`/`to_s`, because honouring that means
# **dispatching**, and a builtin cannot push a frame.
#
# So each such builtin defers to a twin here under a different name (L116). The
# different name is what makes this cheap: it shadows nothing, so no purity answer
# changes, and `Repr` stays the fast path for everything it can still handle. The
# twins then recurse through *ordinary dispatch*, which is exactly the behaviour
# that was missing — `[custom].inspect` renders each element with its own
# `inspect`, and a plain object renders each ivar with its own.
#
# `__write` and `__addr_str` are the two primitives they need: append a String to
# stdout with no rendering, and the `0x…` a default `inspect` carries.
class Object
  # `rb_obj_as_string` (L129): **the** way a C-level renderer turns a value into a
  # String. It calls `to_s`, and if that answers something that is not a String it
  # falls back to the default `#<C:0x…>` form — CRuby never lets a non-String out.
  # A value that already *is* a String is used verbatim, so a redefined
  # `String#to_s` is not called [V].
  #
  # Every twin below renders through this and `__as_inspect` rather than through a
  # bare `to_s`/`inspect`, because a bare one is exactly the bug: `[BadToS.new].join`
  # raised `TypeError: no implicit conversion of Integer into String` where CRuby
  # answers `#<BadToS:0x…>`. The desugaring of string interpolation calls this too
  # (desugar C38), which is why the desugar harness's wrapper defines a twin of it
  # in plain Ruby — the same rule has to hold on both sides of the round-trip.
  def __as_string
    return self if String === self

    s = to_s
    String === s ? s : __any_to_s
  end

  # `rb_inspect`: `inspect`, and then **`rb_obj_as_string` of the result** — which
  # is why `p Bar.new` prints `1` for a `Bar#inspect` that answers `1`, rather than
  # raising [V]. Note it is the *result* that is coerced here, not the receiver.
  def __as_inspect
    v = inspect
    String === v ? v : v.__as_string
  end

  def __inspect_slow
    ivs = instance_variables
    # `__any_to_s` minus its closing `>`: the default `inspect` names the class the
    # same dispatch-free way, so the two cannot drift.
    head = __any_to_s
    head = head[0, head.length - 1]
    return head + ">" if ivs.empty?

    head + " " + ivs.map { |n| n.to_s + "=" + instance_variable_get(n).__as_inspect }.join(", ") + ">"
  end

  def __to_s_slow = __any_to_s

  # `p` returns its argument (or the array of them, or nil for none) [V].
  def __p_slow(*args)
    args.each { |a| __write(a.__as_inspect + "\n") }
    return nil if args.empty?
    return args[0] if args.length == 1

    args
  end

  def __print_slow(*args)
    args.each { |a| __write(a.__as_string) }
    nil
  end

  # `puts` flattens arrays, prints a blank line for nil or an empty array, and
  # does not double a newline the value already ends with [V].
  def __puts_slow(*args)
    return __write("\n") if args.empty?

    args.each { |a| __puts_one(a) }
    nil
  end

  def __puts_one(a)
    if a.is_a?(Array)
      return __write("\n") if a.empty?

      a.each { |e| __puts_one(e) }
    elsif a.nil?
      __write("\n")
    else
      str = a.__as_string
      __write(str)
      __write("\n") unless str.end_with?("\n")
    end
    nil
  end
end

class Array
  def __inspect_slow = "[" + map { |e| e.__as_inspect }.join(", ") + "]"

  def __to_s_slow = __inspect_slow

  # `join` renders each element with `to_s`, flattens nested arrays, and renders
  # nil as the empty string [V].
  def __join_slow(sep = nil)
    # The separator goes through `StringValue` (`to_str`), **not** `to_s`: a String
    # is used verbatim, so `["a"].join("-")` is unaffected by a redefined
    # `String#to_s` [V]. Calling `to_s` here made that program raise `TypeError:
    # no implicit conversion of Integer into String` (L129). A non-String
    # separator gates, exactly as the pure `joinImpl` does.
    s = if sep.nil?
          ""
        elsif String === sep
          sep
        else
          return __unsupported__("Array#join with a non-String separator")
        end
    parts = []
    __join_collect(parts)
    out = ""
    i = 0
    while i < parts.length
      out += s unless i.zero?
      out += parts[i]
      i += 1
    end
    out
  end

  def __join_collect(parts)
    each do |e|
      if e.is_a?(Array)
        e.__join_collect(parts)
      elsif e.nil?
        parts.push("")
      else
        parts.push(e.__as_string)
      end
    end
    nil
  end
end

class Range
  # A **nil endpoint prints as nothing** — `(1..nil).inspect` is `"1.."` — except
  # when both are nil, which prints `"nil..nil"` [V]. `to_s` needs no such case:
  # `nil.to_s` is `""` already, so `(nil..nil).to_s` really is `".."`. The Lean
  # twin in `Repr.lean` carries the same rule (L122).
  def __inspect_slow
    dots = exclude_end? ? "..." : ".."
    lo = self.begin
    hi = self.end
    return "nil" + dots + "nil" if lo.nil? && hi.nil?

    (lo.nil? ? "" : lo.__as_inspect) + dots + (hi.nil? ? "" : hi.__as_inspect)
  end

  def __to_s_slow
    self.begin.__as_string + (exclude_end? ? "..." : "..") + self.end.__as_string
  end
end

class Exception
  # `Exception#message` **is** `to_s` (`exc_message` is one `rb_funcall`), so a
  # user `to_s` shows through it and a user `message` changes nothing about
  # `to_s`/`inspect` [V]. As a Lean builtin sharing `to_s`'s arm it read the
  # payload directly, and `E.new("boom").message` answered "boom" for a class whose
  # `to_s` says otherwise. Prelude Ruby is the only spelling that dispatches
  # (L131). Note it does not coerce: a `to_s` answering `1` makes `message`
  # answer **1** [V].
  def message = to_s

  # `rb_exc_inspect`: `rb_obj_as_string(exc)` — so the *dispatched* `to_s`, coerced
  # — and the bare class name when that is empty [V].
  def __inspect_slow
    s = __as_string
    return self.class.to_s if s.empty?

    "#<" + self.class.to_s + ": " + s + ">"
  end
end

class Hash
  def __inspect_slow
    return "{}" if empty?

    "{" + map { |k, v| __hash_key_repr(k) + " " + v.__as_inspect }.join(", ") + "}"
  end

  def __to_s_slow = __inspect_slow

  # A Symbol key with an identifier-like name renders `k: v`; everything else
  # renders `k => v` [V].
  def __hash_key_repr(k)
    return k.__as_inspect + " =>" unless k.is_a?(Symbol)

    str = k.to_s
    ident = !str.empty? && !"0123456789".include?(str[0]) &&
            str.each_char.all? { |c| c == "_" || c == "?" || c == "!" || c == "=" ||
                                     "abcdefghijklmnopqrstuvwxyz".include?(c.downcase) ||
                                     "0123456789".include?(c) }
    ident ? str + ":" : str.inspect + ":"
  end
end

# ─── Conversion protocols (`rb_check_funcall`) ──────────────────────────────
#
# `String.try_convert` / `Array.try_convert` and the implicit-conversion sites
# share one rule, and it is subtler than "call it if `respond_to?`":
#
#   * if the class carries a **custom `respond_to?`**, CRuby asks it, and a false
#     answer means "not convertible" without the method ever being called;
#   * otherwise the method is called if it is defined **or if `method_missing`
#     can serve it** — so a `method_missing`-provided `to_ary` converts even
#     though `respond_to?(:to_ary)` is false [V].
#
# Both halves are observable and they disagree, which is why this is written out
# rather than approximated by either one. `__user_defines?` is the only piece
# that needs the machine: "does this object's class chain carry a *user*
# definition of this name" is a fact about the method tables (L115).
class Object
  # The default `<=>`: `0` when the two are `==`, and **nil** otherwise — the nil
  # is what lets `Comparable` degrade to "incomparable" rather than raise from
  # the wrong place. CRuby calls `rb_equal`, so a **user `==` participates**;
  # here that is free, because `==` is an ordinary send. As a builtin it had to
  # gate on a class with a user `==` (L114), which is the same lesson as
  # `try_convert` (L115): a rule that needs to dispatch does not belong in Lean.
  def <=>(other)
    self == other ? 0 : nil
  end
end

module Kernel
  def __check_convert(obj, meth)
    if obj.__user_defines?(:respond_to?)
      return nil unless obj.respond_to?(meth)

      return obj.send(meth)
    end
    return obj.send(meth) if obj.__user_defines?(meth)

    if obj.__user_defines?(:method_missing)
      # A **custom `respond_to_missing?`** is consulted before `method_missing` is
      # entered (`check_funcall_missing` tests `rb_method_basic_definition_p` on it,
      # so the *default* one — which answers false — is deliberately not), and it is
      # asked with `include_private = true` [V]. Missing this clause is what made
      # `Integer(obj)` on an object whose `method_missing` serves `to_int` and whose
      # `respond_to_missing?` names only `to_int` raise from the **`to_str`** probe
      # that runs first (L130).
      return nil if obj.__user_defines?(:respond_to_missing?) &&
                    !obj.respond_to_missing?(meth, true)

      return obj.send(meth)
    end

    nil
  end
end

class String
  def self.try_convert(obj)
    return obj if obj.is_a?(String)

    r = __check_convert(obj, :to_str)
    return nil if r.nil?
    return r if r.is_a?(String)

    raise TypeError, "can't convert " + obj.class.to_s + " to String (" +
                     obj.class.to_s + "#to_str gives " + r.class.to_s + ")"
  end
end

class Array
  def self.try_convert(obj)
    return obj if obj.is_a?(Array)

    r = __check_convert(obj, :to_ary)
    return nil if r.nil?
    return r if r.is_a?(Array)

    raise TypeError, "can't convert " + obj.class.to_s + " to Array (" +
                     obj.class.to_s + "#to_ary gives " + r.class.to_s + ")"
  end
end

# ─── The coerce protocol (`rb_num_coerce_bin` and friends) ──────────────────
#
# A numeric operator does not decide "not a number" from the class chain: it asks
# the **argument** to `coerce` itself and re-dispatches the operator on the pair
# that comes back. Three halves of that are observable, and a Lean rule can
# produce none of them (L123):
#
#   * the `coerce` body **runs** — `3 + Money.new(4)` is `7`, and whatever the
#     body printed, printed;
#   * the failure says *why*. Nothing answered `coerce` → "X can't be coerced
#     into Integer"; something answered with the wrong shape → "coerce must
#     return [x, y]", *even for the comparisons*, which are otherwise the
#     forgiving ones;
#   * the pair decides the rest. `["a", 2]` makes `0 + o` raise "no implicit
#     conversion of Integer into String" from `String#+`, and `0 < o` raise
#     "comparison of String with 2 failed" — errors about operands the program
#     never wrote. [V]
#
# `coerceDefer?` sends the operators' non-numeric argument here. The three
# entry points mirror CRuby's three wrappers exactly, because they differ:
# `rb_num_coerce_bin` raises, `rb_num_coerce_relop` raises a *different* error
# naming the original operands, and `rb_num_coerce_cmp` answers nil.
class Object
  # `rb_check_funcall`'s callability rule, one step past L115's: a **user**
  # `respond_to?` is asked first and a false answer is believed without calling
  # anything; otherwise the call happens if the method is defined or a user
  # `method_missing` can serve it — and in that second case a user
  # `respond_to_missing?` gets the same veto. A `respond_to?` that says *true*
  # over a method nobody supplies is not callable either: CRuby calls the
  # default `method_missing`, rescues the `NoMethodError` and reports "not
  # callable", which is what returning false here reproduces [V].
  #
  # Not folded into `__check_convert`: that one answers `nil` for both "nothing
  # answered" and "answered nil", and `do_coerce` raises differently for those.
  def __coercible?(obj)
    return false if obj.__user_defines?(:respond_to?) && !obj.respond_to?(:coerce)
    return true if obj.__user_defines?(:coerce)
    return false unless obj.__user_defines?(:method_missing)

    !obj.__user_defines?(:respond_to_missing?) || obj.respond_to_missing?(:coerce, true)
  end

  # CRuby's `do_coerce`. `err` separates the arithmetic operators (raise) from
  # the comparisons (answer "incomparable"), and it moves only the **first**
  # outcome: a non-nil answer of the wrong shape raises either way [V].
  def __do_coerce(other, err)
    unless __coercible?(other)
      __coerce_failed(other) if err
      return nil
    end

    pair = other.send(:coerce, self)
    return nil if pair.nil? && !err
    raise TypeError, "coerce must return [x, y]" unless pair.is_a?(Array) && pair.length == 2

    pair
  end

  # `rb_num_coerce_bin`: coerce, then run the operator on the pair.
  def __coerce_bin(other, op)
    pair = __do_coerce(other, true)
    pair[0].send(op, pair[1])
  end

  # `rb_num_coerce_relop`: "did not coerce" *and* "the coerced comparison
  # answered nil" are the same outcome, an ArgumentError naming the operands the
  # program actually wrote — not the coerced pair.
  def __coerce_relop(other, op)
    pair = __do_coerce(other, false)
    r = pair.nil? ? nil : pair[0].send(op, pair[1])
    __cmp_failed(other) if r.nil?

    r
  end

  # `rb_num_coerce_cmp`: `<=>` never raises for an incomparable operand, and
  # passes the pair's own answer through — including its nil.
  def __coerce_cmp(other)
    pair = __do_coerce(other, false)
    pair.nil? ? nil : (pair[0] <=> pair[1])
  end

  def __coerce_add(other) = __coerce_bin(other, :+)

  def __coerce_sub(other) = __coerce_bin(other, :-)

  def __coerce_mul(other) = __coerce_bin(other, :*)

  def __coerce_div(other) = __coerce_bin(other, :/)

  def __coerce_mod(other) = __coerce_bin(other, :%)

  def __coerce_pow(other) = __coerce_bin(other, :**)

  def __coerce_divmod(other) = __coerce_bin(other, :divmod)

  def __coerce_lt(other) = __coerce_relop(other, :<)

  def __coerce_gt(other) = __coerce_relop(other, :>)

  def __coerce_le(other) = __coerce_relop(other, :<=)

  def __coerce_ge(other) = __coerce_relop(other, :>=)

  # `Integer#==`/`Float#==` are the exception in this family: they do not coerce
  # at all. `num_equal` hands the comparison to the other object — `rb_equal(y,
  # x)` — and reduces its answer to a boolean, so a user `==` decides `0 == obj`
  # and a truthy `5` becomes `true` [V].
  def __eq_reverse(other)
    (other == self) ? true : false
  end
end

class Regexp
  # `$~` lives in the **frame** (L121), and CRuby's `last_match` is a C function
  # reading its caller's — so this needs the one primitive that says so, without
  # which it would read its own (always-empty) slot.
  def self.last_match(n = nil)
    __match_to_caller
    md = $~
    return md if n.nil?
    return nil if md.nil?

    md[n]
  end
end

# ─── Forwardable ────────────────────────────────────────────────────────────
#
# `def_delegator :@list, :size` installs a `size` that forwards to `@list.size`.
# Like `Struct`, it is a metaprogramming pattern rather than a library: the whole
# module is `define_method` over a receiver expression, so it costs prelude Ruby
# and no Lean rules. `pkg_version.rb` delegates six methods to its `version`.
#
# The accessor may be an ivar (`:@list`) or a method (`:inner`), which is the one
# case worth being careful about — `instance_variable_get` for the former,
# `send` for the latter [V].
module Forwardable
  def def_delegator(accessor, method, ali = method)
    acc = accessor.to_s
    meth = method.to_sym
    ivar = acc.start_with?("@")
    define_method(ali.to_sym) do |*args, **kw, &blk|
      target = ivar ? instance_variable_get(acc) : send(acc)
      kw.empty? ? target.send(meth, *args, &blk) : target.send(meth, *args, **kw, &blk)
    end
    nil
  end

  def def_delegators(accessor, *methods)
    methods.each { |mm| def_delegator(accessor, mm) }
    nil
  end

  # The `_delegator`-less spellings are the documented aliases.
  def delegate(hash)
    hash.each do |methods, accessor|
      Array(methods).each { |mm| def_delegator(accessor, mm) }
    end
    nil
  end
end

# ─── JSON — generation only ─────────────────────────────────────────────────
#
# `version_spec.rb` asserts `Version#to_json`, which Homebrew gets from the json
# library. Generation is a pure fold over the value; **parsing is not modeled**
# and `JSON.parse` gates, because the slice never parses (its OSV records arrive
# as already-decoded Hashes in the specs).
module JSON
  def self.generate(obj) = obj.__to_json

  def self.dump(obj) = obj.__to_json

  def self.parse(*args, **kw)
    __unsupported__("JSON.parse (only generation is modeled)")
  end
end

class Object
  def to_json(*args) = __to_json

  # `#<Object:0x…>`-style default: the json library emits the `to_s` for an
  # object it does not know, as a JSON string.
  def __to_json = to_s.__to_json
end

class NilClass
  def __to_json = "null"
end

class TrueClass
  def __to_json = "true"
end

class FalseClass
  def __to_json = "false"
end

class Integer
  def __to_json = to_s
end

class Float
  def __to_json = to_s
end

class Symbol
  def __to_json = to_s.__to_json
end

class String
  # Only the escapes JSON requires: quote, backslash, and the C0 controls. `/`
  # is **not** escaped [V].
  def __to_json
    out = "\""
    each_char do |c|
      out += if c == "\"" then "\\\""
             elsif c == "\\" then "\\\\"
             elsif c == "\n" then "\\n"
             elsif c == "\t" then "\\t"
             elsif c == "\r" then "\\r"
             elsif c.ord < 32 then "\\u" + format("%04x", c.ord)
             else c
             end
    end
    out + "\""
  end
end

class Array
  def __to_json = "[" + map { |e| e.__to_json }.join(",") + "]"
end

class Hash
  def __to_json
    "{" + map { |k, v| k.to_s.__to_json + ":" + v.__to_json }.join(",") + "}"
  end
end

# ─── Pathname — the pure path half ─────────────────────────────────────────
#
# `Version.detect` wraps its argument in `Pathname(spec)` and then asks it for
# `to_s`, `basename`, `dirname` and Homebrew's own `stem` — all pure string
# operations on the path, with no filesystem access anywhere in the slice. So
# `Pathname` is a wrapper over a String with exactly those, plus the
# `extname`/`sub`/`==`/`inspect` that fall out; anything else routes to
# `method_missing` and gates by name, the same guard `File` and `URI` use, so
# `Pathname#exist?` refuses rather than answering.
#
# `Pathname#stem`, which `Version.detect` also calls, is deliberately **not**
# here: it is Homebrew's own extension (`extend/pathname.rb:187`), not Ruby's, so
# putting it in the prelude would make the model answer something the control —
# running the same program without Homebrew's boot path — cannot. It belongs in
# the difftest harness's stub set, alongside `blank?` (N36).
class Pathname
  include Comparable

  def initialize(path)
    @path = path.to_s
  end

  def to_s = @path

  def to_str = @path

  def to_path = @path

  def inspect = "#<Pathname:" + @path + ">"

  def <=>(other) = other.is_a?(Pathname) ? (@path <=> other.to_s) : nil

  def ==(other) = other.is_a?(Pathname) && @path == other.to_s

  def eql?(other) = self == other

  def basename(suffix = nil)
    Pathname.new(suffix.nil? ? File.basename(@path) : File.basename(@path, suffix))
  end

  def dirname = Pathname.new(File.dirname(@path))

  def extname = File.extname(@path)

  def sub(*args, &blk) = Pathname.new(@path.sub(*args, &blk))

  def empty? = @path.empty?

  def method_missing(name, *args, **kw, &blk)
    __unsupported__("Pathname#" + name.to_s + " (only the pure path operations are modeled)")
  end

  def respond_to_missing?(name, include_private = false)
    true
  end
end

module Kernel
  def Pathname(arg)
    arg.is_a?(Pathname) ? arg : Pathname.new(arg)
  end
end

# ─── URI — the one function the slice reaches ───────────────────────────────
#
# `version.rb:351` calls `URI.decode_www_form_component(spec)` and that is the
# **only** use of `URI` anywhere in the slice's eight files. It is a pure string
# function, so it is modeled; everything else on `URI` routes to
# `method_missing` and gates by name, for the same reason `File` does — defining
# the constant without that guard would turn `URI.parse` from an honest
# Unsupported into a NoMethodError.
#
# One real limit, and it is the byte-string limit again: a `%XX` above 0x7F is a
# *byte* of a multi-byte character (`caf%C3%A9` is `café`), and the model has no
# byte strings, so that gates rather than producing two junk characters.
module URI
  def self.decode_www_form_component(str, enc = nil)
    s = str.to_s
    out = ""
    i = 0
    while i < s.length
      c = s[i]
      if c == "+"
        out += " "
        i += 1
      elsif c == "%"
        hex = s[i + 1, 2]
        if hex.nil? || hex.length < 2 || !__hex2?(hex)
          raise ArgumentError, "invalid %-encoding (" + s + ")"
        end
        n = Integer(hex, 16)
        if n > 127
          return __unsupported__("URI.decode_www_form_component of a multi-byte %-escape " \
                                 "(byte strings are not modeled)")
        end
        out += n.chr
        i += 3
      else
        out += c
        i += 1
      end
    end
    out
  end

  def self.__hex2?(h)
    h.each_char.all? { |c| "0123456789abcdefABCDEF".include?(c) }
  end

  def self.method_missing(name, *args, **kw, &blk)
    __unsupported__("URI." + name.to_s + " (only decode_www_form_component is modeled)")
  end

  def self.respond_to_missing?(name, include_private = false)
    true
  end
end

# ─── File — the pure path operations only ───────────────────────────────────
#
# `File` is a filesystem class, and the slice reaches exactly one of its
# methods: `File.basename(url)` in `vulns/identify.rb`, used to chop the last
# component off a *URL*. That operation is pure string manipulation with no
# effect at all, so it is modeled; everything else routes to `method_missing`
# and gates by name. Defining the constant without that guard would turn
# `File.read` from an honest Unsupported into a NoMethodError, which is a wrong
# answer rather than a refusal.
module File
  SEPARATOR = "/"

  def self.basename(path, suffix = nil)
    s = path.to_s
    parts = s.split("/")
    base = parts.empty? ? (s.empty? ? "" : "/") : parts[parts.length - 1]
    return base if suffix.nil?
    return base if suffix == base
    if suffix == ".*"
      i = base.length - 1
      while i > 0
        return base[0, i] if base[i] == "."
        i -= 1
      end
      base
    else
      base.end_with?(suffix) ? base[0, base.length - suffix.length] : base
    end
  end

  def self.extname(path)
    b = basename(path)
    i = b.length - 1
    while i > 0
      return b[i, b.length - i] if b[i] == "."
      i -= 1
    end
    ""
  end

  def self.dirname(path)
    s = path.to_s
    i = s.length - 1
    while i >= 0
      if s[i] == "/"
        return "/" if i.zero?
        return s[0, i]
      end
      i -= 1
    end
    "."
  end

  def self.join(*parts)
    parts.map { |x| x.to_s }.join("/")
  end

  def self.method_missing(name, *args, **kw, &blk)
    __unsupported__("File." + name.to_s + " (only the pure path operations are modeled)")
  end

  def self.respond_to_missing?(name, include_private = false)
    true
  end
end

class String
  # `sub`/`gsub` live here because of the **block form**, which a builtin cannot
  # serve: it has to call back into the interpreter once per match. The
  # two-argument replacement form stays a primitive (`__sub_rep`/`__gsub_rep`)
  # and this only dispatches to it, so the common path costs one extra send.
  #
  # The loop walks **absolute offsets into `self`** via `__search_at`, and that is
  # not a style choice. The earlier version matched against a progressively
  # shortened `rest`, which re-anchored the pattern at every step: `\A` and `^`
  # matched at each remainder's start, so `"12".gsub(/\A\d/) { "X" }` answered
  # `"XX"` where CRuby answers `"X2"` — a **wrong answer** that no corpus reached
  # until the W4b heads generated anchored patterns (N39). Offsets also make `$~`
  # come out right: `__search_at` sets it per iteration, so a block can read `$1`,
  # and the spans are relative to the whole string rather than to a remainder.
  #
  # A **zero-width** match advances one character, without which
  # `"aaa".gsub(/a*/) { "X" }` would not terminate.
  def sub(pat, rep = nil, &blk)
    __match_to_caller
    return __sub_rep(pat, rep) unless rep.nil?
    return __unsupported__("String#sub with neither a replacement nor a block") if blk.nil?
    re = pat.is_a?(Regexp) ? pat : Regexp.new(Regexp.escape(pat))
    m = __search_at(re, 0)
    return self if m.nil?
    b = m.begin(0)
    e = m.end(0)
    self[0, b].to_s + blk.call(m[0]).to_s + self[e, length - e].to_s
  end

  def gsub(pat, rep = nil, &blk)
    __match_to_caller
    return __gsub_rep(pat, rep) unless rep.nil?
    return __unsupported__("String#gsub with neither a replacement nor a block") if blk.nil?
    re = pat.is_a?(Regexp) ? pat : Regexp.new(Regexp.escape(pat))
    out = ""
    cur = 0        # absolute offset of the first character not yet copied out
    last = nil     # begin offset of the last successful match, for `$~`
    guard = 0
    while guard <= length + 1
      guard += 1
      m = __search_at(re, cur)
      break if m.nil?
      b = m.begin(0)
      e = m.end(0)
      last = b
      out += self[cur, b - cur].to_s + blk.call(m[0]).to_s
      if e == b
        out += self[e, 1].to_s
        cur = e + 1
      else
        cur = e
      end
      break if cur > length
    end
    out += self[cur, length - cur].to_s if cur <= length
    # CRuby leaves `$~` at the **last successful** match, not at the failed search
    # that ended the loop [V]. Re-searching from that match's own start finds it
    # again (leftmost-first), which is cheaper than carrying the MatchData.
    __search_at(re, last) unless last.nil?
    out
  end

  # `partition`/`rpartition` split around the first / last occurrence of a
  # String separator and always return three parts [V]; a miss puts the whole
  # string in the *head* for `partition` and in the *tail* for `rpartition`.
  # `index`/`rindex` for a String needle (a Regexp needle would go through the
  # matcher and is not needed here).
  def index(needle, start = 0)
    __match_to_caller
    i = start < 0 ? length + start : start
    i = 0 if i < 0
    # A **Regexp** needle searches with the engine and sets `$~`, exactly as
    # `match` does [V]. Without this branch `needle.length` raised NoMethodError
    # where CRuby answers an offset — a wrong answer, not a gate (N39).
    if needle.is_a?(Regexp)
      m = __search_at(needle, i)
      return m.nil? ? nil : m.begin(0)
    end
    n = needle.length
    while i + n <= length
      return i if self[i, n] == needle
      i += 1
    end
    nil
  end

  def rindex(needle, start = nil)
    # Backward search with a pattern is its own algorithm (CRuby scans right to
    # left for the *last* match); not modeled rather than approximated.
    return __unsupported__("String#rindex with a Regexp needle") if needle.is_a?(Regexp)
    n = needle.length
    i = (start.nil? ? length - n : (start < 0 ? length + start : start))
    i = length - n if i > length - n
    while i >= 0
      return i if self[i, n] == needle
      i -= 1
    end
    nil
  end

  def each_char
    return to_enum_chars unless block_given?
    __each_char_blk { |c| yield(c) }
  end

  # `each_char` without a block would need an Enumerator; the two prelude uses
  # (`all?`, `format`'s digit scan) always pass one, and `chars` covers the rest.
  def to_enum_chars
    chars
  end

  def __each_char_blk
    return __unsupported__("Enumerator: String#each_char without a block") unless block_given?
    i = 0
    while i < length
      yield(self[i, 1])
      i += 1
    end
    self
  end

  def partition(sep)
    i = index(sep)
    return [self, "", ""] if i.nil?
    [self[0, i], sep, self[i + sep.length, length - i - sep.length]]
  end

  def rpartition(sep)
    i = rindex(sep)
    return ["", "", self] if i.nil?
    [self[0, i], sep, self[i + sep.length, length - i - sep.length]]
  end

  # `tr` over explicit character lists and `a-z` ranges, with `^` negation. The
  # `to`-list is padded with its last character, and an empty `to` deletes [V].
  def tr(from, to)
    neg = from.start_with?("^") && from.length > 1
    src = __tr_expand(neg ? from[1, from.length - 1] : from)
    dst = __tr_expand(to)
    out = ""
    each_char do |c|
      hit = src.include?(c)
      hit = !hit if neg
      if !hit
        out += c
      elsif dst.empty?
        # delete
      elsif neg
        out += dst[dst.length - 1]
      else
        i = src.index(c)
        out += (i < dst.length ? dst[i] : dst[dst.length - 1])
      end
    end
    out
  end

  def __tr_expand(spec)
    out = []
    i = 0
    while i < spec.length
      if i + 2 < spec.length && spec[i + 1] == "-"
        a = spec[i].ord
        b = spec[i + 2].ord
        while a <= b
          out.push(a.chr)
          a += 1
        end
        i += 3
      else
        out.push(spec[i])
        i += 1
      end
    end
    out
  end

  # ── Encodings (L117/L118) ──
  #
  # The model has exactly two: UTF-8 and ASCII-8BIT. A binary String's payload
  # holds one *character per byte*, which is what makes `Purl.encode` —
  # `component.b.gsub(…) { |c| "%%%02X" % c.ord }` — answer `caf%C3%A9` for
  # `"café"` rather than the character-wise `caf%E9` (L110 gated on this).
  #
  # These are one line each over a Lean primitive, and they are here rather than
  # in Lean for L115's reason: the *interesting* part of `force_encoding` is
  # dispatching `Encoding#name` on its argument, which a builtin cannot do.
  #
  # There is a **third** CRuby encoding this model does not track: `US-ASCII`,
  # which CRuby gives to every String it *synthesizes* rather than reads from
  # source — `65.chr`, `1.to_s`, `:a.to_s`, `nil.to_s`, `[1,2].join`,
  # `/a/.source`, `1.inspect` are all US-ASCII while a literal is UTF-8 [V].
  # Tracking it needs a third tag threaded through ~40 String-producing rules;
  # `slice-gates.md` carries it as a known gap.
  #
  # So `encoding` answers only what the tag actually determines: BINARY, or
  # UTF-8 for a String holding a non-ASCII byte (which no US-ASCII String can).
  # For an ASCII-only String it hands back `Encoding.__undetermined`, whose
  # *observations* gate — it is still the right thing to pass to
  # `force_encoding`, which is the only use the slice makes of it
  # (`Identify.decode` ends `.force_encoding(component.encoding)`).
  def encoding
    return Encoding::BINARY if __binary?
    return Encoding::UTF_8 unless __bytes.all? { |x| x < 128 }
    Encoding.__undetermined
  end

  # `force_encoding` **mutates and returns self**, which is why it goes through
  # `__force_*` rather than the copying `__as_*` that `b` uses.
  def force_encoding(enc)
    # `__name_raw`, not `name`: the undetermined encoding refuses to *name*
    # itself but is UTF-8-or-US-ASCII, and re-tagging as either leaves the bytes
    # alone — `__force_utf8` gates on an invalid sequence in both readings.
    n = enc.is_a?(Encoding) ? (enc.__name_raw || "UTF-8") : enc.to_s
    if n == "ASCII-8BIT" || n == "BINARY" || n == "ascii-8bit" || n == "binary"
      __force_binary
    elsif n == "UTF-8" || n == "utf-8"
      __force_utf8
    else
      __unsupported__("String#force_encoding to " + n)
    end
  end

  def bytes = __bytes

  def each_byte
    return __unsupported__("Enumerator: String#each_byte without a block") unless block_given?
    __bytes.each { |x| yield(x) }
    self
  end

  # `b` is a *copy* in ASCII-8BIT, so it is the non-mutating primitive.
  def b = __as_binary
end

# ─── Encoding ───────────────────────────────────────────────────────────────
#
# Two real instances and one honest placeholder are the whole class: the model's
# Strings are either UTF-8 or ASCII-8BIT (L117), and `UNDETERMINED` stands for
# "UTF-8 or US-ASCII, and this model does not track which" — see `String#encoding`
# above for why that is a refusal rather than a guess.
#
# `ASCII_8BIT` is `BINARY` *by identity*, matching CRuby, where
# `Encoding::BINARY.equal?(Encoding::ASCII_8BIT)` is true [V] — `BINARY` is the
# alias and `ASCII-8BIT` the `name`, which is why `name` and `inspect` disagree
# about which spelling to use.
#
# Anything else CRuby's Encoding can do (`list`, `default_external`,
# `compatible?`, `Encoding.find`) is absent, so it gates by the shadow rule
# rather than by a `method_missing` guard.
class Encoding
  def initialize(name)
    @name = name
  end

  # The raw tag, `nil` for the undetermined one. Not CRuby API — it exists so
  # `String#force_encoding` can act on an encoding that refuses to name itself.
  def __name_raw = @name

  def __gate = __unsupported__("Encoding of an ASCII-only String (US-ASCII vs UTF-8 is not tracked — L118)")

  def name = @name.nil? ? __gate : @name

  def to_s = name

  def inspect
    return __gate if @name.nil?
    @name == "UTF-8" ? "#<Encoding:UTF-8>" : "#<Encoding:BINARY (ASCII-8BIT)>"
  end

  def ==(other)
    return __gate if @name.nil?
    return false unless other.is_a?(Encoding)
    return other.__gate if other.__name_raw.nil?
    other.__name_raw == @name
  end

  def eql?(other) = self == other

  UTF_8 = new("UTF-8")
  BINARY = new("ASCII-8BIT")
  ASCII_8BIT = BINARY

  # The "UTF-8 or US-ASCII, and the model does not know which" instance. One
  # object, memoized, so identity is stable across calls the way the real
  # constants' is.
  UNDETERMINED = new(nil)

  def self.__undetermined = UNDETERMINED
end

# ─── Struct ─────────────────────────────────────────────────────────────────
#
# `Struct.new(:a, :b)` returns a **class**, so the whole feature is a class
# factory: `Class.new` plus `define_method`, both of which the model already has
# (L64/L66). That is the thesis of this project made concrete — a "core class"
# that is really a metaprogramming pattern costs prelude Ruby, not Lean rules.
#
# It could not live here before L103: `inspect`, `to_s` and `==` are part of a
# Struct's contract, and defining any of them in the prelude used to turn off
# pure repr for the whole program.
class Struct
  # `keyword_init: nil` (the default) accepts *either* calling convention, which
  # is what CRuby does for a struct that was not created with an explicit
  # `keyword_init:` [V].
  def self.new(*names, keyword_init: nil, &body)
    return __unsupported__("Struct.new with no members") if names.empty?
    return __unsupported__("Struct.new(\"Name\") (named struct constant)") if names[0].is_a?(String)
    syms = names.map { |n| n.to_sym }
    kwi = keyword_init
    # `Class.new { … }` (block form) is not modeled; `Class.new` + `class_eval`
    # is the same thing and both halves are (L64/L66).
    cls = Class.new
    cls.class_eval do
      define_singleton_method(:members) { syms.dup }

      define_method(:members) { syms.dup }

      define_method(:initialize) do |*a, **kw|
        if kwi == true || (kwi.nil? && a.empty? && !kw.empty?)
          bad = kw.keys.reject { |k| syms.include?(k) }
          raise ArgumentError, "unknown keywords: " + bad.map { |k| k.inspect }.join(", ") unless bad.empty?
          syms.each { |s| instance_variable_set("@" + s.to_s, kw[s]) }
        else
          raise ArgumentError, "struct size differs" if a.length > syms.length
          i = 0
          while i < syms.length
            instance_variable_set("@" + syms[i].to_s, a[i])
            i += 1
          end
        end
        nil
      end

      syms.each do |s|
        define_method(s) { instance_variable_get("@" + s.to_s) }
        define_method(s.to_s + "=") { |v| instance_variable_set("@" + s.to_s, v) }
      end

      define_method(:to_a) { syms.map { |s| send(s) } }
      define_method(:deconstruct) { syms.map { |s| send(s) } }

      define_method(:to_h) do
        h = {}
        syms.each { |s| h[s] = send(s) }
        h
      end

      define_method(:[]) do |k|
        if k.is_a?(Integer)
          i = k < 0 ? syms.length + k : k
          raise IndexError, "offset " + k.to_s + " too large for struct(size:" + syms.length.to_s + ")" if i < 0 || i >= syms.length
          send(syms[i])
        else
          key = k.to_sym
          raise NameError, "no member '" + k.to_s + "' in struct" unless syms.include?(key)
          send(key)
        end
      end

      define_method(:==) do |other|
        other.class == self.class && syms.all? { |s| send(s) == other.send(s) }
      end

      define_method(:eql?) { |other| self == other }

      define_method(:each) do |&blk|
        return __unsupported__("Enumerator: Struct#each without a block") if blk.nil?
        syms.each { |s| blk.call(send(s)) }
        self
      end

      define_method(:size) { syms.length }
      define_method(:length) { syms.length }

      define_method(:inspect) do
        parts = syms.map { |s| s.to_s + "=" + send(s).inspect }
        nm = self.class.name
        "#<struct " + (nm.nil? ? "" : nm + " ") + parts.join(", ") + ">"
      end

      define_method(:to_s) { inspect }
    end
    cls.class_eval(&body) unless body.nil?
    cls
  end
end

# ─── T — the sorbet-runtime shim ────────────────────────────────────────────
#
# Sorbet's *runtime* half, modeled the way this project models everything else:
# as ordinary RubyCore code performing heap mutation, not as new Lean rules
# (`../../docs/semantics/types-and-preservation.md` §A.5, §C.2 — "a `sig` is heap
# mutation that replaces a method-table entry with a checking wrapper").
#
# Why it belongs in the model at all: the honest soundness statement for Sorbet
# is the *runtime* three-outcome one (§C.1 option 2), because the static half is
# unsound by design. That statement is only meaningful if the enforcement
# mechanism is inside the semantics — otherwise there is nothing for the theorem
# to quantify over. With the shim here, "sorbet-runtime raised a TypeError at a
# sig boundary" is an ordinary reachable outcome of `stepFn`, so the existing
# `typeStuck` / `invariant_sound` machinery applies to it unchanged.
#
# Fidelity is established the same way as the rest of the prelude: by difftest
# against the real gem over `difftest/corpus/sorbet/`. Error messages therefore
# match sorbet-runtime **byte for byte**, except for the `Caller:`/`Definition:`
# source-location lines, which RubyCore cannot produce (the AST carries no line
# numbers) and which the engine normalizes away on both sides.

module T
  # A runtime type. sorbet-runtime coerces raw types into `T::Types::*` objects
  # with a `valid?` predicate; the shim keeps that shape but flattens the class
  # hierarchy into one tagged object, since only `valid?` and the printed label
  # are observable.
  #
  # NOTE the deliberate absence of `to_s`/`inspect`/`==`: defining any of those
  # anywhere in the prelude flips `reprPure` off globally (authoring rule 3) and
  # every `puts` in every program would gate. `label` carries the rendering.
  class Type
    def initialize(kind, args, label)
      @kind = kind
      @args = args
      @label = label
    end

    def label
      return @label unless @kind == :proc

      # `T.proc` renders its accumulated chain; the gem prints `params()` even
      # when empty (verified: `T.proc.returns(Integer)` names itself
      # `T.proc.params().returns(Integer)`).
      parts = []
      unless @proc_params.nil?
        @proc_params.each { |k, v| parts.push(k.to_s + ": " + T.type_label(v)) }
      end
      tail = if @proc_void
               ".void"
             elsif @proc_returns.nil?
               ".returns(T.untyped)"
             else
               ".returns(" + T.type_label(@proc_returns) + ")"
             end
      "T.proc.params(" + parts.join(", ") + ")" + tail
    end

    # The `T.proc` builder chain. sorbet-runtime's `T.proc` returns a builder
    # that accumulates `.params`/`.returns`/`.void`, and the resulting type's
    # runtime check is only `is_a?(Proc)` — the declared parameter and return
    # types are **erased**, exactly like generic type arguments (§A.6). That
    # erasure is not an approximation here: it is why
    # `difftest/corpus/sorbet/untyped-boundary/003.rb` reaches a TypeError
    # inside typed code with nothing having checked the block's return.
    def params(**kw)
      @proc_params = kw
      self
    end

    def returns(type)
      @proc_returns = type
      self
    end

    def void
      @proc_void = true
      self
    end

    # Is this `T.nilable(X)`? (`T.nilable` builds an `:any` of X and NilClass.)
    def nilable?
      @kind == :any && !@args.nil? && @args.any? { |a| a == NilClass }
    end

    # The label of the non-nil part, for the T::Struct prop-type message.
    def nilable_inner_label
      rest = @args.reject { |a| a == NilClass }
      rest.length == 1 ? T.type_label(rest[0]) : @label
    end

    def valid?(value)
      k = @kind
      return true if k == :untyped
      return value.is_a?(@args[0]) if k == :simple
      if k == :any
        i = 0
        while i < @args.length
          return true if T.__valid?(@args[i], value)
          i += 1
        end
        return false
      end
      if k == :all
        i = 0
        while i < @args.length
          return false unless T.__valid?(@args[i], value)
          i += 1
        end
        return true
      end
      # Generics are ERASED at runtime (§A.6): the check is the top-level class
      # only, never the element types. This is not a shortcut — it is what
      # sorbet-runtime does, and reproducing it is the point (a heterogeneous
      # array walks straight through, `difftest/corpus/sorbet/generics/000.rb`).
      return value.is_a?(@args[0]) if k == :erased_generic
      return value.is_a?(Proc) if k == :proc
      return value.is_a?(Class) if k == :class_of
      # :self_type / :attached_class / :type_parameter — unchecked at runtime
      true
    end
  end

  # A subscriptable type constructor: `T::Array[Integer]`.
  class GenericType
    def initialize(base, label)
      @base = base
      @label = label
    end

    def [](*args)
      parts = []
      i = 0
      while i < args.length
        parts.push(T.type_label(args[i]))
        i += 1
      end
      T::Type.new(:erased_generic, [@base], @label + "[" + parts.join(", ") + "]")
    end
  end

  # ── coercion and rendering ────────────────────────────────────────────────

  def self.__valid?(type, value)
    return type.valid?(value) if type.is_a?(T::Type)
    return value.is_a?(type) if type.is_a?(Module)
    true
  end

  def self.type_label(type)
    return type.label if type.is_a?(T::Type)
    return type.name if type.is_a?(Module)
    type.inspect
  end

  # `T::Utils.string_truncate_middle(s, 30, 30)`: the gem shortens a long value
  # in a type error to `first 27 + "..." + last 30` [V]. Reproduced because the
  # ellipsis is *observable* — a 100-character String in a failing sig prints
  # differently from the String itself.
  def self.__truncate_middle(s)
    return s if s.length <= 60

    s[0...27] + "..." + s[-30..-1]
  end

  # `T::Types::Base#describe_obj`, byte for byte (gem 0.6.13405, `types/base.rb`).
  # Three rules, none of them guessable and all three observable:
  #
  #   * `nil` / `true` / `false` print **no value clause** — "it would be
  #     redundant to print class and value", says the gem;
  #   * an object whose `inspect` is the **default** one prints `with hash N`
  #     rather than the `#<C:0x…>` the gem calls ugly. `N` is `Object#hash`,
  #     which is *per-process seeded* — no implementation has a stable answer
  #     (N38), so the model refuses here rather than inventing one. It used to
  #     answer the `with value` form, which was simply wrong;
  #   * everything else prints `with value <inspect, truncated>`.
  #
  # The class is named by `to_s`, not `name`: for an anonymous class the gem
  # prints `#<Class:0x…>` and `name` is nil, which made `+` raise a *different*
  # TypeError (the L124 rule, one file over). (L127.)
  def self.__describe_obj(value)
    # `equal?`, not `==`: the gem's `case obj when nil, true, false` dispatches on
    # the *literal* (`nil === obj`), never on `obj`. Writing it as `value == true`
    # dispatches `==` on the value instead, which gates the whole program for any
    # receiver whose `==` is an unmodeled builtin — `T.let((1..2), Integer)` came
    # back `unmodeled builtin would shadow: Range#==`. Identity is exact here:
    # nil/true/false are immediates.
    if value.nil? || value.equal?(true) || value.equal?(false)
      return "type " + value.class.to_s
    end

    if value.__default_inspect?
      __unsupported__("sorbet-runtime: a type error naming an object with the " +
                      "default inspect (the gem prints its per-process `hash`)")
    end
    "type " + value.class.to_s + " with value " + T.__truncate_middle(value.inspect)
  end

  # The shared failure path. Message shapes are sorbet-runtime's, verified
  # against the gem (`difftest/corpus/sorbet/`).
  def self.__check!(prefix, type, value)
    return value if T.__valid?(type, value)
    raise TypeError, prefix + ": Expected type " + T.type_label(type) +
                     ", got " + T.__describe_obj(value)
  end

  # ── the assertion family (§A.3) ───────────────────────────────────────────
  # The static/runtime split is the whole soundness architecture in one table:
  # `T.unsafe` is the ONE form with no runtime check; every other form that is
  # static-unsound is at least runtime-checked. That asymmetry is reproduced
  # exactly here.

  def self.let(value, type)
    __check!("T.let", type, value)
  end

  def self.cast(value, type)
    __check!("T.cast", type, value)
  end

  def self.assert_type!(value, type)
    __check!("T.assert_type!", type, value)
  end

  def self.must(value)
    raise TypeError, "Passed `nil` into T.must" if value.nil?
    value
  end

  # No runtime check at all — the escape hatch, faithfully unchecked.
  def self.unsafe(value)
    value
  end

  # `T.bind(self, X)`: trusted statically, checked at runtime like T.cast.
  def self.bind(value, type)
    __check!("T.bind", type, value)
  end

  # A static-only tool: at runtime it is the identity.
  def self.reveal_type(value)
    value
  end

  # Exhaustiveness. Statically proves all cases are handled; reaching it at
  # runtime means the static proof did not apply, and the gem raises.
  def self.absurd(value)
    raise TypeError, "Control flow reached T.absurd."
  end

  # ── type constructors (§A.1) ──────────────────────────────────────────────

  def self.untyped
    T::Type.new(:untyped, [], "T.untyped")
  end

  def self.noreturn
    T::Type.new(:untyped, [], "T.noreturn")
  end

  def self.anything
    T::Type.new(:untyped, [], "T.anything")
  end

  def self.self_type
    T::Type.new(:self_type, [], "T.self_type")
  end

  def self.attached_class
    T::Type.new(:attached_class, [], "T.attached_class")
  end

  def self.type_parameter(name)
    T::Type.new(:type_parameter, [], "T.type_parameter(:" + name.to_s + ")")
  end

  def self.class_of(klass)
    T::Type.new(:class_of, [klass], "T.class_of(" + T.type_label(klass) + ")")
  end

  def self.any(*types)
    T::Type.new(:any, types, "T.any(" + T.__labels(types) + ")")
  end

  def self.all(*types)
    T::Type.new(:all, types, "T.all(" + T.__labels(types) + ")")
  end

  # `T.nilable(x)` is *literally* `T.any(NilClass, x)` [D: /docs/union-types],
  # but it prints under its own name.
  def self.nilable(type)
    T::Type.new(:any, [NilClass, type], "T.nilable(" + T.type_label(type) + ")")
  end

  def self.proc
    T::Type.new(:proc, [], "T.proc")
  end

  def self.type_alias(&blk)
    yield
  end

  def self.__labels(types)
    parts = []
    i = 0
    while i < types.length
      parts.push(T.type_label(types[i]))
      i += 1
    end
    parts.join(", ")
  end

  # ── the sig DSL and its runtime enforcement (§A.5) ────────────────────────

  # Records what a `sig { … }` block declared. The block is `instance_eval`ed
  # against one of these, so every DSL method returns self to keep the chain
  # going.
  class Decl
    def initialize
      @params = nil
      @returns = nil
      @void = false
      @checked = :always
    end

    def param_types
      @params
    end

    def return_type
      @returns
    end

    def void?
      @void
    end

    def checked_level
      @checked
    end

    def params(**kw)
      @params = kw
      self
    end

    def returns(type)
      @returns = type
      self
    end

    def void
      @void = true
      self
    end

    def checked(level)
      @checked = level
      self
    end

    # Declarations with no runtime effect. They exist so a real-world sig
    # parses; the static half is Sorbet's business, not the model's.
    def on_failure(*args)
      self
    end

    def type_parameters(*args)
      self
    end

    def abstract
      self
    end

    def overridable
      self
    end

    def override(**kw)
      self
    end

    def final
      self
    end

    def bind(type)
      self
    end
  end

  # `extend T::Sig` is what puts `sig` in a class body. Enforcement rides on
  # `Module#method_added`: `sig` records a pending declaration and the hook
  # wraps the method defined immediately after — the same mechanism the real
  # gem uses, which is why the model had to grow the hook (L77).
  module Sig
    def sig(&blk)
      # In a class/module body `self` is the definee and `T::Sig#method_added`
      # (an instance method of the extended module, so it sits on the class
      # object's singleton chain) is already the hook. At **toplevel** `self` is
      # `main`, not a Module: the `def` that follows lands on Object, whose
      # `method_added` must therefore be installed explicitly. The real gem does
      # the same thing — `sig` installs hooks on the definee rather than
      # assuming they are there.
      if self.is_a?(Module)
        @__t_pending_sig = blk
      else
        T.__toplevel_sig(blk)
      end
      nil
    end

    def method_added(name)
      T.__hook(self, name)
    end
  end

  def self.__toplevel_sig(blk)
    Object.instance_variable_set(:@__t_pending_sig, blk)
    return nil if @__toplevel_hook_installed
    @__toplevel_hook_installed = true
    # A *singleton* method on Object, so it resolves ahead of CRuby's
    # `Module#method_added` no-op (a plain Object instance method would be
    # shadowed by it — see the `.def'` rule in Interp.lean).
    Object.define_singleton_method(:method_added) do |name|
      T.__hook(Object, name)
    end
    nil
  end

  # The hook body, shared by the class-body and toplevel paths.
  def self.__hook(mod, name)
    blk = mod.instance_variable_get(:@__t_pending_sig)
    return nil if blk.nil?
    mod.instance_variable_set(:@__t_pending_sig, nil)
    # Re-entrancy guard: installing the wrapper defines a method, and CRuby
    # fires `method_added` for `define_method` too. Without this a sig would
    # wrap its own wrapper forever.
    return nil if mod.instance_variable_get(:@__t_wrapping)
    mod.instance_variable_set(:@__t_wrapping, true)
    T.__wrap(mod, name, blk)
    mod.instance_variable_set(:@__t_wrapping, false)
    nil
  end

  # Install the checking wrapper: alias the original aside, then define a
  # forwarding method that validates arguments, calls through, and validates the
  # return. This IS the heap mutation of §C.2 — a method-table entry replaced by
  # a checking one.
  # The sig block is evaluated **lazily, once, on the first call** of the method
  # it governs — not at `def` time. That is what the real gem does, and it is
  # not a detail: a sig may name a constant that is not defined yet when the
  # class body runs (`utils/output.rb` has `T.nilable(Time)` in a sig, with
  # `Time` supplied later by the boot path), and evaluating eagerly turns that
  # into a load-time NameError the real program never sees. The `cache` array is
  # captured by the wrapper's closure, so the memo needs no `object_id` and no
  # global table.
  #
  # Consequence of laziness, recorded rather than hidden: `.checked(:never)`
  # can no longer skip *installing* the wrapper (deciding that would mean
  # evaluating the block eagerly), so the wrapper is always installed and calls
  # straight through instead. The escape hatch still skips every check; what
  # changes is only that the frame is present, which is the same reflective
  # visibility the gradual-guarantee probe already records as a violation (N33).
  def self.__wrap(mod, name, blk)
    # The hidden alias must be **unique per module**, not just per method name.
    # With a flat `__t_unchecked_initialize`, a subclass's alias shadows its
    # parent's, so the parent wrapper's `send(hidden, …)` dispatches back into
    # the *subclass's* original body — which is how `Version::NullToken`'s
    # zero-argument `initialize` ended up receiving `Token#initialize`'s one
    # argument ("wrong number of arguments (given 1, expected 0)"). The bug was
    # latent until L107 stopped gating sigs with keyword parameters.
    hidden = "__t_u_" + (mod.name.nil? ? "anon" : mod.name.gsub("::", "_")) +
             "__" + name.to_s
    cache = []
    mod.send(:alias_method, hidden, name)
    mod.send(:define_method, name) do |*args, **kw, &b|
      if cache.empty?
        d = T::Decl.new
        d.instance_eval(&blk)
        cache.push(d)
      end
      decl = cache[0]
      if decl.checked_level == :never
        kw.empty? ? send(hidden, *args, &b) : send(hidden, *args, **kw, &b)
      else
        T.__check_params_kw(decl, args, kw)
        result = kw.empty? ? send(hidden, *args, &b) : send(hidden, *args, **kw, &b)
        T.__check_return(decl, result)
      end
    end
    nil
  end

  # Positional-or-keyword matching (L107). Sorbet requires a sig to list the
  # method's parameters in order, so the i-th *positional* declared name governs
  # the i-th argument; a declared name that appears as a **key in `kw`** is a
  # keyword parameter and is checked against that value instead. The shim has no
  # `instance_method(…).parameters` to consult, but it does not need one: the
  # call itself says which names arrived as keywords. A declared name that is
  # neither is an optional parameter the caller omitted, and there is nothing to
  # check. This replaces the old rule, which gated the whole sig as soon as it
  # declared more names than there were positional arguments — 186 of the
  # Homebrew-slice corpus's programs.
  def self.__check_params_kw(decl, args, kw)
    types = decl.param_types
    return nil if types.nil?
    i = 0
    types.keys.each do |key|
      if kw.key?(key)
        T.__check!("Parameter '" + key.to_s + "'", types[key], kw[key])
      elsif i < args.length
        T.__check!("Parameter '" + key.to_s + "'", types[key], args[i])
        i += 1
      end
    end
    nil
  end

  def self.__check_params(decl, args)
    types = decl.param_types
    return nil if types.nil?
    names = types.keys
    return __unsupported__("sorbet-runtime: sig with more params than arguments (keyword params?)") if names.length > args.length
    i = 0
    while i < names.length
      key = names[i]
      __check!("Parameter '" + key.to_s + "'", types[key], args[i])
      i += 1
    end
    nil
  end

  def self.__check_return(decl, result)
    # `.void` discards the real return value and yields sorbet's VOID sentinel,
    # which IS observable (`p` prints it), so the shim reproduces it.
    return T::Private::Types::Void::VOID if decl.void?
    rt = decl.return_type
    return result if rt.nil?
    __check!("Return value", rt, result)
  end

  module Private
    module Types
      module Void
        module VOID
        end
      end
    end
  end
end

# `extend T::Helpers` is the other half of the annotation surface (the `sig`
# half is `T::Sig`). Everything it installs is a *declaration*: `abstract!`
# and `interface!` tell the static checker that instantiating or calling is a
# type error, `sealed!`/`final!` restrict subclassing, `requires_ancestor`
# constrains where a module may be mixed in — none of them changes what a
# correct program does at runtime.
#
# sorbet-runtime does add one runtime behaviour to `abstract!`: calling an
# unimplemented abstract method raises `NotImplementedError`. That is
# reproduced below rather than dropped, because it is a reachable outcome and
# dropping it would make an abstract call silently return nil.
#
# `mixes_in_class_methods(M)` is the one with real semantics — the includer
# gets `extend M` — so it is implemented rather than declared.
module T
  module Helpers
    # `abstract!` / `interface!` are mostly declarations, but they have one
    # runtime effect and the slice's specs test it: the abstract class itself
    # cannot be instantiated [V] —
    # `RuntimeError: A is declared as abstract; it cannot be instantiated`.
    # Subclasses can, so the guard compares against the declaring class and the
    # inherited path allocates and initializes directly (rather than `super`,
    # which from a `define_singleton_method` body would have to resolve through
    # the eigenclass chain).
    def abstract!
      @__t_abstract = true
      cls = self
      define_singleton_method(:new) do |*a, **kw, &b|
        if equal?(cls)
          raise RuntimeError, cls.name + " is declared as abstract; it cannot be instantiated"
        end
        obj = allocate
        obj.send(:initialize, *a, **kw, &b)
        obj
      end
      nil
    end

    def interface!
      abstract!
    end

    def sealed!
      nil
    end

    def final!
      nil
    end

    # Takes a block naming the required ancestor; purely static.
    def requires_ancestor(&blk)
      nil
    end

    def mixes_in_class_methods(*mods)
      @__t_class_methods = mods
      nil
    end

    def included(base)
      mods = @__t_class_methods
      base.extend(mods[0]) if !mods.nil? && mods.length == 1
      nil
    end
  end
end

# Subscriptable generic constructors and the Boolean alias. Assigned at toplevel
# (not inside `module T`) so `Array`/`Hash` resolve to the real classes rather
# than to the constants being defined.
T::Array = T::GenericType.new(Array, "T::Array")
T::Hash = T::GenericType.new(Hash, "T::Hash")
T::Range = T::GenericType.new(Range, "T::Range")
T::Enumerable = T::GenericType.new(Enumerable, "T::Enumerable")
T::Boolean = T::Type.new(:any, [TrueClass, FalseClass], "T::Boolean")

# `T::Struct` / `T::Enum` are **structural**, not annotations: they define a
# class hierarchy and generate methods, so a program using them cannot be
# understood by ignoring them. Until they are modeled they gate at first use —
# an honest Unsupported rather than a NameError that would read as a wrong
# answer (the difftest engine's one unforgivable verdict).
# `T::Struct` — a typed record. Like `Struct` (L105) this is a metaprogramming
# pattern rather than a core class: `const`/`prop` are class macros that record a
# property and define its reader, and `initialize` is generated from the record.
# It could not live in the prelude before L103, because a `T::Struct` needs its
# own `inspect`.
#
# Two behaviours that a plausible implementation gets wrong, both verified
# against the gem [V]:
#   * `T::Struct` does **not** define `==` — two structs with equal fields are
#     *not* equal, because equality stays identity (inherited from Object).
#   * `inspect` lists the props **alphabetically**, while `serialize` lists them
#     in declaration order and **omits nil**.
class T::Struct
  def self.__own_props
    @__props = [] if @__props.nil?
    @__props
  end

  # Props are inherited, parents first.
  def self.__all_props
    sup = superclass
    base = (!sup.nil? && sup.respond_to?(:__all_props)) ? sup.__all_props : []
    base + __own_props
  end

  # The gem exposes `props` as a Hash keyed by prop name.
  def self.props
    h = {}
    __all_props.each { |pp| h[pp[0]] = { type: pp[1] } }
    h
  end

  def self.const(name, type, default: :__t_none, factory: nil)
    __define_prop(name, type, false, default)
  end

  def self.prop(name, type, default: :__t_none, factory: nil)
    __define_prop(name, type, true, default)
  end

  def self.__define_prop(name, type, mutable, default)
    nm = name.to_sym
    __own_props.push([nm, type, mutable, default])
    ivar = "@" + nm.to_s
    define_method(nm) { instance_variable_get(ivar) }
    if mutable
      cls = self
      define_method(nm.to_s + "=") do |v|
        T.__struct_check(cls, nm, type, v)
        instance_variable_set(ivar, v)
      end
    end
    nil
  end

  def initialize(**kw)
    ps = self.class.__all_props
    known = ps.map { |pp| pp[0] }
    extra = kw.keys.reject { |k| known.include?(k) }
    unless extra.empty?
      raise ArgumentError, self.class.name + ": Unrecognized properties: " +
                           extra.map { |k| k.to_s }.join(", ")
    end
    ps.each do |pp|
      nm = pp[0]
      type = pp[1]
      dflt = pp[3]
      if kw.key?(nm)
        v = kw[nm]
        T.__struct_check(self.class, nm, type, v)
      elsif dflt != :__t_none
        v = dflt
      elsif T.__struct_nilable?(type)
        v = nil
      else
        raise ArgumentError, "Missing required prop `" + nm.to_s +
                             "` for class `" + self.class.name + "`"
      end
      instance_variable_set("@" + nm.to_s, v)
    end
    nil
  end

  def inspect
    ps = self.class.__all_props.map { |pp| pp[0].to_s }.sort
    "<" + self.class.name + " " +
      ps.map { |n| n + "=" + send(n).inspect }.join(" ") + ">"
  end

  def to_s
    inspect
  end

  def serialize(strict = true)
    h = {}
    self.class.__all_props.each do |pp|
      v = send(pp[0])
      h[pp[0].to_s] = v unless v.nil?
    end
    h
  end
end

module T
  # A prop typed `T.nilable(X)` with no default starts as nil [V].
  def self.__struct_nilable?(type)
    return false unless type.is_a?(T::Type)
    type.nilable?
  end

  # The gem reports the *non-nil* part of a nilable prop's type in this message
  # ("need a String", not "need a T.nilable(String)") [V]. The `Caller:` line the
  # gem appends is a source location RubyCore cannot produce; the difftest engine
  # normalizes it away on both sides (see the shim header).
  def self.__struct_check(cls, name, type, value)
    return value if T.__valid?(type, value)
    want = (type.is_a?(T::Type) && type.nilable?) ? type.nilable_inner_label : T.type_label(type)
    # A *different* rule from `__describe_obj` above, and checked separately
    # against the gem: this path prints the plain `inspect` — no truncation, no
    # hash substitution, addresses and all (the difftest engine normalizes those)
    # — and names the class with `to_s`, so an anonymous one is `#<Class:0x…>`
    # rather than the nil that `name` answers (L127).
    raise TypeError, "Parameter '" + name.to_s + "': Can't set " + cls.to_s + "." +
                     name.to_s + " to " + value.inspect + " (instance of " +
                     value.class.to_s + ") - need a " + want
  end
end

class T::Enum
  def self.enums(*args)
    __unsupported__("T::Enum")
  end
end
