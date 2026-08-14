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
# 3. **Never define a repr-sensitive method** (`to_s`, `inspect`, `==`, `eql?`,
#    `message`, `to_str`): defining one flips `reprPure` off globally (L7) and
#    every `puts`/`inspect` in every program would then gate.
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

  def between?(lo, hi)
    self >= lo && self <= hi
  end

  def clamp(lo, hi = nil)
    return __unsupported__("Comparable#clamp with a Range") if hi.nil?
    return lo if self < lo
    return hi if self > hi
    self
  end

  # A `<=>` of nil means "not comparable", and every operator except `==` turns
  # that into `ArgumentError: comparison of X with Y failed` [V] — X is the
  # receiver's class name, Y is the argument rendered the way coercion errors
  # render it (its value for nil/true/false/Integer/Symbol, its class name
  # otherwise). Gating instead, as the prelude used to, refused a case the model
  # can answer exactly.
  def __cmp!(other)
    c = self <=> other
    return c unless c.nil?
    raise ArgumentError, "comparison of " + self.class.name + " with " +
                         Comparable.__desc(other) + " failed"
  end

  def self.__desc(o)
    return "nil" if o.nil?
    return "true" if o == true
    return "false" if o == false
    return o.inspect if o.is_a?(Integer) || o.is_a?(Symbol)
    o.class.name
  end

  def <(other) = __cmp!(other) < 0

  def <=(other) = __cmp!(other) <= 0

  def >(other) = __cmp!(other) > 0

  def >=(other) = __cmp!(other) >= 0

  def between?(min, max)
    if self < min
      false
    else
      !(self > max)
    end
  end

  def clamp(min, max)
    if self < min
      min
    elsif self > max
      max
    else
      self
    end
  end
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
  # TypeError naming the element's class.
  def to_h
    h = {}
    each do |e|
      pair = block_given? ? yield(e) : e
      unless pair.is_a?(Array) && pair.length == 2
        raise TypeError, "wrong element type " + pair.class.name + " (expected array)" unless pair.is_a?(Array)
        raise ArgumentError, "wrong array length (expected 2, was " + pair.length.to_s + ")"
      end
      h[pair[0]] = pair[1]
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
  # `Integer(x, base)` — strict, unlike `String#to_i`: the whole string must be
  # a number or it is an ArgumentError [V]. `vulns/identify.rb` uses the base-16
  # form to decode a percent-escape.
  def Integer(arg, base = 10)
    return arg if arg.is_a?(Integer) && base == 10
    s = arg.to_s.strip
    neg = s.start_with?("-")
    s = s[1, s.length - 1] if neg || s.start_with?("+")
    digits = "0123456789abcdefghijklmnopqrstuvwxyz"[0, base]
    if s.empty? || !s.each_char.all? { |c| digits.include?(c.downcase) }
      raise ArgumentError, "invalid value for Integer(): " + arg.inspect
    end
    n = 0
    s.each_char { |c| n = n * base + digits.index(c.downcase) }
    neg ? -n : n
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
  def __inspect_slow
    ivs = instance_variables
    head = "#<" + self.class.name + ":" + __addr_str
    return head + ">" if ivs.empty?

    head + " " + ivs.map { |n| n.to_s + "=" + instance_variable_get(n).inspect }.join(", ") + ">"
  end

  def __to_s_slow
    "#<" + self.class.name + ":" + __addr_str + ">"
  end

  # `p` returns its argument (or the array of them, or nil for none) [V].
  def __p_slow(*args)
    args.each { |a| __write(a.inspect + "\n") }
    return nil if args.empty?
    return args[0] if args.length == 1

    args
  end

  def __print_slow(*args)
    args.each { |a| __write(a.is_a?(String) ? a : a.to_s) }
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
      str = a.is_a?(String) ? a : a.to_s
      __write(str)
      __write("\n") unless str.end_with?("\n")
    end
    nil
  end
end

class Array
  def __inspect_slow = "[" + map { |e| e.inspect }.join(", ") + "]"

  def __to_s_slow = __inspect_slow

  # `join` renders each element with `to_s`, flattens nested arrays, and renders
  # nil as the empty string [V].
  def __join_slow(sep = nil)
    s = sep.nil? ? "" : sep.to_s
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
        parts.push(e.is_a?(String) ? e : e.to_s)
      end
    end
    nil
  end
end

class Range
  def __inspect_slow
    self.begin.inspect + (exclude_end? ? "..." : "..") + self.end.inspect
  end

  def __to_s_slow
    self.begin.to_s + (exclude_end? ? "..." : "..") + self.end.to_s
  end
end

class Hash
  def __inspect_slow
    return "{}" if empty?

    "{" + map { |k, v| __hash_key_repr(k) + " " + v.inspect }.join(", ") + "}"
  end

  def __to_s_slow = __inspect_slow

  # A Symbol key with an identifier-like name renders `k: v`; everything else
  # renders `k => v` [V].
  def __hash_key_repr(k)
    return k.inspect + " =>" unless k.is_a?(Symbol)

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
    return obj.send(meth) if obj.__user_defines?(meth) || obj.__user_defines?(:method_missing)

    nil
  end
end

class String
  def self.try_convert(obj)
    return obj if obj.is_a?(String)

    r = __check_convert(obj, :to_str)
    return nil if r.nil?
    return r if r.is_a?(String)

    raise TypeError, "can't convert " + obj.class.name + " to String (" +
                     obj.class.name + "#to_str gives " + r.class.name + ")"
  end
end

class Array
  def self.try_convert(obj)
    return obj if obj.is_a?(Array)

    r = __check_convert(obj, :to_ary)
    return nil if r.nil?
    return r if r.is_a?(Array)

    raise TypeError, "can't convert " + obj.class.name + " to Array (" +
                     obj.class.name + "#to_ary gives " + r.class.name + ")"
  end
end

class Regexp
  # `$~` is an ordinary global, so this needs nothing from the machine.
  def self.last_match(n = nil)
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
  # The loop is written on `match` + `pre_match`/`post_match` rather than on
  # offsets, and it advances past a **zero-width** match by one character —
  # without that, `"aaa".gsub(/a*/) { "X" }` would not terminate.
  def sub(pat, rep = nil, &blk)
    return __sub_rep(pat, rep) unless rep.nil?
    return __unsupported__("String#sub with neither a replacement nor a block") if blk.nil?
    re = pat.is_a?(Regexp) ? pat : Regexp.new(Regexp.escape(pat))
    m = re.match(self)
    return self if m.nil?
    m.pre_match + blk.call(m[0]).to_s + m.post_match
  end

  def gsub(pat, rep = nil, &blk)
    return __gsub_rep(pat, rep) unless rep.nil?
    return __unsupported__("String#gsub with neither a replacement nor a block") if blk.nil?
    re = pat.is_a?(Regexp) ? pat : Regexp.new(Regexp.escape(pat))
    out = ""
    rest = self
    guard = 0
    while guard <= length
      guard += 1
      m = re.match(rest)
      break if m.nil?
      out += m.pre_match + blk.call(m[0]).to_s
      adv = m.end(0)
      if adv == m.begin(0)
        out += rest[adv, 1].to_s
        adv += 1
      end
      break if adv > rest.length
      rest = rest[adv, rest.length - adv]
    end
    out + rest
  end

  # `partition`/`rpartition` split around the first / last occurrence of a
  # String separator and always return three parts [V]; a miss puts the whole
  # string in the *head* for `partition` and in the *tail* for `rpartition`.
  # `index`/`rindex` for a String needle (a Regexp needle would go through the
  # matcher and is not needed here).
  def index(needle, start = 0)
    n = needle.length
    i = start < 0 ? length + start : start
    i = 0 if i < 0
    while i + n <= length
      return i if self[i, n] == needle
      i += 1
    end
    nil
  end

  def rindex(needle, start = nil)
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

  # `b` returns a copy in ASCII-8BIT. The model has no encodings: a String is a
  # sequence of *characters*, so for ASCII input `b` is a copy and for anything
  # else it would silently mean the wrong thing. `Purl.encode` is exactly that
  # case — `"café".b.gsub(…) { |c| "%%%02X" % c.ord }` must yield `%C3%A9` (two
  # UTF-8 bytes) and a character-wise model yields `%E9`. So non-ASCII gates
  # rather than answering (L110).
  def b
    return __unsupported__("String#b on non-ASCII (byte strings are not modeled)") unless
      each_char.all? { |c| c.ord < 128 }
    dup
  end
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

  # The shared failure path. Message shapes are sorbet-runtime's, verified
  # against the gem (`difftest/corpus/sorbet/`).
  def self.__check!(prefix, type, value)
    return value if T.__valid?(type, value)
    raise TypeError, prefix + ": Expected type " + T.type_label(type) +
                     ", got type " + value.class.name +
                     " with value " + value.inspect
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
    raise TypeError, "Parameter '" + name.to_s + "': Can't set " + cls.name + "." +
                     name.to_s + " to " + value.inspect + " (instance of " +
                     value.class.name + ") - need a " + want
  end
end

class T::Enum
  def self.enums(*args)
    __unsupported__("T::Enum")
  end
end
