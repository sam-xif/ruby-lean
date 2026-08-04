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
  def <(other)
    c = (self <=> other)
    return __unsupported__("Comparable#< with a nil <=>") if c.nil?
    c < 0
  end

  def <=(other)
    c = (self <=> other)
    return __unsupported__("Comparable#<= with a nil <=>") if c.nil?
    c <= 0
  end

  def >(other)
    c = (self <=> other)
    return __unsupported__("Comparable#> with a nil <=>") if c.nil?
    c > 0
  end

  def >=(other)
    c = (self <=> other)
    return __unsupported__("Comparable#>= with a nil <=>") if c.nil?
    c >= 0
  end

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

class Integer
  include Comparable

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

class Float
  include Comparable
end

class String
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
