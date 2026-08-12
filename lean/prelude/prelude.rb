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
    hidden = "__t_unchecked_" + name.to_s
    cache = []
    mod.send(:alias_method, hidden, name)
    mod.send(:define_method, name) do |*args, &b|
      if cache.empty?
        d = T::Decl.new
        d.instance_eval(&blk)
        cache.push(d)
      end
      decl = cache[0]
      if decl.checked_level == :never
        send(hidden, *args, &b)
      else
        T.__check_params(decl, args)
        result = send(hidden, *args, &b)
        T.__check_return(decl, result)
      end
    end
    nil
  end

  # Positional matching: Sorbet requires a sig to list the method's parameters
  # in order, so the i-th declared name governs the i-th argument. A sig over a
  # method with *keyword* parameters cannot be matched this way (the shim has no
  # `instance_method(…).parameters` to consult), so it declares rather than
  # guesses.
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
    def abstract!
      @__t_abstract = true
      nil
    end

    def interface!
      @__t_abstract = true
      nil
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
class T::Struct
  def self.prop(*args)
    __unsupported__("T::Struct")
  end

  def self.const(*args)
    __unsupported__("T::Struct")
  end
end

class T::Enum
  def self.enums(*args)
    __unsupported__("T::Enum")
  end
end
