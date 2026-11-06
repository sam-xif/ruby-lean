# ─── Enumerable ─────────────────────────────────────────────────────────────
#
# Everything here is written against `each` alone, so one `each` per collection
# (Array/Hash natively, `Range#each` below, any user class) buys the whole module.
# Early exit uses `return` from inside the block (unwinds to this method's frame)
# or `break` (returns from `each`) — both already modeled (Semantics 04 §4).

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
  # the builtin; the block form falls through to here).
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

