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
        # `Module#name` answers nil and `+` would raise. Every message in
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



