# ─── Integer ────────────────────────────────────────────────────────────────

class Numeric
  # CRuby mixes Comparable into Numeric, not into Integer/Float — which is also
  # where it lands in `Integer.ancestors` [V].
  include Comparable
end

# Enumerator's suspension machinery is native; these collection methods use
# ordinary Ruby dispatch.
class Enumerator
  include Enumerable
end

class Enumerator::Generator
  include Enumerable
end

class Enumerator
  class Chain < Enumerator
    undef_method :next, :next_values, :peek, :peek_values, :feed

    def initialize(*enums)
      __chain_init(enums)
    end

    def each(*args)
      return __unsupported__("Enumerator::Chain blockless each wrapping") unless block_given?
      __chain_enums.each do |e|
        e.each(*args) { |*values| yield(*values) }
      end
      self
    end

    def size
      total = 0
      __chain_enums.each do |e|
        return nil unless e.respond_to?(:size)
        n = e.size
        return nil if n.nil?
        return n if n.is_a?(Float) && n.infinite?
        return nil unless n.is_a?(Integer)
        total += n
      end
      total
    end

    def inspect
      return "#<#{self.class}: uninitialized>" unless __chain_enums(:initialized?)
      "#<#{self.class}: #{__chain_enums.inspect}>"
    end

    def rewind
      __chain_enums
      __unsupported__("Enumerator::Chain rewind requires visited-iterator state")
    end
  end
end

# Immediate classes undefine new but retain allocate (which raises TypeError).
# Real tombstones preserve singleton inheritance and reflection.
class << Integer
  undef_method :new
end
class << Float
  undef_method :new
end
class << Symbol
  undef_method :new
end
class << NilClass
  undef_method :new
end
class << TrueClass
  undef_method :new
end
class << FalseClass
  undef_method :new
end

# Native frozen fractions have no public allocator. The tombstones also apply
# to subclasses; a program may still explicitly define its own singleton new.
class << Rational
  undef_method :new
  undef_method :allocate
end

class << Complex
  undef_method :new
  undef_method :allocate
  def rect(real, imag = 0)
    __complex_rect(real, imag)
  end
  alias rectangular rect
end

module Kernel
  def self.Rational(*args)
    super(*args)
  end
  def self.Complex(*args)
    super(*args)
  end
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
  # heads turned up first.
  #
  # Only Symbol compares to Symbol; `:k <=> 1` and `:k <=> "k"` are both nil [V],
  # and Comparable turns that nil into the ArgumentError for the operators.
  def <=>(other)
    return nil unless other.is_a?(Symbol)
    to_s <=> other.to_s
  end
end

