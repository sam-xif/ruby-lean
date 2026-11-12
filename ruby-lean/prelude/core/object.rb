# frozen_string_literal: true

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
  def loop
    return __enum_for(:loop, :infinite) unless block_given?
    begin
      while true
        yield
      end
    rescue StopIteration => e
      e.result
    end
  end
  private :loop

  # Object#=== first tests identity in the native primitive (rb_equal).
  # Only unequal identities dispatch ==, whose result is converted to a Boolean.
  def __case_equal(other)
    if self == other
      true
    else
      false
    end
  end

  def tap
    return __unsupported__("Enumerator: Object#tap without a block") unless block_given?
    yield(self)
    self
  end

  # `rb_cmpint`: `self <=> other`, with a nil — "not comparable" — turned into the
  # `ArgumentError: comparison of X with Y failed` that every comparison operator
  # except `==` raises [V]. The message comes from the `__cmp_failed` primitive so
  # that one rule names an operand (`coerceDesc`): the hand-written copy
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

