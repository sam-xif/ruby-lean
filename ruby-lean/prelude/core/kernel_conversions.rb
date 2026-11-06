# ─── Kernel conversions ─────────────────────────────────────────────────────

module Kernel
  # `Integer(x, base)` is `rb_convert_to_integer`, and it is **two rules wearing
  # one name**. The version here used to be only the second half's
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

  # `rb_Array`: nil → [], then `to_ary`, then `to_a`, else a one-element array
  # [V]. `vulns/vulnerability.rb` uses it three times to normalize optional OSV
  # list fields.
  #
  # Both conversions are `rb_check_funcall`, not `respond_to?`: the older
  # spelling missed a `method_missing`-supplied `to_ary` entirely and, worse,
  # *used* a non-Array answer — `Array(o)` for a `to_ary` returning `"nope"`
  # answered `"nope"` where CRuby raises. The `respond_to?` arm survives for the
  # **core** `to_a`s (Hash, Range, Struct, MatchData), which `__check_convert`
  # cannot see: it is `rb_check_funcall` over `__user_defines?`, and a builtin
  # definition is not a user one.
  def Array(arg)
    return [] if arg.nil?

    r = __check_array_type(arg)
    return r unless r.nil?

    if arg.__user_defines?(:to_a) || arg.__user_defines?(:method_missing)
      u = __check_convert(arg, :to_a)
      return u if u.is_a?(Array)

      unless u.nil?
        raise TypeError, "can't convert " + arg.class.to_s + " to Array (" +
                         arg.class.to_s + "#to_a gives " + u.class.to_s + ")"
      end
    elsif arg.respond_to?(:to_a)
      return arg.to_a
    end

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

