# ─── Dispatching repr: the prelude twins ────────────────────────────────────
#
# Pure repr (`Repr.lean`) renders a value without running any Ruby, which is fast
# and is what almost every program needs. It cannot speak for a value whose class
# — or whose *contents* — override `inspect`/`to_s`, because honouring that means
# **dispatching**, and a builtin cannot push a frame.
#
# So each such builtin defers to a twin here under a different name. The
# different name is what makes this cheap: it shadows nothing, so no purity answer
# changes, and `Repr` stays the fast path for everything it can still handle. The
# twins then recurse through *ordinary dispatch*, which is exactly the behaviour
# that was missing — `[custom].inspect` renders each element with its own
# `inspect`, and a plain object renders each ivar with its own.
#
# `__write` and `__addr_str` are the two primitives they need: append a String to
# stdout with no rendering, and the `0x…` a default `inspect` carries.
class Object
  # `rb_obj_as_string`: **the** way a C-level renderer turns a value into a
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

    s = self.to_s
    String === s ? s : __any_to_s
  end

  # `rb_inspect`: `inspect`, and then **`rb_obj_as_string` of the result** — which
  # is why `p Bar.new` prints `1` for a `Bar#inspect` that answers `1`, rather than
  # raising [V]. Note it is the *result* that is coerced here, not the receiver.
  def __as_inspect
    v = self.inspect
    String === v ? v : v.__as_string
  end

  # Native Object#inspect uses the checked hook and continuation in L289.
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

  # `puts` flattens arrays, prints a blank line for nil, skips empty arrays, and
  # does not double a newline the value already ends with [V].
  def __puts_slow(*args)
    return __write("\n") if args.empty?

    args.each { |a| __puts_one(a) }
    nil
  end

  # `rb_io_puts` asks each argument for `to_ary` before rendering it, so an
  # object that answers one is *flattened* and one that answers the wrong type
  # raises — neither of which a payload test can see. Since L133 `toAryDefer?`
  # routes such an argument here instead of gating `puts`.
  def __puts_one(a)
    return __write("\n") if a.nil?

    unless String === a
      arr = __check_array_type(a)
      unless arr.nil?
        return nil if arr.empty?

        arr.each { |e| __puts_one(e) }
        return nil
      end
    end

    str = a.__as_string
    __write(str)
    __write("\n") unless str.end_with?("\n")
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
    # no implicit conversion of Integer into String`. A non-String
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

  # `ary_join_one`: a nested Array is joined recursively — and "nested" is
  # `rb_check_array_type`, not `is_a?(Array)`, so an element answering `to_ary`
  # is joined too (`[Pair.new].join(",")` is `"7,8"`, not `"#<Pair:0x…>"`). Found
  # by probing L133's other sites; `to_ary` is tried **before** `to_s`, which is
  # why it cannot be left to `__as_string`.
  def __join_collect(parts)
    each do |e|
      if e.nil?
        parts.push("")
      else
        sub = String === e ? nil : __check_array_type(e)
        if sub.nil?
          parts.push(e.__as_string)
        else
          sub.__join_collect(parts)
        end
      end
    end
    nil
  end
end

class Range
  # A **nil endpoint prints as nothing** — `(1..nil).inspect` is `"1.."` — except
  # when both are nil, which prints `"nil..nil"` [V]. `to_s` needs no such case:
  # `nil.to_s` is `""` already, so `(nil..nil).to_s` really is `".."`. The Lean
  # twin in `Repr.lean` carries the same rule.
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
  #. Note it does not coerce: a `to_s` answering `1` makes `message`
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

# The native throw constructor passes tag, value, then the raw format String.
class UncaughtThrowError
  def initialize(*args)
    if args.length < 2
      raise ArgumentError, "wrong number of arguments (given #{args.length}, expected 2+)"
    end
    tag = args.shift
    value = args.shift
    super(*args)
    __throw_metadata(tag, value)
    self
  end
end

# Native specialized exception initializers delegate their message to super.
# Metadata arguments/keywords await their own payload model.
class NameError
  def initialize(*args, **kw)
    if args.length > 1 || !kw.empty?
      __unsupported__("NameError initializer metadata")
    end
    super(*args)
    self
  end
end

class NoMethodError
  def initialize(*args, **kw)
    if args.length > 1 || !kw.empty?
      __unsupported__("NoMethodError initializer metadata")
    end
    super(*args)
    self
  end
end

class KeyError
  def initialize(*args, **kw)
    if args.length > 1 || !kw.empty?
      __unsupported__("KeyError initializer metadata")
    end
    super(*args)
    self
  end
end

class FrozenError
  def initialize(*args, **kw)
    if args.length > 1 || !kw.empty?
      __unsupported__("FrozenError initializer metadata")
    end
    super(*args)
    self
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

