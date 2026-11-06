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
# definition of this name" is a fact about the method tables.
class Object
  # The default `<=>`: `0` when the two are `==`, and **nil** otherwise — the nil
  # is what lets `Comparable` degrade to "incomparable" rather than raise from
  # the wrong place. CRuby calls `rb_equal`, so a **user `==` participates**;
  # here that is free, because `==` is an ordinary send. As a builtin it had to
  # gate on a class with a user `==`, which is the same lesson as
  # `try_convert`: a rule that needs to dispatch does not belong in Lean.
  def <=>(other)
    self == other ? 0 : nil
  end
end

module Kernel
  # `rb_check_funcall`'s callability rule, over an arbitrary method name: a
  # **user `respond_to?`** is asked first and a false answer is believed without
  # calling anything; otherwise the call happens if the method is defined or a
  # user `method_missing` can serve it.
  #
  # Split out of `__check_convert` by L133, because the two questions are not the
  # same one: `rb_check_funcall` returns `Qundef` for "not callable" and the
  # method's own answer otherwise, and `rb_convert_type_with_id` distinguishes
  # them — a `to_ary` that *answers nil* raises `can't convert C to Array
  # (C#to_ary gives NilClass)`, where an absent one raises `no implicit
  # conversion`. Collapsing both into `nil` cost the first of those messages.
  def __conv_callable?(obj, meth)
    if obj.__user_defines?(:respond_to?)
      return obj.respond_to?(meth)
    end
    return true if obj.__user_defines?(meth)

    if obj.__user_defines?(:method_missing)
      # A **custom `respond_to_missing?`** is consulted before `method_missing` is
      # entered (`check_funcall_missing` tests `rb_method_basic_definition_p` on it,
      # so the *default* one — which answers false — is deliberately not), and it is
      # asked with `include_private = true` [V]. Missing this clause is what made
      # `Integer(obj)` on an object whose `method_missing` serves `to_int` and whose
      # `respond_to_missing?` names only `to_int` raise from the **`to_str`** probe
      # that runs first.
      return !obj.__user_defines?(:respond_to_missing?) ||
             obj.respond_to_missing?(meth, true)
    end

    false
  end

  # `rb_check_funcall`, for the callers that treat "answered nil" and "nothing
  # answered" alike — which is every conversion but `rb_convert_type_with_id`.
  def __check_convert(obj, meth)
    __conv_callable?(obj, meth) ? obj.send(meth) : nil
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

  # `rb_str_cmp_m` for a non-String operand that could dispatch (the builtins
  # keep every other case; `strCmpDefer?`). `rb_check_string_type` first — so a
  # `to_str`, or a `method_missing` serving one, runs and its String is compared —
  # and only when nothing converts, `rb_invcmp`: the operand's own `<=>` as a
  # **plain** call (`rb_cmp`, not `rb_check_funcall` — no `respond_to?` is asked,
  # and a missing `<=>` raises `NoMethodError`), nil passed through, anything
  # else `rb_cmpint`-ed and negated [V].
  def __str_cmp_slow(other)
    s = String.try_convert(other)
    return self <=> s unless s.nil?

    r = other.__send__(:<=>, self)
    return nil if r.nil?

    if r > 0
      -1
    elsif r < 0
      1
    else
      0
    end
  end

  # `Comparable`'s operators over that `<=>`, with its nil turned into
  # `comparison of String with C failed`.
  def __str_rel_slow(other)
    c = __str_cmp_slow(other)
    __cmp_failed(other) if c.nil?

    c
  end

  def __str_lt_slow(other) = __str_rel_slow(other) < 0

  def __str_gt_slow(other) = __str_rel_slow(other) > 0

  def __str_le_slow(other) = __str_rel_slow(other) <= 0

  def __str_ge_slow(other) = __str_rel_slow(other) >= 0

  def __str_cmp_basic(_other) = __unsupported__("String comparison with a BasicObject operand")
end

# ─── The implicit Array conversion (`rb_check_array_type`) ────────────
#
# Every implicit Array-conversion site in CRuby — `Array#+`, `#concat`,
# `#flatten`, `Kernel#Array`, `puts`, a block's auto-splat, `a, b = obj` — is
# `rb_check_array_type`, which is `rb_check_funcall(:to_ary)`. It **dispatches**,
# so three things the model's payload test could not produce are observable:
#
#   * the `to_ary` body **runs**, including one a `method_missing` serves, and
#     whatever it printed, printed;
#   * an Array answer is *used* — `[1] + Pair.new` is `[1, 7, 8]`;
#   * a non-Array answer names the method: "can't convert C to Array
#     (C#to_ary gives String)" — `to`, not `into`, against the `into` of the
#     nothing-answered case [V].
module Kernel
  # `rb_check_array_type`: nil when nothing answered, so the caller decides what
  # "not an array" means. An Array is itself — a redefined `to_ary` on `Array`
  # is not consulted, as `rb_check_convert_type_with_id` short-circuits on the
  # builtin type [V].
  def __check_array_type(obj)
    return obj if obj.is_a?(Array)

    r = __check_convert(obj, :to_ary)
    return nil if r.nil?
    return r if r.is_a?(Array)

    raise TypeError, "can't convert " + obj.class.to_s + " to Array (" +
                     obj.class.to_s + "#to_ary gives " + r.class.to_s + ")"
  end

  # `rb_to_array_type` (`rb_convert_type_with_id`). **Not** `__check_array_type`
  # with a raise bolted on, and the difference is a message: the check form
  # answers nil for a `to_ary` that returned nil, but this one type-checks the
  # answer *whatever it is*, so `nil` is a mismatch naming `NilClass` and only an
  # **absent** `to_ary` gets `no implicit conversion` [V]. `__conv_desc` names
  # nil/true/false literally there, exactly as Lean's `coerceName` does.
  def __to_array_type(obj)
    return obj if obj.is_a?(Array)

    unless __conv_callable?(obj, :to_ary)
      raise TypeError, "no implicit conversion of " + __conv_desc(obj) + " into Array"
    end

    r = obj.to_ary
    return r if r.is_a?(Array)

    raise TypeError, "can't convert " + obj.class.to_s + " to Array (" +
                     obj.class.to_s + "#to_ary gives " + r.class.to_s + ")"
  end
end

class Array
  def self.try_convert(obj) = __check_array_type(obj)

  # The twins `toAryDefer?` sends `Array#+`/`#concat` to when their argument
  # might answer `to_ary`. Each converts and then re-enters the builtin with a
  # real Array, which cannot defer again.
  def __ary_plus_slow(other) = self + __to_array_type(other)

  def __ary_concat_slow(other) = concat(__to_array_type(other))

  # `rb_ary_flatten` converts **every element** with `rb_check_array_type`, not
  # just the ones that already are Arrays — so an element answering `to_ary` is
  # spliced. Entered only when some element could (`anyToAryDeep`), and only for
  # the depth-less form; `flatten(n)` gates in the builtin.
  def __ary_flatten_slow
    out = []
    each do |e|
      sub = __check_array_type(e)
      if sub.nil?
        out << e
      else
        out.concat(sub.__ary_flatten_slow)
      end
    end
    out
  end
end

# ─── The coerce protocol (`rb_num_coerce_bin` and friends) ──────────────────
#
# A numeric operator does not decide "not a number" from the class chain: it asks
# the **argument** to `coerce` itself and re-dispatches the operator on the pair
# that comes back. Three halves of that are observable, and a Lean rule can
# produce none of them:
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
    return true if obj.__coerce_defined?
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

  def __coerce_quo(other) = __coerce_bin(other, :quo)

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
  # `$~` lives in the **frame**, and CRuby's `last_match` is a C function
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

