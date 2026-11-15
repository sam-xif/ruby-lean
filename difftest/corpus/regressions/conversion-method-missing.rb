# #152: `rb_check_funcall` reads a `NoMethodError` from a user `method_missing`
# that ends in `super` as the **default miss** ("not callable"), but the prelude's
# `__conv_callable?` answered "callable" for every name as soon as the class had
# a user `method_missing`, so the raise escaped from every implicit conversion.
#
# The reading is also per-arm, which is why this file keeps a class with a user
# `respond_to_missing?`: once that claim is true (or a user `respond_to?` says
# yes), CRuby's `check_funcall_failed` re-raises instead of answering nil.
def show(label)
  puts("#{label} => #{yield.inspect.gsub(/0x[0-9a-f]+/, '0xADDR')}")
rescue StandardError => e
  puts("#{label} => #{e.class}: #{e.message.gsub(/0x[0-9a-f]+/, '0xADDR')}")
end

class OnlyFoo
  def method_missing(name, *args)
    return "/foo" if name == :foo

    super
  end
end

o = OnlyFoo.new
show("String.try_convert") { String.try_convert(o) }
show("Array.try_convert") { Array.try_convert(o) }
show("Integer") { Integer(o) }
show("Integer exception: false") { Integer(o, exception: false) }
show("Float") { Float(o) }
show("Float exception: false") { Float(o, exception: false) }
show("Array") { Array(o) }
show("String") { String(o) }
show("respond_to? to_str") { o.respond_to?(:to_str) }

# The Array conversions that call `__to_array_type`, which must turn the same
# miss into CRuby's `no implicit conversion` rather than letting it escape.
show("ary +") { [1] + o }
show("ary.concat") { [1].concat(o) }
show("ary.flatten") { [o].flatten }

# A `NoMethodError` raised by the handler itself is the same miss (it never
# reached a real method), so it answers nil as well.
class HandlerRaises
  def method_missing(name, *args)
    raise NoMethodError, "handler gave up on #{name}"
  end
end

h = HandlerRaises.new
show("raises String.try_convert") { String.try_convert(h) }
show("raises Integer") { Integer(h) }
show("raises Array") { Array(h) }

# A miss that *is* a real method's answer still escapes: only the implicit
# `method_missing` arm treats `NoMethodError` as "not callable".
class RealToStrRaises
  def to_str
    raise NoMethodError, "from to_str"
  end
end

show("real to_str String.try_convert") { String.try_convert(RealToStrRaises.new) }
show("real to_str Integer") { Integer(RealToStrRaises.new) }

# A user `respond_to_missing?` that claims the name keeps CRuby's re-raise.
class ClaimedMiss
  def respond_to_missing?(name, include_private = false)
    name == :to_str || super
  end

  def method_missing(name, *args)
    super
  end
end

show("claimed String.try_convert") { String.try_convert(ClaimedMiss.new) }

# An answered nil is still distinct from a miss: the conversion names the class
# it got, where a miss reaches `no implicit conversion`.
class ToINil
  def to_i = nil
end

class ToAryNil
  def to_ary = nil
end

show("to_i nil Integer") { Integer(ToINil.new) }
show("to_ary nil ary +") { [1] + ToAryNil.new }
show("to_ary nil flatten") { [ToAryNil.new].flatten }
