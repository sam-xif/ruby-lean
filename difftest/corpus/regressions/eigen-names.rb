# L124, group 2/3. An eigenclass is named after the object it is attached to, by
# `rb_any_to_s` — so a plain object's singleton class is `#<Class:#<Foo:0x…>>`,
# not `#<Class:Object>`, which is what the model answered for *every* object,
# named class or not. This was not an anonymous-class defect and no probe of
# anonymous classes would have found it; it turned up because fixing `className`
# made the eigenclass name observable.
#
# The second half is the mirror image: nine message sites read `classOf`, which
# answers the *eigenclass* when one exists, where CRuby uses `rb_obj_class`. Once
# eigenclasses were named correctly those five wrong answers said
# `#<Class:#<Foo:0x…>> can't be coerced` instead of `Foo can't be coerced`.
def norm(s)
  s.gsub(/0x[0-9a-f]+/, "0xADDR")
end

def show(label)
  puts("#{label} => #{norm(yield.to_s)}")
rescue StandardError => e
  puts("#{label} => #{norm(e.class.to_s)}: #{norm(e.message)}")
end

class Foo
  def hi = 1
end

module Mixin
  def mixed = 2
end

# the eigenclass's own name, for each kind of attached object. A user
# `inspect`/`to_s` and any ivars are *ignored*: this is `rb_any_to_s`, not
# `inspect` [V].
class Custom
  def inspect = "IGNORED"
  def to_s = "IGNORED"
end

show("object") { Foo.new.singleton_class.to_s }
show("object, custom inspect") { Custom.new.singleton_class.to_s }
show("object with ivars") do
  o = Foo.new
  o.instance_variable_set(:@a, 1)
  o.singleton_class.to_s
end
show("two objects differ") do
  a = Foo.new
  b = Foo.new
  (a.singleton_class.to_s != b.singleton_class.to_s).to_s
end
show("anonymous class's instance") { Class.new.new.singleton_class.to_s }
show("class") { Foo.singleton_class.to_s }
show("anonymous class") { Class.new.singleton_class.to_s }
show("module") { Mixin.singleton_class.to_s }
show("metaclass of a metaclass") { Foo.singleton_class.singleton_class.to_s }
show("array") { [1, 2].singleton_class.to_s }
show("string") { "ab".singleton_class.to_s }
show("exception") { StandardError.new("m").singleton_class.to_s }
show("nil") { nil.singleton_class.to_s }
show("eigenclass inspect") { Foo.new.singleton_class.inspect }
show("class of an eigenclass") { Foo.new.singleton_class.class.to_s }
show("nomethod on an eigenclass") { Foo.new.singleton_class.frobnicate }

# `NoMethodError` is the one message that *does* render through the eigenclass:
# when a singleton class exists the receiver is shown by `rb_any_to_s` instead of
# `an instance of C`. Materializing it any way at all is enough [V].
show("nomethod, plain") { Foo.new.frobnicate }
show("nomethod, singleton def") do
  o = Foo.new
  def o.own = 3
  o.frobnicate
end
show("nomethod, extended") { Foo.new.extend(Mixin).frobnicate }
show("nomethod, eigenclass merely asked for") do
  o = Foo.new
  o.singleton_class
  o.frobnicate
end
show("nomethod, class receiver keeps 'for class'") do
  def Foo.own = 4
  Foo.frobnicate
end

# ...and these do not: `rb_obj_class` skips the eigenclass, so a singleton method
# on the operand changes none of them
show("coerce") do
  o = Foo.new
  def o.own = 5
  0 + o
end
show("relop") do
  o = Foo.new
  def o.own = 5
  1 < o
end
show("no implicit conversion") do
  o = Foo.new
  def o.own = 5
  "abc" + o
end
show("superclass") do
  o = Foo.new
  def o.own = 5
  Class.new(o)
end
show("frozen") do
  o = Foo.new
  def o.own = 5
  o.freeze
  o.instance_variable_set(:@a, 1)
end
show("raised class") do
  e = StandardError.new("m")
  def e.own = 5
  raise e
end
