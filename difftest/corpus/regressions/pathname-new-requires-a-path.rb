# CRuby's `Pathname#initialize` is `@path = File.path(path).dup`: a String is a
# path already, anything else converts through `#to_path` and then `#to_str`
# (never `#to_s`), a result that is still not a String raises `TypeError`, and a
# path holding a null byte raises `ArgumentError`. The model used to call
# `to_s`, so it answered a `Pathname` where CRuby raises, and read the wrong
# attribute of an object that has both `#to_path` and `#to_s`.
#
# Every conversion is exercised here, plus the controls that must not move: a
# plain String, a String subclass, and an object that only has `#to_str`.
def show(label)
  puts("#{label} => #{yield.inspect}")
rescue StandardError => e
  puts("#{label} => #{e.class}: #{e.message}")
end

class ToPath
  def to_path = "/from-to-path"
  def to_s = "/from-to-s"
end

class ToStrOnly
  def to_str = "/from-to-str"
end

class BothBad
  def to_path = 5
  def to_str = "/from-to-str"
end

class NullToPath
  def to_path = "/bad\0path"
end

# `#to_path` that answers nil is still an answer: CRuby does not then try
# `#to_str`, it raises
class NilToPath
  def to_path = nil
  def to_str = "/from-to-str"
end

# `File.path` asks `rb_check_funcall`, so a `#to_path` that only
# `method_missing` serves is called too, and a custom `respond_to_missing?` is
# believed when it denies the name
class MethodMissingPath
  def method_missing(name, *args)
    name == :to_path ? "/from-method-missing" : super
  end
end

class DeclaredMethodMissingPath
  def method_missing(name, *args)
    name == :to_path ? "/from-respond-to-missing" : super
  end

  def respond_to_missing?(name, include_private = false)
    name == :to_path || super
  end
end

class DeniedMethodMissingPath
  def method_missing(name, *args)
    name == :to_path ? "/from-denied-to-path" : (name == :to_str ? "/from-denied-to-str" : super)
  end

  def respond_to_missing?(name, include_private = false)
    name == :to_str || super
  end
end

# a String subclass is a String, so it is used as it is
class StrSub < String; end

show("string")        { Pathname.new("/plain").to_s }
show("string subclass") { Pathname.new(StrSub.new("/sub")).to_s }
show("to_path wins")  { Pathname.new(ToPath.new).to_s }
show("to_str only")   { Pathname.new(ToStrOnly.new).to_s }
show("pathname")      { Pathname.new(Pathname.new("/nested")).to_s }
show("kernel func")   { Pathname.new("/plain") == Pathname("/plain") }

# a non-String with neither conversion raises rather than being coerced
show("integer")  { Pathname.new(123) }
show("nil")      { Pathname.new(nil) }
show("symbol")   { Pathname.new(:sym) }
show("true")     { Pathname.new(true) }
show("array")    { Pathname.new([1]) }
show("object")   { Pathname.new(Object.new) }
show("kernel func, integer") { Pathname(3) }

# a `#to_path` that answers a non-String does **not** fall back to `#to_str`
show("to_path not a string") { Pathname.new(BothBad.new) }
show("to_path answers nil") { Pathname.new(NilToPath.new) }

# the same rule for a conversion `method_missing` provides
show("method_missing to_path")  { Pathname.new(MethodMissingPath.new).to_s }
show("declared to_path")        { Pathname.new(DeclaredMethodMissingPath.new).to_s }
show("denied to_path, to_str")  { Pathname.new(DeniedMethodMissingPath.new).to_s }

# `File.path`'s null-byte check runs on the converted String
show("null byte")          { Pathname.new("/bad\0path") }
show("null byte, to_path") { Pathname.new(NullToPath.new) }

# the constructor copies the path, so mutating the argument changes nothing
s = +"/before"
pn = Pathname.new(s)
s << "/after"
show("argument mutated after") { pn.to_s }
