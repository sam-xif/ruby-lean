def show(label)
  p [label, yield]
rescue StandardError => e
  p [label, e.class, e.message]
end
class Text
  def to_str
    puts :converted
    "text"
  end
end
show(:defined) { "a" + Text.new }
class PrivateText
  private
  def to_str = "private"
end
show(:private) { "a" + PrivateText.new }
class MissingText
  def method_missing(n, *args)
    puts n
    n == :to_str ? "missing" : super
  end
end
show(:missing) { "a" + MissingText.new }
class RejectText < Text
  def respond_to?(name)
    puts name
    false
  end
end
show(:rejected) { "a" + RejectText.new }
class BadText
  def to_str = nil
end
show(:nil_result) { "a" + BadText.new }
class BadMissing
  def method_missing(name, *args) = nil
end
show(:nil_missing) { "a" + BadMissing.new }
class FailingText
  def method_missing(name, *args) = super
end
show(:absent) { "a" + FailingText.new }
class PromisedText < FailingText
  def respond_to_missing?(name, priv = false) = true
end
show(:promised_failure) { "a" + PromisedText.new }
class MutationText
  def initialize(s) = @s = s
  def to_str
    @s << "b"
    def @s.+(other) = "redefined"
    "c"
  end
end
show(:mutation) { s = "a"; s + MutationText.new(s) }
class AliasedString < String
  alias add +
  def +(other) = super
end
show(:alias) { AliasedString.new("a").add(Text.new) }
show(:super) { AliasedString.new("a") + Text.new }
show(:throw) do
  o = Object.new
  def o.to_str = throw(:converted, :escaped)
  catch(:converted) { "a" + o }
end
show(:nil_operand) { "a" + nil }
show(:false_operand) { "a" + false }
show(:arity) { "a".send(:+, Text.new, Text.new) }
show(:keywords) { "a".send(:+, text: Text.new) }
# The native String type bypasses even overridden conversion/reflection hooks.
s = "b"
def s.to_str = raise("must not convert")
def s.respond_to?(*args) = raise("must not ask")
show(:string_bypass) { "a" + s }
