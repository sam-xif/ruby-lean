# L275 / F56: &operand invokes conversion after receiver, arguments and keywords.
def converted(value)
  p [1, 2].map(&value)
rescue => e
  p [e.class, e.message]
end

converted(:to_s)
converted(->(x) { x + 1 })
class NilClass
  def to_proc; raise 'nil must bypass conversion'; end
end
def block_present; block_given?; end
p block_present(&nil)
b = ->(x) { x + 2 }
def b.to_proc; raise 'Proc must bypass conversion'; end
converted(b)

class Symbol
  alias_method :original_to_proc, :to_proc
  def respond_to?(name, include_private = false)
    raise 'defined to_proc must bypass respond_to?'
  end
  private
  def to_proc; ->(x) { x + 10 }; end
end
converted(:to_s)
class Symbol
  def to_proc; nil; end
end
converted(:to_s)
class Symbol
  def to_proc; 7; end
end
converted(:to_s)
class Symbol
  def to_proc; raise NoMethodError, 'converter raised'; end
end
converted(:to_s)
class Symbol
  remove_method :respond_to?
  undef_method :to_proc
end
converted(:to_s)
class Symbol
  def method_missing(name, *args)
    p [name, args, block_given?]
    ->(x) { x + 20 }
  end
end
converted(:to_s)
class Symbol
  def respond_to_missing?(name, priv)
    p [name, priv]
    false
  end
end
converted(:to_s)
class Symbol
  def respond_to_missing?(name, priv); true; end
  def method_missing(name, *args); raise NoMethodError, 'promised missing'; end
end
converted(:to_s)
class Symbol
  remove_method :respond_to_missing?
end
converted(:to_s) # same NoMethodError, now becomes a conversion TypeError
class Symbol
  def method_missing(name, *args); nil; end
end
converted(:to_s)
class Symbol
  def method_missing(name, *args); 7; end
end
converted(:to_s)
class Symbol
  alias_method :to_proc, :original_to_proc
  remove_method :method_missing
end
converted(:to_s)

class Converter
  private
  def to_proc
    p :convert
    ->(x) { x + 30 }
  end
end
converted(Converter.new)
converted(Object.new)
converted(false)
converted(7)

def marked(label, value)
  p label
  value
end
class Target
  def run(arg, k:)
    p [arg, k]
    yield(arg + k)
  end
end
p marked(:receiver, Target.new).run(marked(:arg, 2), k: marked(:keyword, 3),
  &marked(:operand, Converter.new))

class MissingConverter
  def respond_to?(name)
    p name
    true
  end
  def method_missing(name, *args); ->(x) { x + 40 }; end
end
converted(MissingConverter.new)
class MissingConverter
  def respond_to?(name, priv)
    p [name, priv]
    false
  end
end
converted(MissingConverter.new)
class MissingConverter
  def respond_to?(name, priv); true; end
  def method_missing(name, *args); raise NoMethodError, 'respond promised'; end
end
converted(MissingConverter.new)
class MissingConverter
  def respond_to?(name, priv)
    self.class.send(:define_method, :to_proc) { ->(x) { x + 50 } }
    true
  end
end
converted(MissingConverter.new)

class ConversionExit
  def to_proc
    begin
      raise 'conversion exception'
    ensure
      p :conversion_ensure
    end
  end
end
converted(ConversionExit.new)
