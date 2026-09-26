# Checked conversion: response hooks, redefinition and the NoMethodError boundary.
def attempt(value)
  p [3].map(&value)
rescue => e
  p [e.class, e.message]
end
class MissingBlock
  def respond_to?(a, b, c); raise 'must not run'; end
end
attempt(MissingBlock.new)
class MissingBlock
  def respond_to?(*args)
    p args
    true
  end
  def respond_to_missing?(name, priv)
    p [name, priv]
    false
  end
  def method_missing(name, *args); raise 'false hook must prevent this'; end
end
attempt(MissingBlock.new)
class MissingBlock
  remove_method :respond_to?
  def respond_to_missing?(name, priv)
    raise ArgumentError, 'response raised'
  end
end
attempt(MissingBlock.new)
class MissingBlock
  remove_method :respond_to_missing?
  def method_missing(name, *args)
    self.class.send(:define_method, :to_proc) { ->(x) { x + 60 } }
    raise NoMethodError, 'installed while failing'
  end
end
attempt(MissingBlock.new) # no response promise: the failure still becomes TypeError
attempt(MissingBlock.new)
class MissingBlock
  remove_method :to_proc
  def method_missing(name, *args)
    begin
      raise NoMethodError, 'not promised'
    ensure
      p :missing_ensure
    end
  end
end
attempt(MissingBlock.new)
class MissingBlock
  def method_missing(name, *args); raise ArgumentError, 'never swallowed'; end
end
attempt(MissingBlock.new)

class MissingPromise
  def respond_to_missing?(name, priv); true; end
  def method_missing(name, *args)
    self.class.send(:define_method, :to_proc) { ->(x) { x } }
    raise NoMethodError, 'hook promised before installation'
  end
end
attempt(MissingPromise.new)
class MissingParent
  def respond_to_missing?(name, priv); true; end
  def method_missing(name, *args)
    self.class.send(:define_method, :to_proc) { ->(x) { x } }
    raise NoMethodError, 'installation below missing-method owner'
  end
end
class MissingChild < MissingParent; end
attempt(MissingChild.new)

class BlockParent
  protected
  def to_proc; ->(x) { x + 70 }; end
end
class BlockChild < BlockParent
  def to_proc
    p :child
    super
  end
end
attempt(BlockChild.new)
module BlockPrefix
  def to_proc
    p :prefix
    super
  end
end
class BlockChild
  prepend BlockPrefix
end
attempt(BlockChild.new)

class ThrowBlock
  def to_proc
    throw :converted, 81
  end
end
p catch(:converted) { [1].map(&ThrowBlock.new) }
