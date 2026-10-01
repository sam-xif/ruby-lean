# L272: rb_equal checks identity before dispatching == and returns a Boolean.
class IdentityProbe
  def ==(other); false; end
  def equal?(other); false; end
end
a = IdentityProbe.new
p [a === a, a === IdentityProbe.new]
class IdentityProbe
  undef_method :==
end
p a === a
begin
  a === IdentityProbe.new
rescue NoMethodError
  p :missing_equality
end
class TruthyEquality
  def ==(other); :truthy; end
end
p TruthyEquality.new === Object.new

class SuperEquality
  def ==(other); :truthy; end
  def ===(other); super; end
end
p SuperEquality.new === Object.new

class TrueClass
  def ==(other); !other; end
end
p [true === true, true === false]
class TrueClass
  undef_method :==
end
p true === true
class FalseClass
  undef_method :==
end
p false === false
class NilClass
  undef_method :==
end
p nil === nil

class Integer
  def ==(other); false; end
end
class Symbol
  undef_method :==
end
class String
  undef_method :==
end
p [1 === 1, 1 === 1.0, :a === :a, "a" === "a", Float::NAN === Float::NAN]
