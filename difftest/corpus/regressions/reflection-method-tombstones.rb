# L279: CRuby's shadow method list must not resurrect an undefined/private method.
class HiddenString < String
  undef_method :size
  def to_s
    super
  end
  private :to_s
end
s = HiddenString.new
p [s.respond_to?(:size), s.respond_to?(:size, true), s.respond_to?(:to_s), s.respond_to?(:to_s, true)]
p [HiddenString.method_defined?(:size), HiddenString.public_method_defined?(:size)]
p [HiddenString.method_defined?(:to_s), HiddenString.public_method_defined?(:to_s), HiddenString.private_method_defined?(:to_s)]
p [Rational.respond_to?(:new), Rational.respond_to?(:allocate), Complex.respond_to?(:new), Complex.respond_to?(:allocate)]
class ChildComplex < Complex; end
p [ChildComplex.respond_to?(:new), ChildComplex.respond_to?(:allocate)]
