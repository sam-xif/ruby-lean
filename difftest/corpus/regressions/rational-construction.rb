# L278: native allocators are undefined, fractions immutable and conversions exact.
r = Rational(1, -2)
p [r, r.frozen?, r.is_a?(Numeric), Rational.ancestors[0, 3]]
p [Rational(r).equal?(r), Rational(r, 1).equal?(r), 2.to_r, 1.2.to_r, Rational(1.2, 2.5)]
begin
  Rational.new
rescue NoMethodError => e
  puts e.message
end
begin
  Rational.allocate
rescue NoMethodError => e
  puts e.message
end
begin
  r.instance_variable_set(:@x, 1)
rescue FrozenError => e
  puts e.message
end
begin
  def r.changed
    :wrong
  end
rescue FrozenError => e
  puts e.message
end
class SubFraction < Rational
  def initialize
    puts "must not run"
  end
end
begin
  SubFraction.new
rescue NoMethodError => e
  puts e.message
end
p r.singleton_class.frozen?
begin
  class << r
    def changed
      :wrong
    end
  end
rescue FrozenError => e
  puts e.message
end
begin
  r.define_singleton_method(:changed) { :wrong }
rescue FrozenError => e
  puts e.message
end
