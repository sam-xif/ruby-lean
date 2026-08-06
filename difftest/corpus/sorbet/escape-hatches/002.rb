# typed: true
require "sorbet-runtime"

class C
  extend T::Sig

  sig { params(x: Integer).returns(String) }
  def f(x)
    x.to_s
  end

  define_method(:f) { |x| x.no_such_method }
end

puts C.new.f(1)
